/*
 * Copyright 2016 Clozure Associates
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "lisp.h"
#include "lisp-exceptions.h"
#include "lisp_globals.h"
#include <ctype.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <stdarg.h>
#include <errno.h>
#include <stdio.h>
#ifdef LINUX
#include <strings.h>
#include <sys/mman.h>
#endif

#ifdef DARWIN
#include <sys/mman.h>
#ifndef SA_NODEFER
#define SA_NODEFER 0
#endif
#include <sysexits.h>
#if defined(ARM64)
#include <libkern/OSCacheControl.h>
#endif

/* a distinguished UUO at a distinguished address */
extern void pseudo_sigreturn(ExceptionInformation *);
#endif


#include "threads.h"

/* Debug: called from assembly when catch_top is about to change */
void
debug_catch_top_change(natural old_val, natural new_val, natural lr)
{
  static int dbg_catch_count = 0;
  if (dbg_catch_count < 40) {
    dbg_catch_count++;
    fprintf(dbgout, "CATCH[%d]: 0x%lx -> 0x%lx lr=0x%lx\n",
            dbg_catch_count, (unsigned long)old_val,
            (unsigned long)new_val, (unsigned long)lr);
    fflush(dbgout);
  }
}

void
enable_fp_exceptions()
{
}

void
disable_fp_exceptions()
{
}

/*
  Handle exceptions.
*/

extern LispObj lisp_nil;

extern natural lisp_heap_gc_threshold;
extern Boolean grow_dynamic_area(natural);

Boolean allocation_enabled = true;

Boolean
did_gc_notification_since_last_full_gc = false;

int
page_size = 16384;

int
log2_page_size = 14;

TCR *gc_tcr = NULL;


static inline void
add_bytes_consed(TCR *tcr, natural bytes)
{
  tcr->bytes_allocated += bytes;
}


/*
  adjust_exception_pc: advance PC by delta/4 instructions.
  On ARM64, all instructions are 4 bytes wide, and delta is
  always passed as a byte count (typically 4).
*/
void
adjust_exception_pc(ExceptionInformation *xp, int delta)
{
  xpPC(xp) += (delta >> 2);
}


/*
  If the PC is pointing to an allocation trap, the previous instruction
  must have decremented allocptr.  Return the non-zero amount by which
  allocptr was decremented.

  ARM64 allocation sequence (3 instructions before the HLT):
    [-3]: sub allocptr, allocptr, #imm12  (or sub allocptr, allocptr, Xm)
    [-2]: cmp allocptr, allocbase
    [-1]: b.hi ok
    [ 0]: hlt #0  (alloc trap)
*/
signed_natural
allocptr_displacement(ExceptionInformation *xp)
{
  pc program_counter = xpPC(xp);
  opcode instr = *program_counter;
  opcode prev_instr;

  if (IS_ALLOC_TRAP(instr)) {
    /* The alloc trap was preceded by cmp and b.hi.
       The sub from allocptr is at [-3]. */
    prev_instr = program_counter[-3];

    if (IS_SUB_IMM_FROM_ALLOCPTR(prev_instr)) {
      /* SUB Xd, Xn, #imm12 — extract imm12 from bits 21:10 */
      natural imm12 = (prev_instr >> 10) & 0xFFF;
      return -((signed_natural)imm12);
    }

    if (IS_SUB_REG_FROM_ALLOCPTR(prev_instr)) {
      /* SUB Xd, Xn, Xm — read Xm register value */
      unsigned rm = (prev_instr >> 16) & 0x1F;
      return -((signed_natural)xpGPR(xp, rm));
    }

    Bug(xp, "Can't determine allocation displacement");
  }
  return 0;
}


/*
  ================================================================
  Chunk 2: Allocation handling.

  update_bytes_allocated — track bytes consumed by allocation.
  lisp_allocation_failure — signal allocation failure.
  callback_for_gc_notification — notify Lisp of GC.
  finish_allocating_cons — emulate post-trap cons instructions.
  finish_allocating_uvector — emulate post-trap uvector instructions.
  allocate_object — satisfy an allocation request, possibly via GC.
  handle_alloc_trap — top-level alloc trap handler.
  ================================================================
*/

#ifndef XNOMEM
#define XNOMEM 10
#endif


void
update_bytes_allocated(TCR *tcr, void *cur_allocptr)
{
  BytePtr
    last = (BytePtr) tcr->last_allocptr,
    current = (BytePtr) cur_allocptr;
  if (last && (cur_allocptr != ((void *)VOID_ALLOCPTR))) {
    add_bytes_consed(tcr, last - current);
  }
  tcr->last_allocptr = 0;
}


void
lisp_allocation_failure(ExceptionInformation *xp, TCR *tcr, natural bytes_needed)
{
  xpGPR(xp, allocptr) = xpGPR(xp, allocbase) = VOID_ALLOCPTR;
  handle_error(xp, bytes_needed < (128 << 10) ? XNOMEM : error_alloc_failed,
               0, NULL);
}


void
callback_for_gc_notification(ExceptionInformation *xp, TCR *tcr)
{
  LispObj cmain = nrs_CMAIN.vcell;

  did_gc_notification_since_last_full_gc = true;
  if (is_uvector_fulltag(fulltag_of(cmain)) &&
      (header_subtag(header_of(cmain)) == subtag_macptr)) {
    callback_to_lisp(cmain, xp, SIGTRAP, 0, NULL);
  }
}


/*
  finish_allocating_cons: emulate post-allocation instructions for
  a cons cell.  Called from pc_luser_xp when a GC interrupts between
  the alloc trap and the BIC that clears allocptr's low bits.

  Post-alloc sequence for cons:
    stur cdr_reg, [allocptr, #cons.cdr]       ; offset -8
    str  car_reg, [allocptr, #cons.car]        ; offset 0
    orr  result, allocptr, tag_reg, LSL #56
    bic  allocptr, allocptr, #dnode_mask
*/
void
finish_allocating_cons(ExceptionInformation *xp)
{
  pc program_counter = xpPC(xp);
  opcode instr;
  LispObj cur_allocptr = xpGPR(xp, allocptr);

  while (1) {
    instr = *program_counter++;

    if (IS_CLR_ALLOCPTR_TAG(instr)) {
      xpGPR(xp, allocptr) = cur_allocptr & ~((LispObj)(dnode_size - 1));
      xpPC(xp) = program_counter;
      return;
    }

    if (IS_STUR_TO_ALLOCPTR(instr)) {
      int offset = STUR_OFFSET(instr);
      unsigned dest_reg = STR_RT(instr);
      *(LispObj *)((char *)cur_allocptr + offset) = xpGPR(xp, dest_reg);
    } else if (IS_STR_UOFF_TO_ALLOCPTR(instr)) {
      natural offset = STR_UOFF(instr);
      unsigned dest_reg = STR_RT(instr);
      *(LispObj *)((char *)cur_allocptr + offset) = xpGPR(xp, dest_reg);
    } else if (IS_SET_ALLOCPTR_RESULT(instr)) {
      unsigned rd = ORR_RD(instr);
      unsigned rm = ORR_RM(instr);
      xpGPR(xp, rd) = cur_allocptr | (xpGPR(xp, rm) << tag_shift);
    } else {
      Bug(xp, "Unexpected instruction at " LISP
          " while finishing cons allocation",
          (LispObj)(program_counter - 1));
    }
  }
}


/*
  finish_allocating_uvector: emulate post-allocation instructions for
  a uvector (misc object).  Called from pc_luser_xp when a GC interrupts
  between the alloc trap and the BIC.

  Post-alloc sequence for uvector:
    stur header_reg, [allocptr, #misc_header_offset]   ; offset -8
    orr  result, allocptr, tag_reg, LSL #56
    bic  allocptr, allocptr, #dnode_mask
*/
void
finish_allocating_uvector(ExceptionInformation *xp)
{
  pc program_counter = xpPC(xp);
  opcode instr;
  LispObj cur_allocptr = xpGPR(xp, allocptr);

  while (1) {
    instr = *program_counter++;

    if (IS_CLR_ALLOCPTR_TAG(instr)) {
      xpGPR(xp, allocptr) = cur_allocptr & ~((LispObj)(dnode_size - 1));
      xpPC(xp) = program_counter;
      return;
    }

    if (IS_STUR_TO_ALLOCPTR(instr)) {
      int offset = STUR_OFFSET(instr);
      unsigned dest_reg = STR_RT(instr);
      *(LispObj *)((char *)cur_allocptr + offset) = xpGPR(xp, dest_reg);
    } else if (IS_SET_ALLOCPTR_RESULT(instr)) {
      unsigned rd = ORR_RD(instr);
      unsigned rm = ORR_RM(instr);
      xpGPR(xp, rd) = cur_allocptr | (xpGPR(xp, rm) << tag_shift);
    } else {
      Bug(xp, "Unexpected instruction at " LISP
          " while finishing uvector allocation",
          (LispObj)(program_counter - 1));
    }
  }
}


/*
  allocate_object: try to allocate bytes_needed bytes from the
  dynamic area.  May trigger EGC or full GC.  On success, adjusts
  allocptr by disp_from_allocptr and returns true.
*/
Boolean
allocate_object(ExceptionInformation *xp,
                natural bytes_needed,
                signed_natural disp_from_allocptr,
                TCR *tcr,
                Boolean *crossed_threshold)
{
  area *a = active_dynamic_area;

  /* Maybe do an EGC */
  if (a->older && lisp_global(OLDEST_EPHEMERAL)) {
    if (((a->active) - (a->low)) >= a->threshold) {
      gc_from_xp(xp, 0L);
    }
  }

  /* Try to grab a segment without extending the heap. */
  if (new_heap_segment(xp, bytes_needed, false, tcr, crossed_threshold)) {
    xpGPR(xp, allocptr) += disp_from_allocptr;
    return true;
  }

  /* Don't bother with a full GC if the object is larger than
     everything allocated so far. */
  if ((lisp_global(HEAP_END) - lisp_global(HEAP_START)) > bytes_needed) {
    untenure_from_area(tenured_area);
    gc_from_xp(xp, 0L);
    did_gc_notification_since_last_full_gc = false;
  }

  /* Try again, growing the heap if necessary. */
  if (new_heap_segment(xp, bytes_needed, true, tcr, NULL)) {
    xpGPR(xp, allocptr) += disp_from_allocptr;
    return true;
  }

  return false;
}


/*
  handle_alloc_trap: handle an allocation trap (HLT instruction in
  the alloc sequence).

  On ARM64 TBI, allocptr doesn't carry a fulltag in its low bits
  (tags go in the high byte via ORR), so we compute bytes_needed
  uniformly from the displacement:
    disp = -(size - node_size)
    bytes_needed = (-disp) + node_size = size

  No fulltag-based cons/uvector dispatch is needed here.
*/
Boolean
handle_alloc_trap(ExceptionInformation *xp, TCR *tcr, Boolean *notify)
{
  signed_natural disp;
  natural cur_allocptr, bytes_needed;

  if (!allocation_enabled) {
    /* Back up before the alloc_trap, then let pc_luser_xp() back
       up some more through the allocation sequence. */
    xpPC(xp) -= 1;
    pc_luser_xp(xp, tcr, NULL);
    allocation_enabled = true;
    tcr->save_allocbase = (void *)VOID_ALLOCPTR;
    handle_error(xp, error_allocation_disabled, 0, NULL);
    return true;
  }

  cur_allocptr = xpGPR(xp, allocptr);
  disp = allocptr_displacement(xp);

  if (disp == 0) {
    return false;
  }

  bytes_needed = (-disp) + node_size;

  update_bytes_allocated(tcr, (void *)(cur_allocptr - disp));

  if (allocate_object(xp, bytes_needed, disp, tcr, notify)) {
    adjust_exception_pc(xp, 4);
    if (notify && *notify) {
      pc_luser_xp(xp, tcr, NULL);
      callback_for_gc_notification(xp, tcr);
    }
    return true;
  }

  lisp_allocation_failure(xp, tcr, bytes_needed);
  return true;
}


natural gc_deferred = 0, full_gc_deferred = 0;

signed_natural
flash_freeze(TCR *tcr, signed_natural param)
{
  return 0;
}


/*
  ================================================================
  Chunk 3: GC trap handling, stack overflow, protection violations,
           error dispatch.
  ================================================================
*/

/* Forward declarations for functions defined in later chunks. */
void normalize_tcr(ExceptionInformation *, TCR *, Boolean);
signed_natural gc_like_from_xp(ExceptionInformation *,
                               signed_natural (*)(TCR *, signed_natural),
                               signed_natural);
Boolean allocate_list(ExceptionInformation *, TCR *);


/*
  handle_gc_trap: handle a GC trap (hlt with gc_trap info code).
  The selector in imm0 determines the operation; imm1 is an
  optional argument.
*/
Boolean
handle_gc_trap(ExceptionInformation *xp, TCR *tcr)
{
  LispObj
    selector = xpGPR(xp, imm0),
    arg = xpGPR(xp, imm1);
  area *a = active_dynamic_area;
  Boolean egc_was_enabled = (a->older != NULL);
  natural gc_previously_deferred = gc_deferred;

  switch (selector) {
  case GC_TRAP_FUNCTION_EGC_CONTROL:
    egc_control(arg != 0, a->active);
    xpGPR(xp, arg_z) = lisp_nil + (egc_was_enabled ? t_offset : 0);
    break;

  case GC_TRAP_FUNCTION_CONFIGURE_EGC:
    a->threshold = unbox_fixnum(xpGPR(xp, arg_x));
    g1_area->threshold = unbox_fixnum(xpGPR(xp, arg_y));
    g2_area->threshold = unbox_fixnum(xpGPR(xp, arg_z));
    xpGPR(xp, arg_z) = lisp_nil + t_offset;
    break;

  case GC_TRAP_FUNCTION_SET_LISP_HEAP_THRESHOLD:
    if (((signed_natural) arg) > 0) {
      lisp_heap_gc_threshold =
        align_to_power_of_2((arg - 1) +
                            (heap_segment_size - 1),
                            log2_heap_segment_size);
    }
    /* fall through */
  case GC_TRAP_FUNCTION_GET_LISP_HEAP_THRESHOLD:
    xpGPR(xp, imm0) = lisp_heap_gc_threshold;
    break;

  case GC_TRAP_FUNCTION_USE_LISP_HEAP_THRESHOLD:
    untenure_from_area(tenured_area);
    resize_dynamic_heap(a->active, lisp_heap_gc_threshold);
    if (egc_was_enabled) {
      if ((a->high - a->active) >= a->threshold) {
        tenure_to_area(tenured_area);
      }
    }
    xpGPR(xp, imm0) = lisp_heap_gc_threshold;
    break;

  case GC_TRAP_FUNCTION_SET_GC_NOTIFICATION_THRESHOLD:
    if ((signed_natural)arg >= 0) {
      lisp_heap_notify_threshold = arg;
      did_gc_notification_since_last_full_gc = false;
    }
    /* fall through */
  case GC_TRAP_FUNCTION_GET_GC_NOTIFICATION_THRESHOLD:
    xpGPR(xp, imm0) = lisp_heap_notify_threshold;
    break;

  case GC_TRAP_FUNCTION_ENSURE_STATIC_CONSES:
    ensure_static_conses(xp, tcr, 32768);
    break;

  case GC_TRAP_FUNCTION_FLASH_FREEZE:
    untenure_from_area(tenured_area);
    gc_like_from_xp(xp, flash_freeze, 0);
    a->active = (BytePtr) align_to_power_of_2(a->active, log2_page_size);
    tenured_area->static_dnodes = area_dnode(a->active, a->low);
    if (egc_was_enabled) {
      tenure_to_area(tenured_area);
    }
    xpGPR(xp, imm0) = tenured_area->static_dnodes << dnode_shift;
    break;

  case GC_TRAP_FUNCTION_ALLOCATION_CONTROL:
    switch (arg) {
    case 0: /* disable if allocation enabled */
      xpGPR(xp, arg_z) = lisp_nil;
      if (allocation_enabled) {
        TCR *other_tcr;
        ExceptionInformation *other_context;
        suspend_other_threads(true);
        normalize_tcr(xp, tcr, false);
        for (other_tcr = tcr->next; other_tcr != tcr;
             other_tcr = other_tcr->next) {
          other_context = other_tcr->pending_exception_context;
          if (other_context == NULL) {
            other_context = other_tcr->suspend_context;
          }
          normalize_tcr(other_context, other_tcr, true);
        }
        allocation_enabled = false;
        xpGPR(xp, arg_z) = t_value;
        resume_other_threads(true);
      }
      break;
    case 1: /* enable if disabled */
      xpGPR(xp, arg_z) = lisp_nil;
      if (!allocation_enabled) {
        allocation_enabled = true;
        xpGPR(xp, arg_z) = t_value;
      }
      break;
    default:
      xpGPR(xp, arg_z) = lisp_nil;
      if (allocation_enabled) {
        xpGPR(xp, arg_z) = t_value;
      }
      break;
    }
    break;

  default:
    update_bytes_allocated(tcr, (void *) ptr_from_lispobj(xpGPR(xp, allocptr)));

    if (selector == GC_TRAP_FUNCTION_IMMEDIATE_GC) {
      if (!full_gc_deferred) {
        gc_from_xp(xp, 0L);
        break;
      }
      /* Tried to do a full GC when gc was deferred.
         Fall through to GC_TRAP_FUNCTION_GC. */
      selector = GC_TRAP_FUNCTION_GC;
    }

    if (egc_was_enabled) {
      egc_control(false, (BytePtr) a->active);
    }
    gc_from_xp(xp, 0L);
    if (gc_deferred > gc_previously_deferred) {
      full_gc_deferred = 1;
    } else {
      full_gc_deferred = 0;
    }
    if (selector > GC_TRAP_FUNCTION_GC) {
      if (selector & GC_TRAP_FUNCTION_IMPURIFY) {
        impurify_from_xp(xp, 0L);
        lisp_global(OLDSPACE_DNODE_COUNT) = 0;
        gc_from_xp(xp, 0L);
      }
      if (selector & GC_TRAP_FUNCTION_PURIFY) {
        purify_from_xp(xp, 0L);
        lisp_global(OLDSPACE_DNODE_COUNT) = 0;
        gc_from_xp(xp, 0L);
      }
      if (selector & GC_TRAP_FUNCTION_SAVE_APPLICATION) {
        OSErr err;
        extern OSErr save_application(unsigned, Boolean);
        TCR *tcr = get_tcr(true);
        area *vsarea = tcr->vs_area;
        nrs_TOPLFUNC.vcell = *((LispObj *)(vsarea->high) - 1);
        err = save_application(arg, egc_was_enabled);
        if (err == noErr) {
          _exit(0);
        }
        fatal_oserr(": save_application", err);
      }
      switch (selector) {
      case GC_TRAP_FUNCTION_FREEZE:
        a->active = (BytePtr) align_to_power_of_2(a->active, log2_page_size);
        tenured_area->static_dnodes = area_dnode(a->active, a->low);
        xpGPR(xp, imm0) = tenured_area->static_dnodes << dnode_shift;
        break;
      default:
        break;
      }
    }

    if (egc_was_enabled) {
      egc_control(true, NULL);
    }
    break;
  }

  adjust_exception_pc(xp, 4);
  return true;
}


void
signal_stack_soft_overflow(ExceptionInformation *xp, unsigned reg)
{
  handle_error(xp, error_stack_overflow, reg, NULL);
}


Boolean
handle_sigfpe(ExceptionInformation *xp, TCR *tcr)
{
  return false;
}


/*
  is_write_fault: on ARM64 Linux, SEGV_ACCERR indicates a write to
  a protected (read-only or guarded) page.
*/
Boolean
is_write_fault(ExceptionInformation *xp, siginfo_t *info)
{
  return (info != NULL && info->si_code == SEGV_ACCERR);
}


OSStatus
do_hard_stack_overflow(ExceptionInformation *xp, protected_area_ptr area, BytePtr addr)
{
  reset_lisp_process(xp);
  return -1;
}


OSStatus
do_vsp_overflow(ExceptionInformation *xp, BytePtr addr)
{
  TCR *tcr = get_tcr(true);
  area *a = tcr->vs_area;
  protected_area_ptr vsp_soft = a->softprot;
  unprotect_area(vsp_soft);
  signal_stack_soft_overflow(xp, vsp);
  return 0;
}


OSStatus
do_soft_stack_overflow(ExceptionInformation *xp, protected_area_ptr prot_area, BytePtr addr)
{
  if (prot_area->why == kVSPsoftguard) {
    return do_vsp_overflow(xp, addr);
  }
  unprotect_area(prot_area);
  signal_stack_soft_overflow(xp, Rsp);
  return 0;
}


OSStatus
do_spurious_wp_fault(ExceptionInformation *xp, protected_area_ptr area, BytePtr addr)
{
  return -1;
}


protection_handler
 * protection_handlers[] = {
   do_spurious_wp_fault,
   do_soft_stack_overflow,
   do_soft_stack_overflow,
   do_soft_stack_overflow,
   do_hard_stack_overflow,
   do_hard_stack_overflow,
   do_hard_stack_overflow
   };


/*
  Lower (move toward 0) the "end" of the soft protected area associated
  with a by a page, if we can.
*/
void
adjust_soft_protection_limit(area *a)
{
  char *proposed_new_soft_limit = a->softlimit - 4096;
  protected_area_ptr p = a->softprot;

  if (proposed_new_soft_limit >= (p->start+16384)) {
    p->end = proposed_new_soft_limit;
    p->protsize = p->end-p->start;
    a->softlimit = proposed_new_soft_limit;
  }
  protect_area(p);
}


void
restore_soft_stack_limit(unsigned stkreg)
{
  area *a;
  TCR *tcr = get_tcr(true);

  switch (stkreg) {
  case Rsp:
    a = tcr->cs_area;
    if ((a->softlimit - 4096) > (a->hardlimit + 16384)) {
      a->softlimit -= 4096;
    }
    tcr->cs_limit = (LispObj)ptr_to_lispobj(a->softlimit);
    break;
  case vsp:
    a = tcr->vs_area;
    adjust_soft_protection_limit(a);
    break;
  }
}


/* Maybe this'll work someday.  We may have to do something to
   make the thread look like it's not handling an exception */
void
reset_lisp_process(ExceptionInformation *xp)
{
}


void
platform_new_heap_segment(ExceptionInformation *xp, TCR *tcr, BytePtr low, BytePtr high)
{
  tcr->last_allocptr = (void *)high;
  xpGPR(xp, allocptr) = (LispObj) high;
  xpGPR(xp, allocbase) = (LispObj) low;
  tcr->save_allocbase = (void *)low;
}


LispObj *
tcr_frame_ptr(TCR *tcr)
{
  ExceptionInformation *xp;
  LispObj *bp = NULL;

  if (tcr->pending_exception_context)
    xp = tcr->pending_exception_context;
  else {
    xp = tcr->suspend_context;
  }
  if (xp) {
    bp = (LispObj *) xpGPR(xp, Rsp);
  }
  return bp;
}


/* On ARM64, lisp_frame has savevsp, savelr, savefn, and padding (32 bytes).
   No marker word (unlike ARM32). */
Boolean
lisp_frame_p(lisp_frame *spPtr)
{
  /* For now, always return true — the frame walker is only called
     on known cstack regions.  A more robust check would validate
     that savelr is within a known code area. */
  return true;
}


OSStatus
handle_protection_violation(ExceptionInformation *xp, siginfo_t *info,
                            TCR *tcr, int old_valence)
{
  BytePtr addr;
  protected_area_ptr area;
  protection_handler *handler;
  extern Boolean touch_page(void *);
  extern void touch_page_end(void);

#ifdef LINUX
  addr = (BytePtr) ((natural) (xpFaultAddress(xp)));
#else
  if (info) {
    addr = (BytePtr)(info->si_addr);
  } else {
    addr = (BytePtr) ((natural) (xpFaultAddress(xp)));
  }
#endif

  if (addr && (addr == tcr->safe_ref_address)) {
    adjust_exception_pc(xp, 4);
    xpGPR(xp, imm0) = 0;
    return true;
  }

  if (xpPC(xp) == (pc)touch_page) {
    xpGPR(xp, imm0) = 0;
    xpPC(xp) = (pc)touch_page_end;
    return true;
  }

#if defined(DARWIN) && defined(ARM64)
  /* W^X page toggle for macOS ARM64.
     Pages cannot be simultaneously writable and executable.
     Heap pages start as RX (after make_heap_executable).
     Write faults toggle individual pages to RW.
     Execute faults toggle pages back to RX.
     Note: use 'struct area' to avoid shadowing by local 'area' variable. */
  {
    uint32_t esr = UC_MCONTEXT(xp)->__es.__esr;
    uint32_t ec = (esr >> 26) & 0x3F;
    struct area *dyn = (struct area *)((struct area *)all_areas)->succ;
    Boolean in_heap = ((addr >= dyn->low && addr < dyn->high) ||
                       (addr >= static_space_start &&
                        addr < static_space_limit));

    if (in_heap) {
      natural page_start = truncate_to_power_of_2((natural)addr, log2_page_size);

      if (ec == 0x20 || ec == 0x21) {
        /* Instruction Abort: page is RW, needs RX for code execution */
        sys_icache_invalidate((void *)page_start, page_size);
        mprotect((void *)page_start, page_size, PROT_READ | PROT_EXEC);
        return true;
      } else if ((ec == 0x24 || ec == 0x25) && (esr & (1 << 6))) {
        /* Data Abort with WnR=1: write fault, page needs RW */
        mprotect((void *)page_start, page_size, PROT_READ | PROT_WRITE);
        return true;
      }
    }
  }
#endif

  {
    Boolean wf = is_write_fault(xp, info);
    area = wf ? find_protected_area(addr) : NULL;
    fprintf(dbgout, "handle_prot_viol: addr=%p write=%d prot_area=%p vs_low=%p vs_high=%p vsp=0x%lx\n",
            addr, wf, area,
            tcr->vs_area ? (void*)tcr->vs_area->low : NULL,
            tcr->vs_area ? (void*)tcr->vs_area->high : NULL,
            (unsigned long)xpGPR(xp, 25));
    fflush(dbgout);
    if (wf && area != NULL) {
      handler = protection_handlers[area->why];
      return handler(xp, area, addr);
    } else if (wf) {
      if ((addr >= readonly_area->low) &&
          (addr < readonly_area->active)) {
        UnProtectMemory((LogicalAddress)(truncate_to_power_of_2(addr, log2_page_size)),
                        page_size);
        return true;
      }
    }
  }
  if (old_valence == TCR_STATE_LISP) {
    LispObj cmain = nrs_CMAIN.vcell;

    if (is_uvector_fulltag(fulltag_of(cmain)) &&
        (header_subtag(header_of(cmain)) == subtag_macptr)) {
      callback_for_trap(nrs_CMAIN.vcell, xp,
                        is_write_fault(xp, info) ? SIGBUS : SIGSEGV,
                        (natural)addr, NULL);
    }
  }
  return false;
}


Boolean
handle_error(ExceptionInformation *xp, unsigned arg1, unsigned arg2, int *bumpP)
{
  LispObj errdisp = nrs_ERRDISP.vcell;

  fprintf(dbgout, "handle_error: PC=%016lx LR=%016lx arg1=%u arg2=%08x errdisp=%016lx tag=0x%02lx\n",
          (unsigned long)(natural)xpPC(xp), (unsigned long)xpGPR(xp, 30),
          arg1, arg2, (unsigned long)errdisp, (unsigned long)fulltag_of(errdisp));
  fprintf(dbgout, "  nfn(x10)=%016lx fname(x9)=%016lx arg_z(x15)=%016lx\n",
          (unsigned long)xpGPR(xp, 10), (unsigned long)xpGPR(xp, 9),
          (unsigned long)xpGPR(xp, 15));
  /* Try to print the symbol name from x9 (fname) */
  {
    LispObj fname_tagged = xpGPR(xp, 9);
    natural fname_raw = fname_tagged & 0x00FFFFFFFFFFFFFF;
    if (fname_raw > 0x100000000 && fname_raw < 0x400000000000) {
      LispObj pname_tagged = ((LispObj *)fname_raw)[0]; /* symbol.pname */
      natural pname_raw = pname_tagged & 0x00FFFFFFFFFFFFFF;
      if (pname_raw > 0x100000000 && pname_raw < 0x400000000000) {
        LispObj pname_hdr = ((LispObj *)pname_raw)[-1];
        natural pname_len = pname_hdr & 0x00FFFFFFFFFFFFFF;
        char *pname_data = (char *)pname_raw;
        fprintf(dbgout, "  pname: tagged=0x%lx raw=0x%lx hdr=0x%lx len=%lu\n",
                (unsigned long)pname_tagged, (unsigned long)pname_raw,
                (unsigned long)pname_hdr, (unsigned long)pname_len);
        if (pname_len > 0 && pname_len < 256) {
          unsigned char pname_subtag = (pname_hdr >> 56) & 0xFF;
          int char_size = (pname_subtag & 0x7F) == 7 ? 4 : 1; /* simple-string=4, base-string=1 */
          int pi;
          fprintf(dbgout, "  fname symbol name(%d-byte chars): \"", char_size);
          for (pi = 0; pi < (int)pname_len; pi++)
            fprintf(dbgout, "%c", pname_data[pi * char_size]);
          fprintf(dbgout, "\"\n");
        }
      }
    }
  }
  /* For type errors (code 157), read arg_z symbol name (expected type) */
  {
    LispObj ax = xpGPR(xp, 13);
    if (ax == 157) {  /* $xwrongtype */
      LispObj az = xpGPR(xp, 15);
      unsigned az_tag = (unsigned)(az >> 56);
      natural az_raw = az & 0x00FFFFFFFFFFFFFF;
      if (az_tag == 0x63 && az_raw > 0x100000000LL && az_raw < 0x400000000000LL) {
        LispObj *sym = (LispObj *)az_raw;
        LispObj pname = sym[0];  /* symbol.pname is first slot after header */
        natural pname_raw = pname & 0x00FFFFFFFFFFFFFF;
        if (pname_raw > 0x100000000LL && pname_raw < 0x400000000000LL) {
          LispObj pname_hdr = *((LispObj *)pname_raw - 1);
          int pname_len = (int)(pname_hdr & 0xFFFFFFFF);
          unsigned char *pname_data = (unsigned char *)pname_raw;
          if (pname_len > 0 && pname_len < 256) {
            unsigned char pname_subtag = (pname_hdr >> 56) & 0xFF;
            int char_size = (pname_subtag & 0x7F) == 7 ? 4 : 1;
            int pi;
            fprintf(dbgout, "  TYPE ERROR: expected type = \"");
            for (pi = 0; pi < pname_len; pi++)
              fprintf(dbgout, "%c", pname_data[pi * char_size]);
            fprintf(dbgout, "\"\n");
          }
        }
      }
      /* Also show arg_y (the value) */
      LispObj ay = xpGPR(xp, 14);
      fprintf(dbgout, "  TYPE ERROR: value = 0x%lx (tag=0x%02x)\n",
              (unsigned long)ay, (unsigned)(ay >> 56));
    }
    fflush(dbgout);
  }
  /* Dump arg_z (x15) and arg_y (x11) if they look like heap pointers */
  {
    LispObj az = xpGPR(xp, 15);
    unsigned az_tag = (unsigned)(az >> 56);
    natural az_raw = az & 0x00FFFFFFFFFFFFFF;
    if (az_tag != 0 && az_tag != 0xFF && az_raw > 0x100000000LL && az_raw < 0x400000000000LL) {
      LispObj *ap = (LispObj *)(az_raw - 16);
      int ai;
      fprintf(dbgout, "  arg_z contents (tag=0x%02x raw=0x%lx):\n", az_tag, (unsigned long)az_raw);
      for (ai = 0; ai < 6; ai++) {
        fprintf(dbgout, "    [%+d] = %016lx (tag=0x%02lx)\n",
                (ai - 2) * 8, (unsigned long)ap[ai], (unsigned long)(ap[ai] >> 56));
      }
    }
    LispObj ay = xpGPR(xp, 11);
    unsigned ay_tag = (unsigned)(ay >> 56);
    natural ay_raw = ay & 0x00FFFFFFFFFFFFFF;
    if (ay_tag != 0 && ay_tag != 0xFF && ay_raw > 0x100000000LL && ay_raw < 0x400000000000LL) {
      LispObj *ap2 = (LispObj *)(ay_raw - 16);
      int ai2;
      fprintf(dbgout, "  arg_y contents (tag=0x%02x raw=0x%lx):\n", ay_tag, (unsigned long)ay_raw);
      for (ai2 = 0; ai2 < 6; ai2++) {
        fprintf(dbgout, "    [%+d] = %016lx (tag=0x%02lx)\n",
                (ai2 - 2) * 8, (unsigned long)ap2[ai2], (unsigned long)(ap2[ai2] >> 56));
      }
    }
  }
  /* Dump instructions around LR to see the calling code */
  {
    natural lr = xpGPR(xp, 30);
    if (lr > 0x200000000LL && lr < 0x400000000000LL) {
      uint32_t *code = (uint32_t *)(lr - 64);
      fprintf(dbgout, "  code@LR-64: %08x %08x %08x %08x %08x %08x %08x %08x\n",
              code[0], code[1], code[2], code[3], code[4], code[5], code[6], code[7]);
      code = (uint32_t *)(lr - 32);
      fprintf(dbgout, "  code@LR-32: %08x %08x %08x %08x %08x %08x %08x %08x\n",
              code[0], code[1], code[2], code[3], code[4], code[5], code[6], code[7]);
      code = (uint32_t *)lr;
      fprintf(dbgout, "  code@LR:    %08x %08x %08x %08x %08x %08x %08x %08x\n",
              code[0], code[1], code[2], code[3], code[4], code[5], code[6], code[7]);
    }
  }
  /* Dump lisp frame at sp to identify calling function */
  {
    natural sp = xpSP(xp);
    fprintf(dbgout, "  sp=%016lx x10=%016lx x12=%016lx\n",
            (unsigned long)sp, (unsigned long)xpGPR(xp, 10),
            (unsigned long)xpGPR(xp, 12));
    if (sp > 0x100000000LL && sp < 0x800000000000LL) {
      LispObj *frame = (LispObj *)sp;
      fprintf(dbgout, "  frame[0](savevsp)=%016lx frame[1](savelr)=%016lx frame[2](savefn)=%016lx frame[3]=%016lx\n",
              (unsigned long)frame[0], (unsigned long)frame[1],
              (unsigned long)frame[2], (unsigned long)frame[3]);
      /* Try to read function name from savefn's constants */
      {
        LispObj savefn = frame[2];
        natural fn_raw = savefn & 0x00FFFFFFFFFFFFFF;
        if (fn_raw > 0x100000000LL && fn_raw < 0x400000000000LL) {
          LispObj *fn_slots = (LispObj *)fn_raw;
          LispObj fn_hdr = fn_slots[-1];
          natural fn_nslots = fn_hdr & 0x00FFFFFFFFFFFFFF;
          fprintf(dbgout, "  savefn hdr=%016lx nslots=%lu\n",
                  (unsigned long)fn_hdr, (unsigned long)fn_nslots);
          /* Last slot is lfbits, second-to-last is name */
          if (fn_nslots > 2 && fn_nslots < 100) {
            LispObj name_slot = fn_slots[fn_nslots - 2];
            natural name_raw = name_slot & 0x00FFFFFFFFFFFFFF;
            fprintf(dbgout, "  fn name slot=%016lx\n", (unsigned long)name_slot);
            if (name_raw > 0x100000000LL && name_raw < 0x400000000000LL) {
              LispObj pname = ((LispObj *)name_raw)[0]; /* symbol.pname */
              natural pname_raw = pname & 0x00FFFFFFFFFFFFFF;
              if (pname_raw > 0x100000000LL && pname_raw < 0x400000000000LL) {
                LispObj phdr = ((LispObj *)pname_raw)[-1];
                natural plen = phdr & 0x00FFFFFFFFFFFFFF;
                if (plen > 0 && plen < 256) {
                  unsigned char ps = (phdr >> 56) & 0xFF;
                  int cs = (ps & 0x7F) == 7 ? 4 : 1;
                  char *pd = (char *)pname_raw;
                  int pi;
                  fprintf(dbgout, "  savefn name(%d): \"", cs);
                  for (pi = 0; pi < (int)plen; pi++)
                    fprintf(dbgout, "%c", pd[pi * cs]);
                  fprintf(dbgout, "\"\n");
                }
              }
            }
          }
          /* Also dump first few constant slots */
          int si;
          for (si = 0; si < (int)fn_nslots && si < 12; si++) {
            fprintf(dbgout, "  fn_slot[%d]=%016lx\n", si, (unsigned long)fn_slots[si]);
          }
        }
      }
      /* Walk up to 5 lisp frames */
      int fi;
      for (fi = 0; fi < 5; fi++) {
        LispObj *fr = (LispObj *)(sp + (fi + 1) * 32);
        natural fr_addr = (natural)fr;
        if (fr_addr < 0x100000000LL || fr_addr > 0x800000000000LL) break;
        LispObj fr_savefn = fr[2];
        natural fr_fn_raw = fr_savefn & 0x00FFFFFFFFFFFFFF;
        fprintf(dbgout, "  frame[%d] @%p: savevsp=%016lx savelr=%016lx savefn=%016lx",
                fi + 1, fr, (unsigned long)fr[0], (unsigned long)fr[1], (unsigned long)fr_savefn);
        /* Try to print function name */
        if (fr_fn_raw > 0x100000000LL && fr_fn_raw < 0x400000000000LL) {
          LispObj *fr_fn_slots = (LispObj *)fr_fn_raw;
          LispObj fr_fn_hdr = fr_fn_slots[-1];
          natural fr_fn_ns = fr_fn_hdr & 0x00FFFFFFFFFFFFFF;
          if (fr_fn_ns > 2 && fr_fn_ns < 100) {
            LispObj fr_name = fr_fn_slots[fr_fn_ns - 2];
            natural fr_name_raw = fr_name & 0x00FFFFFFFFFFFFFF;
            if (fr_name_raw > 0x100000000LL && fr_name_raw < 0x400000000000LL) {
              LispObj fr_pn = ((LispObj *)fr_name_raw)[0];
              natural fr_pn_raw = fr_pn & 0x00FFFFFFFFFFFFFF;
              if (fr_pn_raw > 0x100000000LL && fr_pn_raw < 0x400000000000LL) {
                LispObj fr_ph = ((LispObj *)fr_pn_raw)[-1];
                natural fr_pl = fr_ph & 0x00FFFFFFFFFFFFFF;
                if (fr_pl > 0 && fr_pl < 256) {
                  unsigned char fr_ps = (fr_ph >> 56) & 0xFF;
                  int fr_cs = (fr_ps & 0x7F) == 7 ? 4 : 1;
                  char *fr_pd = (char *)fr_pn_raw;
                  int fr_pi;
                  fprintf(dbgout, " \"");
                  for (fr_pi = 0; fr_pi < (int)fr_pl; fr_pi++)
                    fprintf(dbgout, "%c", fr_pd[fr_pi * fr_cs]);
                  fprintf(dbgout, "\"");
                }
              }
            }
          }
        }
        fprintf(dbgout, "\n");
      }
    }
  }
  /* Dump constants of frame[1] and frame[2] functions too */
  {
    natural sp = xpSP(xp);
    int fi2;
    for (fi2 = 1; fi2 <= 3; fi2++) {
      LispObj *fr2 = (LispObj *)(sp + fi2 * 32);
      LispObj fn2 = fr2[2];
      natural fn2_raw = fn2 & 0x00FFFFFFFFFFFFFF;
      if (fn2_raw > 0x100000000LL && fn2_raw < 0x400000000000LL) {
        LispObj *fn2_slots = (LispObj *)fn2_raw;
        LispObj fn2_hdr = fn2_slots[-1];
        natural fn2_ns = fn2_hdr & 0x00FFFFFFFFFFFFFF;
        if (fn2_ns > 0 && fn2_ns < 50) {
          fprintf(dbgout, "  frame[%d] fn constants (%lu slots):", fi2, (unsigned long)fn2_ns);
          int si2;
          for (si2 = 0; si2 < (int)fn2_ns && si2 < 12; si2++) {
            fprintf(dbgout, " %016lx", (unsigned long)fn2_slots[si2]);
          }
          fprintf(dbgout, "\n");
        }
      }
    }
  }
  /* Dump vsp stack to trace caller */
  {
    LispObj *dbg_vsp = (LispObj *)xpGPR(xp, 25);
    int dbg_i;
    fprintf(dbgout, "  vsp=%p stack dump:\n", dbg_vsp);
    for (dbg_i = 0; dbg_i < 32; dbg_i++) {
      LispObj val = dbg_vsp[dbg_i];
      unsigned tag = (unsigned)(val >> 56);
      fprintf(dbgout, "    vsp[%2d] = %016lx (tag=0x%02x)\n", dbg_i, (unsigned long)val, tag);
    }
  }
  /* Dump memory around any non-fixnum vsp values to inspect object headers */
  {
    int vi;
    for (vi = 0; vi < 8; vi++) {
      LispObj val = ((LispObj *)xpGPR(xp, 25))[vi];
      unsigned vtag = (unsigned)(val >> 56);
      if (vtag != 0 && vtag != 0xFF && vtag != 0x02) {
        natural raw = val & 0x00FFFFFFFFFFFFFF;
        if (raw > 0x100000000LL && raw < 0x400000000000LL) {
          LispObj *mp = (LispObj *)(raw - 24);
          fprintf(dbgout, "  mem@vsp[%d]=0x%lx (tag=0x%02x addr=0x%lx):\n",
                  vi, (unsigned long)val, vtag, (unsigned long)raw);
          int mi;
          for (mi = 0; mi < 8; mi++) {
            fprintf(dbgout, "    [%+d] = %016lx (tag=0x%02lx)\n",
                    (mi - 3) * 8, (unsigned long)mp[mi], (unsigned long)(mp[mi] >> 56));
          }
        }
      }
    }
  }
  /* Also dump code around each frame's savelr (wider window) */
  {
    natural sp = xpSP(xp);
    int fi;
    for (fi = 0; fi < 3; fi++) {
      LispObj *fr = (LispObj *)(sp + (fi + 1) * 32);
      natural lr = (natural)fr[1];
      if (lr > 0x200000000LL && lr < 0x400000000000LL) {
        uint32_t *code;
        code = (uint32_t *)(lr - 64);
        fprintf(dbgout, "  frame[%d] code@savelr-64: %08x %08x %08x %08x %08x %08x %08x %08x\n",
                fi + 1, code[0], code[1], code[2], code[3],
                code[4], code[5], code[6], code[7]);
        code = (uint32_t *)(lr - 32);
        fprintf(dbgout, "  frame[%d] code@savelr-32: %08x %08x %08x %08x %08x %08x %08x %08x\n",
                fi + 1, code[0], code[1], code[2], code[3],
                code[4], code[5], code[6], code[7]);
        code = (uint32_t *)lr;
        fprintf(dbgout, "  frame[%d] code@savelr+00: %08x %08x %08x %08x %08x %08x %08x %08x\n",
                fi + 1, code[0], code[1], code[2], code[3],
                code[4], code[5], code[6], code[7]);
        code = (uint32_t *)(lr + 32);
        fprintf(dbgout, "  frame[%d] code@savelr+32: %08x %08x %08x %08x %08x %08x %08x %08x\n",
                fi + 1, code[0], code[1], code[2], code[3],
                code[4], code[5], code[6], code[7]);
      }
    }
  }
  /* Dump top of vstack (near savevsp) to see initial list values */
  {
    natural sp = xpSP(xp);
    LispObj *frame0 = (LispObj *)sp;
    natural savevsp0 = (natural)frame0[0];
    if (savevsp0 > 0x100000000LL && savevsp0 < 0x800000000000LL) {
      LispObj *top_vsp = (LispObj *)savevsp0;
      int ti;
      fprintf(dbgout, "  vstack top (savevsp=%p):\n", top_vsp);
      for (ti = -4; ti < 8; ti++) {
        LispObj val = top_vsp[ti];
        unsigned vtag = (unsigned)(val >> 56);
        fprintf(dbgout, "    top[%+d] = %016lx (tag=0x%02x)", ti, (unsigned long)val, vtag);
        /* If it looks like a cons (tag 0x03), show CAR and CDR */
        if (vtag == 0x03) {
          natural cons_raw = val & 0x00FFFFFFFFFFFFFF;
          if (cons_raw > 0x100000000LL && cons_raw < 0x400000000000LL) {
            LispObj car_val = *(LispObj *)cons_raw;         /* cons.car = offset 0 */
            LispObj cdr_val = *(LispObj *)(cons_raw - 8);   /* cons.cdr = offset -8 */
            fprintf(dbgout, "  CAR=%016lx CDR=%016lx", (unsigned long)car_val, (unsigned long)cdr_val);
          }
        }
        fprintf(dbgout, "\n");
      }
    }
  }
  fflush(dbgout);
  /* Dump %all-packages% to diagnose package lookup failures */
  {
    LispObj pkglist = nrs_ALL_PACKAGES.vcell;
    /* Also check TLB access path */
    LispObj binding_idx = nrs_ALL_PACKAGES.binding_index;
    TCR *tcr = get_tcr(false);
    fprintf(dbgout, "  %%all-packages%% vcell=%016lx binding_idx=%ld\n",
            (unsigned long)pkglist, (long)binding_idx);
    if (tcr) {
      fprintf(dbgout, "  tcr=%p tlb_pointer=%016lx tlb_limit=%ld\n",
              tcr, (unsigned long)tcr->tlb_pointer, (long)tcr->tlb_limit);
      /* On ARM64 (fixnumshift=0), binding_idx is a slot index, NOT a byte offset.
         The buggy inline code in the boot image uses it directly as byte offset.
         The correct byte offset is binding_idx * node_size. */
      natural byte_offset_correct = (natural)binding_idx * node_size;
      natural byte_offset_buggy = (natural)binding_idx;  /* what inline code does */
      fprintf(dbgout, "  binding_idx=%ld correct_byte_off=%lu buggy_byte_off=%lu tlb_limit=%lu\n",
              (long)binding_idx, (unsigned long)byte_offset_correct,
              (unsigned long)byte_offset_buggy, (unsigned long)tcr->tlb_limit);
      if (byte_offset_buggy < (natural)tcr->tlb_limit) {
        /* Show what the buggy inline code actually reads */
        LispObj buggy_val = *(LispObj *)((char *)tcr->tlb_pointer + byte_offset_buggy);
        fprintf(dbgout, "  TLB@buggy_off[%lu]=%016lx (ntlb=%016lx)\n",
                (unsigned long)byte_offset_buggy, (unsigned long)buggy_val,
                (unsigned long)no_thread_local_binding_marker);
        if (buggy_val != no_thread_local_binding_marker) {
          fprintf(dbgout, "  WARNING: buggy TLB read gives non-NTLB value!\n");
          pkglist = buggy_val;
        }
      }
      if (byte_offset_correct < (natural)tcr->tlb_limit) {
        LispObj correct_val = *(LispObj *)((char *)tcr->tlb_pointer + byte_offset_correct);
        fprintf(dbgout, "  TLB@correct_off[%lu]=%016lx\n",
                (unsigned long)byte_offset_correct, (unsigned long)correct_val);
      } else {
        fprintf(dbgout, "  correct byte offset %lu exceeds tlb_limit %lu (would use vcell)\n",
                (unsigned long)byte_offset_correct, (unsigned long)tcr->tlb_limit);
      }
    }
    fprintf(dbgout, "  effective %%all-packages%% = %016lx (tag=0x%02lx)\n",
            (unsigned long)pkglist, (unsigned long)fulltag_of(pkglist));
    /* Also check *package* */
    {
      LispObj pkg_vcell = nrs_PACKAGE.vcell;
      LispObj pkg_bidx = nrs_PACKAGE.binding_index;
      fprintf(dbgout, "  *package* vcell=%016lx binding_idx=%ld\n",
              (unsigned long)pkg_vcell, (long)pkg_bidx);
      natural pkg_byte_off = (natural)pkg_bidx * node_size;
      natural pkg_buggy_off = (natural)pkg_bidx;
      if (pkg_buggy_off < (natural)tcr->tlb_limit) {
        LispObj bv = *(LispObj *)((char *)tcr->tlb_pointer + pkg_buggy_off);
        fprintf(dbgout, "  *package* TLB@buggy[%lu]=%016lx\n",
                (unsigned long)pkg_buggy_off, (unsigned long)bv);
      }
      if (pkg_byte_off < (natural)tcr->tlb_limit) {
        LispObj cv = *(LispObj *)((char *)tcr->tlb_pointer + pkg_byte_off);
        fprintf(dbgout, "  *package* TLB@correct[%lu]=%016lx\n",
                (unsigned long)pkg_byte_off, (unsigned long)cv);
      }
      /* Check *early-boot* too */
      fprintf(dbgout, "  checking first 20 TLB slots for non-NTLB values:\n");
      int si;
      for (si = 0; si < 20 && si * (int)node_size < (int)tcr->tlb_limit; si++) {
        LispObj sv = *(LispObj *)((char *)tcr->tlb_pointer + si * node_size);
        if (sv != no_thread_local_binding_marker) {
          fprintf(dbgout, "    TLB[slot %d, off %d]=%016lx (tag=0x%02lx)\n",
                  si, (int)(si * node_size), (unsigned long)sv, (unsigned long)fulltag_of(sv));
        }
      }
    }
    int pkg_count = 0;
    while (fulltag_of(pkglist) == fulltag_cons && pkg_count < 10) {
      LispObj pkg = car(pkglist);
      unsigned pkg_tag = fulltag_of(pkg);
      fprintf(dbgout, "  pkg[%d] = %016lx (tag=0x%02lx)", pkg_count, (unsigned long)pkg, (unsigned long)pkg_tag);
      /* Try to read package.names (5th slot, index 4 from base) */
      natural pkg_raw = untag(pkg);
      if (pkg_raw > 0x100000000LL && pkg_raw < 0x400000000000LL) {
        LispObj pkg_hdr = *((LispObj *)pkg_raw - 1);
        fprintf(dbgout, " hdr=%016lx subtag=0x%02lx", (unsigned long)pkg_hdr, (unsigned long)header_subtag(pkg_hdr));
        /* names is at offset 5*8=40 from base (after header) = slot index 4 from deref */
        LispObj names_list = deref(pkg, 5); /* pkg.names */
        fprintf(dbgout, " names=%016lx", (unsigned long)names_list);
        /* Walk names list */
        int ni = 0;
        LispObj nl = names_list;
        while (fulltag_of(nl) == fulltag_cons && ni < 5) {
          LispObj name_str = car(nl);
          natural str_raw = untag(name_str);
          if (str_raw > 0x100000000LL && str_raw < 0x400000000000LL) {
            LispObj str_hdr = *((LispObj *)str_raw - 1);
            natural str_len = str_hdr & 0x00FFFFFFFFFFFFFFLL;
            unsigned char str_subtag = header_subtag(str_hdr);
            int char_size = (str_subtag & 0x7F) == 7 ? 4 : 1;
            char *str_data = (char *)str_raw;
            fprintf(dbgout, "\n    name[%d]: tag=0x%02lx hdr=%016lx len=%lu subtag=0x%02x \"",
                    ni, (unsigned long)fulltag_of(name_str), (unsigned long)str_hdr,
                    (unsigned long)str_len, str_subtag);
            int ci;
            for (ci = 0; ci < (int)str_len && ci < 64; ci++)
              fprintf(dbgout, "%c", str_data[ci * char_size]);
            fprintf(dbgout, "\"");
            /* Also dump raw bytes of first 16 chars */
            fprintf(dbgout, " raw:");
            for (ci = 0; ci < (int)str_len * char_size && ci < 32; ci++)
              fprintf(dbgout, " %02x", (unsigned char)str_data[ci]);
          }
          nl = cdr(nl);
          ni++;
        }
      }
      fprintf(dbgout, "\n");
      pkglist = cdr(pkglist);
      pkg_count++;
    }
    fprintf(dbgout, "  total packages iterated: %d, remaining list tag=0x%02lx\n",
            pkg_count, (unsigned long)fulltag_of(pkglist));
    fflush(dbgout);
  }
  if (errdisp == unbound_marker) {
    /* During cold boot, %err-disp is unbound.  Try to handle $xnopkg
       (package-not-found) by looking up the package at the C level and
       returning it as the result of %kernel-restart. */
    LispObj arg_y_val = xpGPR(xp, 14);  /* $xnopkg code */
    LispObj arg_z_val = xpGPR(xp, 15);  /* package name string */
    if (arg_y_val == 0x82) {  /* $xnopkg = 130 */
      static int xnopkg_count = 0;
      xnopkg_count++;
      if (xnopkg_count <= 5 || (xnopkg_count % 100) == 0)
        fprintf(dbgout, "  $xnopkg attempt #%d, LR=%016lx\n", xnopkg_count, (unsigned long)xpGPR(xp, 30));
      if (xnopkg_count > 500) {
        fprintf(dbgout, "  too many $xnopkg workarounds (%d), aborting\n", xnopkg_count);
        fflush(dbgout);
        _exit(1);
      }
      /* Walk %all-packages% to find the package by name */
      LispObj search_raw = untag(arg_z_val);
      if (search_raw > 0x100000000LL && search_raw < 0x400000000000LL) {
        LispObj search_hdr = *((LispObj *)search_raw - 1);
        natural search_len = header_element_count(search_hdr);
        unsigned char search_subtag = header_subtag(search_hdr);
        int search_cs = (search_subtag & 0x7F) == 7 ? 4 : 1;
        char *search_data = (char *)search_raw;

        LispObj pkglist = nrs_ALL_PACKAGES.vcell;
        LispObj found_pkg = 0;
        while (fulltag_of(pkglist) == fulltag_cons) {
          LispObj pkg = car(pkglist);
          LispObj names = deref(pkg, 5);  /* pkg.names = slot 4 */
          LispObj nl = names;
          while (fulltag_of(nl) == fulltag_cons) {
            LispObj ns = car(nl);
            natural ns_raw = untag(ns);
            if (ns_raw > 0x100000000LL) {
              LispObj ns_hdr = *((LispObj *)ns_raw - 1);
              natural ns_len = header_element_count(ns_hdr);
              unsigned char ns_subtag = header_subtag(ns_hdr);
              int ns_cs = (ns_subtag & 0x7F) == 7 ? 4 : 1;
              if (ns_len == search_len) {
                int match = 1;
                natural ci;
                for (ci = 0; ci < search_len; ci++) {
                  unsigned char a = ((unsigned char *)search_raw)[ci * search_cs];
                  unsigned char b = ((unsigned char *)ns_raw)[ci * ns_cs];
                  if (a != b) { match = 0; break; }
                }
                if (match) { found_pkg = pkg; break; }
              }
            }
            nl = cdr(nl);
          }
          if (found_pkg) break;
          pkglist = cdr(pkglist);
        }
        if (found_pkg) {
          fprintf(dbgout, "handle_error: $xnopkg workaround — found package %016lx\n",
                  (unsigned long)found_pkg);
          /* Set *package* vcell directly */
          nrs_PACKAGE.vcell = found_pkg;
          fprintf(dbgout, "  set *package* vcell to %016lx\n", (unsigned long)found_pkg);
          /* Pop set-package's lisp frame and return to its caller.
             Frame layout: [savevsp, savelr, savefn, pad] at SP. */
          {
            LispObj *frame = (LispObj *)xpSP(xp);
            LispObj savevsp = frame[0];
            LispObj savelr  = frame[1];
            LispObj savefn  = frame[2];
            LispObj savefp  = frame[3];
            fprintf(dbgout, "  popping set-package frame: savevsp=%016lx savelr=%016lx savefn=%016lx savefp=%016lx\n",
                    (unsigned long)savevsp, (unsigned long)savelr, (unsigned long)savefn, (unsigned long)savefp);
            xpGPR(xp, 25) = savevsp;       /* restore vsp */
            xpGPR(xp, 10) = savefn;        /* restore fn */
            xpGPR(xp, 15) = found_pkg;     /* arg_z = return value */
            xpFP(xp) = savefp;             /* restore fp (x29) */
            xpPC(xp) = (pc)(natural)savelr; /* return to caller */
            xpSP(xp) = ((natural)frame) + 32; /* pop frame */
          }
          fflush(dbgout);
          *bumpP = 0;
          return true;
        }
      }
    }
    fprintf(dbgout, "handle_error: %%err-disp is unbound — aborting.\n");
    fflush(dbgout);
    _exit(1);
  }
  if (is_uvector_fulltag(fulltag_of(errdisp)) &&
      (header_subtag(header_of(errdisp)) == subtag_macptr)) {
    return callback_for_trap(errdisp, xp, arg1, arg2, bumpP);
  }
  return false;
}


/*
  ================================================================
  Chunk 4: Exception dispatch.

  register_codevector_contains_pc — find code vector containing PC.
  callback_for_trap — callback wrapper for error/trap dispatch.
  callback_to_lisp — callback to Lisp error/exception handler.
  allocate_list — allocate a list of cons cells in bulk.
  extend_tcr_tlb — grow the thread-local binding table.
  handle_uuo — dispatch HLT-based UUOs.
  handle_exception — main exception dispatcher.
  ================================================================
*/


natural
register_codevector_contains_pc(natural lisp_function, pc where)
{
  natural code_vector, size;

  if (is_uvector_fulltag(fulltag_of(lisp_function)) &&
      (header_subtag(header_of(lisp_function)) == subtag_function)) {
    code_vector = deref(lisp_function, 2);
    size = header_element_count(header_of(code_vector)) << 2;
    /* untag(code_vector) = base + node_size = first instruction address */
    if ((untag(code_vector) <= (natural)where) &&
        ((natural)where < (untag(code_vector) + size)))
      return code_vector;
  }

  return 0;
}


int
callback_for_trap(LispObj callback_macptr, ExceptionInformation *xp,
                  natural info, natural arg, int *bumpP)
{
  return callback_to_lisp(callback_macptr, xp, info, arg, bumpP);
}


int
callback_to_lisp(LispObj callback_macptr, ExceptionInformation *xp,
                 natural arg1, natural arg2, int *bumpP)
{
  natural callback_ptr;
  area *a;
  natural fnreg = Rfn, codevector, offset;
  pc where = xpPC(xp);
  int delta;

  codevector = register_codevector_contains_pc(xpGPR(xp, fnreg), where);
  if (codevector == 0) {
    fnreg = nfn;
    codevector = register_codevector_contains_pc(xpGPR(xp, fnreg), where);
    if (codevector == 0) {
      fnreg = 0;
    }
  }
  if (codevector) {
    /* untag(codevector) = base + node_size = first instruction address.
       Offset is the byte distance from there to the current PC. */
    offset = (natural)where - untag(codevector);
  } else {
    offset = (natural)where;
  }

  TCR *tcr = get_tcr(true);

  /* Put the active stack pointer where .SPcallback expects it.
     On ARM64, Rsp (x31) is accessed via xpSP, not xpGPR. */
  a = tcr->cs_area;
  a->active = (BytePtr) xpSP(xp);

  /* Copy globals from the exception frame to tcr */
  tcr->save_allocptr = (void *)ptr_from_lispobj(xpGPR(xp, allocptr));
  tcr->save_vsp = (LispObj *) ptr_from_lispobj(xpGPR(xp, vsp));

  /* Call back to Lisp.  Lisp will handle trampolining through some
     code that will push lr/fn & pc/nfn stack frames for backtrace. */
  callback_ptr = deref(callback_macptr, 1);  /* macptr.address */
  UNLOCK(lisp_global(EXCEPTION_LOCK), tcr);
  delta = ((int (*)())callback_ptr)(xp, arg1, arg2, fnreg, offset);
  LOCK(lisp_global(EXCEPTION_LOCK), tcr);

  if (bumpP) {
    *bumpP = delta;
  }

  /* Copy GC registers back into exception frame */
  xpGPR(xp, allocptr) = (LispObj) ptr_to_lispobj(tcr->save_allocptr);
  return true;
}


/*
 * Allocate a large list, where "large" means "large enough to
 * possibly trigger the EGC several times if this was done by
 * individually allocating each CONS."  The number of conses to
 * allocate is in arg_z; arg_y contains the initial element.
 * On successful return, the list will be in arg_z.
 */
Boolean
allocate_list(ExceptionInformation *xp, TCR *tcr)
{
  natural
    nconses = unbox_fixnum(xpGPR(xp, arg_z)),
    bytes_needed = nconses << dnode_shift;
  LispObj
    prev = lisp_nil,
    current;
  Boolean notify_pending_gc = false;

  if (nconses == 0) {
    xpGPR(xp, arg_z) = lisp_nil;
    return true;
  }

  update_bytes_allocated(tcr, (void *) tcr->save_allocptr);

  /*
   * On ARM64 TBI, allocptr has no low-bit fulltag.  The displacement
   * positions allocptr at base + node_size (same bias as a tagged cons
   * pointer without the high-byte tag).
   */
  if (allocate_object(xp, bytes_needed,
                      (-bytes_needed) + node_size, tcr,
                      &notify_pending_gc)) {
    LispObj raw_base = xpGPR(xp, allocptr);
    LispObj cons_tag = (LispObj)tag_cons << tag_shift;

    for (current = raw_base | cons_tag;
         nconses;
         prev = current, current += dnode_size, nconses--) {
      deref(current, 0) = prev;
      /* GC may relocate the initial element, so re-read arg_y each time. */
      deref(current, 1) = xpGPR(xp, arg_y);
    }
    xpGPR(xp, arg_z) = prev;
    xpGPR(xp, arg_y) = raw_base | cons_tag;
    /* Clean allocptr: back to dnode-aligned base */
    xpGPR(xp, allocptr) = raw_base - node_size;
    if (notify_pending_gc && !did_gc_notification_since_last_full_gc) {
      callback_for_gc_notification(xp, tcr);
    }
  } else {
    lisp_allocation_failure(xp, tcr, bytes_needed);
  }
  return true;
}


Boolean
extend_tcr_tlb(TCR *tcr, ExceptionInformation *xp, unsigned idx_regno)
{
  unsigned
    index = (unsigned)(xpGPR(xp, idx_regno)),
    old_limit = tcr->tlb_limit,
    new_limit = align_to_power_of_2(index + 1, 12),
    new_bytes = new_limit - old_limit;
  LispObj
    *old_tlb = tcr->tlb_pointer,
    *new_tlb = realloc(old_tlb, new_limit),
    *work;

  if (new_tlb == NULL) {
    return false;
  }

  work = (LispObj *)((BytePtr)new_tlb + old_limit);

  while (new_bytes) {
    *work++ = no_thread_local_binding_marker;
    new_bytes -= sizeof(LispObj);
  }
  tcr->tlb_pointer = new_tlb;
  tcr->tlb_limit = new_limit;
  return true;
}


/*
  handle_uuo: dispatch HLT-based UUOs on ARM64.

  ARM64 UUOs use the HLT instruction with a 16-bit immediate.
  The low 3 bits encode the format; the upper bits encode register
  numbers, type tags, and/or sub-codes depending on the format.
*/
Boolean
handle_uuo(ExceptionInformation *xp, siginfo_t *info, opcode the_uuo)
{
  unsigned format = HLT_UUO_FORMAT(the_uuo);
  Boolean handled = false;
  int bump = 4;
  TCR *tcr = get_tcr(true);

  fprintf(dbgout, "UUO: PC=%016lx LR=%016lx fmt=%u reg=%u info=%u insn=%08x\n",
          (unsigned long)(natural)xpPC(xp), (unsigned long)xpGPR(xp, 30),
          format, HLT_UUO_REG(the_uuo), HLT_UUO_INFO(the_uuo), the_uuo);
  fprintf(dbgout, "  nfn=%016lx fname=%016lx arg_x=%016lx arg_y=%016lx arg_z=%016lx\n",
          (unsigned long)xpGPR(xp, 10), (unsigned long)xpGPR(xp, 9),
          (unsigned long)xpGPR(xp, 13), (unsigned long)xpGPR(xp, 14),
          (unsigned long)xpGPR(xp, 15));
  fflush(dbgout);

  switch (format) {
  case hlt_code_nullary:
    {
      unsigned nullary_info = HLT_NULLARY_INFO(the_uuo);

      switch (nullary_info) {
      case 1:  /* wrong nargs */
        /* The preceding CMP set nargs; invoke Lisp error handler. */
        handled = handle_error(xp, 0, the_uuo, &bump);
        break;

      case 3:  /* debug trap */
        adjust_exception_pc(xp, bump);
        bump = 0;
        lisp_Debugger(xp, info, debug_entry_dbg, false, "Lisp Breakpoint");
        handled = true;
        break;

      case 4:  /* interrupt_now */
        tcr->interrupt_pending = 0;
        callback_for_trap(nrs_CMAIN.vcell, xp, 0, 0, NULL);
        handled = true;
        break;

      case 5:  /* suspend_now */
        handled = true;
        break;

      case 7:  /* kernel service — service code in imm0 */
        {
          int service = xpGPR(xp, imm0);
          TCR *target = (TCR *)xpGPR(xp, arg_z);

          switch (service) {
          case error_propagate_suspend:
            handled = true;
            break;
          case error_interrupt:
            xpGPR(xp, imm0) = (LispObj) raise_thread_interrupt(target);
            handled = true;
            break;
          case error_suspend:
            xpGPR(xp, imm0) = (LispObj) lisp_suspend_tcr(target);
            handled = true;
            break;
          case error_suspend_all:
            lisp_suspend_other_threads();
            handled = true;
            break;
          case error_resume:
            xpGPR(xp, imm0) = (LispObj) lisp_resume_tcr(target);
            handled = true;
            break;
          case error_resume_all:
            lisp_resume_other_threads();
            handled = true;
            break;
          case error_kill:
            xpGPR(xp, imm0) = (LispObj) kill_tcr(target);
            handled = true;
            break;
          case error_allocate_list:
            allocate_list(xp, tcr);
            handled = true;
            break;
          default:
            handled = false;
            break;
          }
        }
        break;

      default:
        handled = false;
        break;
      }
    }
    break;

  case hlt_code_unary_reg_not_lisptag:
  case hlt_code_unary_reg_not_fulltag:
  case hlt_code_unary_reg_not_subtag:
  case hlt_code_unary_reg_not_xtype:
  case hlt_code_binary:
    handled = handle_error(xp, 0, the_uuo, &bump);
    break;

  case hlt_code_unary_misc:
    {
      unsigned reg = HLT_UUO_REG(the_uuo);
      unsigned misc_info = HLT_UUO_INFO(the_uuo);

      switch (misc_info) {
      case uuo_misc_not_callable:
      case uuo_misc_no_throw_tag:
      case uuo_misc_unbound:
        handled = handle_error(xp, 0, the_uuo, &bump);
        break;
      case uuo_misc_tlb_too_small:
        if (extend_tcr_tlb(tcr, xp, reg)) {
          handled = true;
          bump = 4;
        }
        break;
      default:
        handled = false;
        break;
      }
    }
    break;

  default:
    handled = false;
    bump = 0;
  }

  if (handled && bump) {
    adjust_exception_pc(xp, bump);
  }
  return handled;
}


/*
  handle_exception: main exception dispatcher.

  On ARM64 Linux, HLT instructions generate SIGTRAP (not SIGILL
  as on ARM32).  On ARM64 Darwin, they may arrive via Mach
  exceptions mapped to SIGILL.
*/
Boolean
handle_exception(int signum, ExceptionInformation *xp, TCR *tcr,
                 siginfo_t *info, int old_valence)
{
  pc program_counter;
  opcode instruction = 0;

  if (old_valence != TCR_STATE_LISP) {
    return false;
  }

  program_counter = xpPC(xp);

  if ((signum == SIGTRAP) || (signum == SIGILL)) {
    instruction = *program_counter;
  }

  if (IS_ALLOC_TRAP(instruction)) {
    Boolean did_notify = false,
      *notify_ptr = &did_notify;
    if (did_gc_notification_since_last_full_gc) {
      notify_ptr = NULL;
    }
    return handle_alloc_trap(xp, tcr, notify_ptr);
  } else if ((signum == SIGSEGV) || (signum == SIGBUS)) {
    return handle_protection_violation(xp, info, tcr, old_valence);
  } else if (signum == SIGFPE) {
    return handle_sigfpe(xp, tcr);
  } else if ((signum == SIGTRAP) || (signum == SIGILL)) {
    if (IS_GC_TRAP(instruction)) {
      return handle_gc_trap(xp, tcr);
    } else if (IS_HLT(instruction)) {
      return handle_uuo(xp, info, instruction);
    }
  } else if (signum == SIGNAL_FOR_PROCESS_INTERRUPT) {
    tcr->interrupt_pending = 0;
    callback_for_trap(nrs_CMAIN.vcell, xp, 0, 0, NULL);
    return true;
  }

  return false;
}


/*
  ================================================================
  Chunk 5: pc_luser_xp, normalize_tcr, gc_like_from_xp and
           GC entry-point wrappers.
  ================================================================
*/

/* ----------------------------------------------------------------
   Write-barrier and swap-lr labels from arm64-spentry.s.
   ---------------------------------------------------------------- */
extern opcode
  egc_write_barrier_start,
  egc_write_barrier_end,
  egc_store_node_conditional,
  egc_store_node_conditional_test,
  egc_set_hash_key_conditional,
  egc_set_hash_key_conditional_success,
  egc_set_hash_key, egc_set_hash_key_did_store,
  egc_gvset, egc_gvset_did_store,
  egc_rplaca_did_store,
  egc_rplacd, egc_rplacd_did_store;

extern opcode
  swap_lr_lisp_frame_temp0,
  swap_lr_lisp_frame_temp0_end,
  swap_lr_lisp_frame_arg_z,
  swap_lr_lisp_frame_arg_z_end;


/* ----------------------------------------------------------------
   classify_alloc_instruction: determine where the PC is in the
   ARM64 allocation sequence.
   ---------------------------------------------------------------- */
static alloc_instruction_id
classify_alloc_instruction(ExceptionInformation *xp)
{
  pc program_counter = xpPC(xp);
  opcode instr = *program_counter;

  if (IS_SUB_FROM_ALLOCPTR(instr))
    return ID_sub_allocptr_instruction;
  if (IS_LOAD_ALLOCBASE_FROM_TCR(instr))
    return ID_load_allocbase_instruction;
  if (IS_COMPARE_ALLOCPTR(instr))
    return ID_compare_allocptr_instruction;
  if (IS_BRANCH_AROUND_ALLOC_TRAP(instr))
    return ID_branch_around_alloc_trap_instruction;
  if (IS_ALLOC_TRAP(instr))
    return ID_alloc_trap_instruction;
  if (IS_STUR_TO_ALLOCPTR(instr) ||
      IS_STR_UOFF_TO_ALLOCPTR(instr) ||
      IS_SET_ALLOCPTR_RESULT(instr) ||
      IS_CLR_ALLOCPTR_TAG(instr))
    return ID_finish_allocation;

  return ID_unrecognized_alloc_instruction;
}


/* ----------------------------------------------------------------
   restart_allocation: back up the PC to the SUB instruction that
   begins the allocation sequence so it can be re-attempted.
   ---------------------------------------------------------------- */
static void
restart_allocation(ExceptionInformation *xp)
{
  pc p = xpPC(xp);

  while (1) {
    if (IS_SUB_FROM_ALLOCPTR(*p)) {
      xpPC(xp) = p;
      return;
    }
    --p;
  }
}


/* ----------------------------------------------------------------
   update_area_active: set the active pointer of the area chain
   rooted at *aptr to value.  Walk the ->older chain to find the
   matching area, then mark all younger areas as empty (active=high).
   ---------------------------------------------------------------- */
static void
update_area_active(area **aptr, BytePtr value)
{
  area *a = *aptr;

  for (; a; a = a->older) {
    if ((a->low <= value) && (a->high >= value))
      break;
  }
  if (a == NULL) {
    Bug(NULL, "Can't find active area");
    return;
  }
  a->active = value;
  *aptr = a;

  for (a = a->younger; a; a = a->younger) {
    a->active = a->high;
  }
}


/* ----------------------------------------------------------------
   pc_luser_xp: "PC-loser fixup."  If the thread was interrupted
   in the middle of a non-atomic instruction sequence (write
   barrier, allocation, or swap-LR), finish or restart the
   sequence so that the GC sees consistent state.

   alloc_disp:
     NULL  → we're normalizing another thread for GC.
     non-NULL → we're normalizing the current thread for an
                interrupt; *alloc_disp receives the displacement
                so the interrupt handler can restart later.
   ---------------------------------------------------------------- */
void
pc_luser_xp(ExceptionInformation *xp, TCR *tcr, signed_natural *alloc_disp)
{
  pc program_counter = xpPC(xp);
  LispObj cur_allocptr = xpGPR(xp, allocptr);
  int allocptr_tag = fulltag_of(cur_allocptr);

  /* ---- Section 1: Write-barrier completion ---- */
  if ((program_counter < &egc_write_barrier_end) &&
      (program_counter >= &egc_write_barrier_start)) {
    LispObj *ea = 0, val = 0, root = 0;
    bitvector refbits = (bitvector)(lisp_global(REFBITS));
    Boolean need_check_memo = true, need_memoize_root = false;

    if (program_counter >= &egc_set_hash_key_conditional) {
      /*
       * set_hash_key_conditional: LDXR/STXR on a hash-table slot.
       * If we haven't reached the success point, the CAS either hasn't
       * been attempted yet or will be retried (exclusive monitor cleared
       * by the signal).  Just return.
       */
      if (program_counter < &egc_set_hash_key_conditional_success) {
        return;
      }
      /* CAS succeeded.  imm2 holds the ea (= arg_x + unboxed offset)
         from the CAS setup.  arg_x = root (preserved through the
         set_hash_key_conditional memoization code). */
      root = xpGPR(xp, arg_x);
      ea = (LispObj *)xpGPR(xp, imm2);
      val = xpGPR(xp, arg_z);
      xpGPR(xp, arg_z) = t_value;
      need_memoize_root = true;
    } else if (program_counter >= &egc_store_node_conditional) {
      if ((program_counter < &egc_store_node_conditional_test) ||
          ((program_counter == &egc_store_node_conditional_test) &&
           (xpGPR(xp, imm0) != 0))) {
        /* CAS not yet attempted or STXR failed → just return. */
        return;
      }
      /* imm2 holds ea (= arg_x + unboxed byte-offset) from the CAS
         setup at the top of the loop. */
      ea = (LispObj *)xpGPR(xp, imm2);
      val = xpGPR(xp, arg_z);
      xpGPR(xp, arg_z) = t_value;
    } else if (program_counter >= &egc_set_hash_key) {
      if (program_counter < &egc_set_hash_key_did_store) {
        return;
      }
      root = xpGPR(xp, arg_x);
      val = xpGPR(xp, arg_z);
      ea = (LispObj *)(root + xpGPR(xp, arg_y) + misc_data_offset);
      need_memoize_root = true;
    } else if (program_counter >= &egc_gvset) {
      if (program_counter < &egc_gvset_did_store) {
        return;
      }
      ea = (LispObj *)(xpGPR(xp, arg_x) + xpGPR(xp, arg_y) + misc_data_offset);
      val = xpGPR(xp, arg_z);
    } else if (program_counter >= &egc_rplacd) {
      if (program_counter < &egc_rplacd_did_store) {
        return;
      }
      ea = (LispObj *)untag(xpGPR(xp, arg_y));
      val = xpGPR(xp, arg_z);
    } else {
      /* egc_rplaca */
      if (program_counter < &egc_rplaca_did_store) {
        return;
      }
      ea = ((LispObj *)untag(xpGPR(xp, arg_y))) + 1;
      val = xpGPR(xp, arg_z);
    }

    if (need_check_memo) {
      natural bitnumber = area_dnode(ea, lisp_global(REF_BASE));
      if ((bitnumber < lisp_global(OLDSPACE_DNODE_COUNT)) &&
          ((LispObj)ea < val)) {
        atomic_set_bit(refbits, bitnumber);
        atomic_set_bit(global_refidx, bitnumber >> 8);
        if (need_memoize_root) {
          bitnumber = area_dnode(root, lisp_global(REF_BASE));
          atomic_set_bit(refbits, bitnumber);
          atomic_set_bit(global_refidx, bitnumber >> 8);
        }
      }
    }
    /* All write-barrier subprims return via RET, so set PC = LR. */
    xpPC(xp) = xpLR(xp);
    return;
  }

  /* ---- Section 2: Allocation fixup ---- */
  if (allocptr_tag != tag_positive_fixnum) {
    alloc_instruction_id state = classify_alloc_instruction(xp);

    if (state == ID_unrecognized_alloc_instruction) {
      Bug(xp, "Unrecognized allocation state in thread " LISP, (LispObj)tcr);
      return;
    }

    if (state == ID_finish_allocation) {
      /* Past the alloc trap — finish filling in the object. */
      if (allocptr_tag == fulltag_cons) {
        finish_allocating_cons(xp);
      } else if (is_uvector_fulltag(allocptr_tag)) {
        finish_allocating_uvector(xp);
      } else {
        Bug(xp, "What's being allocated here?");
      }
    } else {
      /* At or before the alloc trap — back up to the SUB so
         the allocation sequence restarts from scratch. */
      restart_allocation(xp);
    }
    xpGPR(xp, allocptr) = VOID_ALLOCPTR;
    xpGPR(xp, allocbase) = VOID_ALLOCPTR;
    return;
  }

  /* ---- Section 3: swap_lr_lisp_frame fixup ---- */
  {
    lisp_frame *swap_frame = NULL;
    pc base = &swap_lr_lisp_frame_temp0;

    if ((program_counter > base) &&
        (program_counter < &swap_lr_lisp_frame_temp0_end)) {
      swap_frame = (lisp_frame *)xpGPR(xp, temp0);
    } else {
      base = &swap_lr_lisp_frame_arg_z;
      if ((program_counter > base) &&
          (program_counter < &swap_lr_lisp_frame_arg_z_end)) {
        swap_frame = (lisp_frame *)xpGPR(xp, arg_z);
      }
    }
    if (swap_frame) {
      /* Complete the 3-instruction swap: ldr imm0,[frame,#savelr];
         str lr,[frame,#savelr]; mov lr,imm0.
         If we're past the first instruction, the LDR has loaded
         the old savelr into imm0.  If we're past the second, the
         STR has saved our LR. */
      if (program_counter >= base + 2) {
        /* STR already done; just finish: mov lr, imm0 */
      } else if (program_counter == base + 1) {
        /* LDR done, STR not yet done: do the store. */
        swap_frame->savelr = xpGPR(xp, Rlr);
      }
      xpGPR(xp, Rlr) = xpGPR(xp, imm0);
      xpPC(xp) = &swap_lr_lisp_frame_temp0_end;
      if (base == &swap_lr_lisp_frame_arg_z)
        xpPC(xp) = &swap_lr_lisp_frame_arg_z_end;
      return;
    }
  }
}


/* ----------------------------------------------------------------
   normalize_tcr: normalize a TCR's stack area pointers and
   allocation state so the GC can safely walk the stacks.
   ---------------------------------------------------------------- */
void
normalize_tcr(ExceptionInformation *xp, TCR *tcr, Boolean is_other_tcr)
{
  void *cur_allocptr = NULL;
  LispObj freeptr = 0;

  if (xp) {
    if (is_other_tcr) {
      pc_luser_xp(xp, tcr, NULL);
      freeptr = xpGPR(xp, allocptr);
      if (fulltag_of(freeptr) == 0) {
        cur_allocptr = (void *)ptr_from_lispobj(freeptr);
      }
    }
    /* SP is not a GPR on AArch64; use xpSP(). */
    update_area_active((area **)&tcr->cs_area, (BytePtr)xpSP(xp));
    update_area_active((area **)&tcr->vs_area,
                       (BytePtr)ptr_from_lispobj(xpGPR(xp, vsp)));
    /* ARM64 has no tsp register; use saved TCR field. */
    update_area_active((area **)&tcr->ts_area, (BytePtr)tcr->save_tsp);
  } else {
    /* In ff-call.  Get area active pointers from saved TCR fields. */
    cur_allocptr = (void *)(tcr->save_allocptr);
    update_area_active((area **)&tcr->vs_area, (BytePtr)tcr->save_vsp);
    update_area_active((area **)&tcr->ts_area, (BytePtr)tcr->save_tsp);
  }

  tcr->save_allocptr = tcr->save_allocbase = (void *)VOID_ALLOCPTR;
  if (cur_allocptr) {
    update_bytes_allocated(tcr, cur_allocptr);
    if (freeptr) {
      xpGPR(xp, allocptr) = VOID_ALLOCPTR;
      xpGPR(xp, allocbase) = VOID_ALLOCPTR;
    }
  }
}


/* ----------------------------------------------------------------
   gc_like_from_xp: suspend all other threads, normalize their
   TCRs, invoke the GC-like function, and resume.
   ---------------------------------------------------------------- */
signed_natural
gc_like_from_xp(ExceptionInformation *xp,
                signed_natural (*fun)(TCR *, signed_natural),
                signed_natural param)
{
  TCR *tcr = get_tcr(true), *other_tcr;
  int result;
  signed_natural inhibit;

  suspend_other_threads(true);
  inhibit = (signed_natural)(lisp_global(GC_INHIBIT_COUNT));
  if (inhibit != 0) {
    if (inhibit > 0) {
      lisp_global(GC_INHIBIT_COUNT) = (LispObj)(-inhibit);
    }
    resume_other_threads(true);
    gc_deferred++;
    return 0;
  }
  gc_deferred = 0;

  gc_tcr = tcr;

  xpGPR(xp, allocptr) = VOID_ALLOCPTR;
  xpGPR(xp, allocbase) = VOID_ALLOCPTR;

  normalize_tcr(xp, tcr, false);

  for (other_tcr = tcr->next; other_tcr != tcr;
       other_tcr = other_tcr->next) {
    if (other_tcr->pending_exception_context) {
      other_tcr->gc_context = other_tcr->pending_exception_context;
    } else if (other_tcr->valence == TCR_STATE_LISP) {
      other_tcr->gc_context = other_tcr->suspend_context;
    } else {
      other_tcr->gc_context = NULL;
    }
    normalize_tcr(other_tcr->gc_context, other_tcr, true);
  }

  result = fun(tcr, param);

  other_tcr = tcr;
  do {
    other_tcr->gc_context = NULL;
    other_tcr = other_tcr->next;
  } while (other_tcr != tcr);

  gc_tcr = NULL;

  resume_other_threads(true);

  return result;
}


/* ----------------------------------------------------------------
   GC entry-point wrappers.
   ---------------------------------------------------------------- */

signed_natural
gc_from_tcr(TCR *tcr, signed_natural param)
{
  area *a;
  BytePtr oldfree, newfree;
  BytePtr oldend, newend;

  a = active_dynamic_area;
  oldend = a->high;
  oldfree = a->active;
  gc(tcr, param);
  newfree = a->active;
  newend = a->high;
  return ((oldfree - newfree) + (newend - oldend));
}

signed_natural
gc_from_xp(ExceptionInformation *xp, signed_natural param)
{
  signed_natural status = gc_like_from_xp(xp, gc_from_tcr, param);

  freeGCptrs();
  return status;
}

signed_natural
purify_from_xp(ExceptionInformation *xp, signed_natural param)
{
  return gc_like_from_xp(xp, purify, param);
}

signed_natural
impurify_from_xp(ExceptionInformation *xp, signed_natural param)
{
  return gc_like_from_xp(xp, impurify, param);
}


/* ================================================================
   Chunk 6: Exception lock helpers, signal handlers, installation,
   and exception_init.
   ================================================================ */

/* ----------------------------------------------------------------
   Exception lock protocol.
   These are per-arch because ALLOW_EXCEPTIONS uses the ucontext
   signal mask, which varies by platform.
   ---------------------------------------------------------------- */

int
prepare_to_wait_for_exception_lock(TCR *tcr, ExceptionInformation *context)
{
  int old_valence = tcr->valence;

  tcr->pending_exception_context = context;
  tcr->valence = TCR_STATE_EXCEPTION_WAIT;

  ALLOW_EXCEPTIONS(context);
  return old_valence;
}

void
wait_for_exception_lock_in_handler(TCR *tcr,
                                   ExceptionInformation *context,
                                   xframe_list *xf)
{
  LOCK(lisp_global(EXCEPTION_LOCK), tcr);
  xf->curr = context;
  xf->prev = tcr->xframe;
  tcr->xframe = xf;
  tcr->pending_exception_context = NULL;
  tcr->valence = TCR_STATE_FOREIGN;
}

void
unlock_exception_lock_in_handler(TCR *tcr)
{
  tcr->pending_exception_context = tcr->xframe->curr;
  tcr->xframe = tcr->xframe->prev;
  tcr->valence = TCR_STATE_EXCEPTION_RETURN;
  UNLOCK(lisp_global(EXCEPTION_LOCK), tcr);
}


/* ----------------------------------------------------------------
   raise_pending_interrupt: if the interrupt level allows it,
   send ourselves SIGNAL_FOR_PROCESS_INTERRUPT so the thread
   re-enters the handler promptly.
   ---------------------------------------------------------------- */
void
raise_pending_interrupt(TCR *tcr)
{
  if (TCR_INTERRUPT_LEVEL(tcr) > 0) {
    pthread_kill((pthread_t)ptr_from_lispobj(tcr->osid),
                 SIGNAL_FOR_PROCESS_INTERRUPT);
  }
}


/* ----------------------------------------------------------------
   exit_signal_handler: restore TCR state after exception handling.
   On Darwin, this is empty because pseudo_sigreturn handles cleanup.
   On other platforms, unmask signals and restore old valence/frame.
   ---------------------------------------------------------------- */
#ifdef DARWIN
void
exit_signal_handler(TCR *tcr, int old_valence, natural old_last_lisp_frame)
{
}
#else
void
exit_signal_handler(TCR *tcr, int old_valence, natural old_last_lisp_frame)
{
  sigset_t mask;

  sigfillset(&mask);
  pthread_sigmask(SIG_SETMASK, &mask, NULL);
  tcr->valence = old_valence;
  tcr->pending_exception_context = NULL;
  tcr->last_lisp_frame = old_last_lisp_frame;
}
#endif


/* ----------------------------------------------------------------
   signal_handler: the main signal handler for SIGILL, SIGSEGV,
   SIGBUS.  Acquires the exception lock, calls handle_exception,
   and cleans up.

   On Darwin, this is called via Mach pseudo-signal: setup_signal_frame
   already called prepare_to_wait (set valence=EXCEPTION_WAIT), and
   passes TCR and old_valence as extra parameters in x3/x4.
   On other platforms, called as a Unix signal handler with 3 args.
   ---------------------------------------------------------------- */
void
signal_handler(int signum, siginfo_t *info, ExceptionInformation *context
#ifdef DARWIN
               , TCR *tcr, int old_valence
#endif
)
{
  xframe_list xframe_link;
#ifndef DARWIN
  TCR *tcr = get_interrupt_tcr(false);
  int old_valence;
  natural old_last_lisp_frame = tcr->last_lisp_frame;

  /* On ARM64, SP is not a GPR.  Save it via xpSP(). */
  tcr->last_lisp_frame = xpSP(context);
  old_valence = prepare_to_wait_for_exception_lock(tcr, context);
#endif

  if (tcr->flags & (1 << TCR_FLAG_BIT_PENDING_SUSPEND)) {
    CLR_TCR_FLAG(tcr, TCR_FLAG_BIT_PENDING_SUSPEND);
    pthread_kill(pthread_self(), thread_suspend_signal);
  }

  wait_for_exception_lock_in_handler(tcr, context, &xframe_link);

  if (!handle_exception(signum, context, tcr, info, old_valence)) {
    char msg[512];

    snprintf(msg, sizeof(msg),
             "Unhandled exception %d at 0x%lx, context->regs at #x%lx",
             signum, (natural)xpPC(context),
             (natural)xpGPRvector(context));
    if (lisp_Debugger(context, info, signum,
                      (old_valence != TCR_STATE_LISP), msg)) {
      SET_TCR_FLAG(tcr, TCR_FLAG_BIT_PROPAGATE_EXCEPTION);
    }
  }

  unlock_exception_lock_in_handler(tcr);
#ifndef DARWIN_USE_PSEUDO_SIGRETURN
  exit_signal_handler(tcr, old_valence, old_last_lisp_frame);
#endif
  /* raise_pending_interrupt is called by do_pseudo_sigreturn on Darwin */
#ifndef DARWIN_USE_PSEUDO_SIGRETURN
  SIGRETURN(context);
#endif
}


/* ----------------------------------------------------------------
   interrupt_handler: handles SIGNAL_FOR_PROCESS_INTERRUPT.
   If the thread can take an interrupt right now, grab the
   exception lock and call handle_exception.  Otherwise, pend it.
   ---------------------------------------------------------------- */
void
interrupt_handler(int signum, siginfo_t *info, ExceptionInformation *context)
{
  TCR *tcr = get_interrupt_tcr(false);

  if (tcr) {
    if (TCR_INTERRUPT_LEVEL(tcr) < 0) {
      tcr->interrupt_pending = 1 << fixnumshift;
    } else {
      LispObj cmain = nrs_CMAIN.vcell;

      if ((fulltag_of(cmain) == fulltag_misc) &&
          (header_subtag(header_of(cmain)) == subtag_macptr)) {
        /*
         * This thread can allegedly take an interrupt now.
         * If we're in foreign code or unwinding, defer it.
         */
        if ((tcr->valence != TCR_STATE_LISP) ||
            (tcr->unwinding != 0)) {
          tcr->interrupt_pending = 1 << fixnumshift;
        } else {
          xframe_list xframe_link;
          int old_valence;
          natural old_last_lisp_frame = tcr->last_lisp_frame;

          tcr->last_lisp_frame = xpSP(context);
          pc_luser_xp(context, tcr, NULL);
          old_valence = prepare_to_wait_for_exception_lock(tcr, context);
          wait_for_exception_lock_in_handler(tcr, context, &xframe_link);
          handle_exception(signum, context, tcr, info, old_valence);
          unlock_exception_lock_in_handler(tcr);
          exit_signal_handler(tcr, old_valence, old_last_lisp_frame);
        }
      }
    }
  }
#ifdef DARWIN
  DarwinSigReturn(context);
#endif
}


/* ----------------------------------------------------------------
   Alternate-signal-stack support (Linux only).
   On Darwin, USE_SIGALTSTACK is not defined; signals are delivered
   on the thread's main stack (and Mach exceptions may be used).
   ---------------------------------------------------------------- */

#ifdef USE_SIGALTSTACK

extern void
call_handler_on_main_stack(int, siginfo_t *, ExceptionInformation *,
                           void *, void *);

void
invoke_handler_on_main_stack(int signo, siginfo_t *info,
                             ExceptionInformation *xp,
                             void *return_address, void *handler)
{
  ExceptionInformation *xp_copy;
  siginfo_t *info_copy;
  BytePtr target_sp;

  /* Allocate copies of xp and info on the thread's main (C) stack,
     below the current SP saved in xp.  The altstack handler received
     the signal, so xpSP(xp) still points to the main stack. */
  target_sp = (BytePtr)xpSP(xp);

  target_sp -= sizeof(ucontext_t);
  target_sp = (BytePtr)((natural)target_sp & ~15);  /* 16-byte align */
  xp_copy = (ExceptionInformation *)target_sp;
  memmove(target_sp, xp, sizeof(*xp));
  xp_copy->uc_stack.ss_sp = 0;
  xp_copy->uc_stack.ss_size = 0;
  xp_copy->uc_stack.ss_flags = 0;
  xp_copy->uc_link = NULL;

  target_sp -= sizeof(siginfo_t);
  target_sp = (BytePtr)((natural)target_sp & ~15);
  info_copy = (siginfo_t *)target_sp;
  memmove(target_sp, info, sizeof(*info));

  /* call_handler_on_main_stack(signo, info, xp, new_sp, handler):
     sets SP = new_sp, then branches to handler with x0-x2 intact. */
  call_handler_on_main_stack(signo, info_copy, xp_copy,
                             target_sp, handler);
}


void
altstack_signal_handler(int signo, siginfo_t *info, ExceptionInformation *xp)
{
  TCR *tcr = get_tcr(true);

  if (signo == SIGBUS) {
    BytePtr addr = (BytePtr)xpFaultAddress(xp);
    area *a = tcr->cs_area;

    if (((BytePtr)truncate_to_power_of_2(addr, log2_page_size))
        == a->softlimit) {
      if (mmap(a->softlimit, page_size,
               PROT_READ | PROT_WRITE | PROT_EXEC,
               MAP_PRIVATE | MAP_ANON | MAP_FIXED,
               -1, 0) == a->softlimit) {
        return;
      }
    }
  } else if (signo == SIGSEGV) {
    BytePtr addr = (BytePtr)xpFaultAddress(xp);
    area *a = tcr->cs_area;

    if ((addr >= a->low) && (addr < a->softlimit)) {
      if (addr < a->hardlimit) {
        Bug(xp, "hard stack overflow");
      } else {
        UnProtectMemory(a->hardlimit, a->softlimit - a->hardlimit);
      }
    }
  }

  invoke_handler_on_main_stack(signo, info, xp,
                               __builtin_return_address(0),
                               signal_handler);
}


void
altstack_interrupt_handler(int signum, siginfo_t *info,
                           ExceptionInformation *context)
{
  invoke_handler_on_main_stack(signum, info, context,
                               __builtin_return_address(0),
                               interrupt_handler);
}

#endif /* USE_SIGALTSTACK */


/* ----------------------------------------------------------------
   install_signal_handler: register a signal handler via sigaction.
   Flags control SA_RESTART, SA_ONSTACK, and reservation.
   ---------------------------------------------------------------- */
void
install_signal_handler(int signo, void *handler, unsigned flags)
{
  struct sigaction sa;
  int err;

  sa.sa_sigaction = (void *)handler;
  sigfillset(&sa.sa_mask);
  sa.sa_flags = SA_SIGINFO;

#ifdef USE_SIGALTSTACK
  if (flags & ON_ALTSTACK)
    sa.sa_flags |= SA_ONSTACK;
#endif
  if (flags & RESTART_SYSCALLS)
    sa.sa_flags |= SA_RESTART;
  if (flags & RESERVE_FOR_LISP) {
    extern sigset_t user_signals_reserved;
    sigaddset(&user_signals_reserved, signo);
  }

  err = sigaction(signo, &sa, NULL);
  if (err) {
    perror("sigaction");
    exit(1);
  }
}


/* ----------------------------------------------------------------
   install_pmcl_exception_handlers: install all CCL signal handlers.

   ARM64 uses HLT for UUOs, which is undefined at EL0 on Linux,
   generating SIGILL.  No condition-code wrapper is needed (unlike
   ARM32) because AArch64 instructions are unconditional.
   ---------------------------------------------------------------- */
void
install_pmcl_exception_handlers()
{
  install_signal_handler(SIGILL, (void *)signal_handler,
                         RESERVE_FOR_LISP);
  install_signal_handler(SIGSEGV, (void *)ALTSTACK(signal_handler),
                         RESERVE_FOR_LISP | ON_ALTSTACK);
  install_signal_handler(SIGBUS, (void *)ALTSTACK(signal_handler),
                         RESERVE_FOR_LISP | ON_ALTSTACK);
  install_signal_handler(SIGNAL_FOR_PROCESS_INTERRUPT,
                         (void *)interrupt_handler,
                         RESERVE_FOR_LISP);
  signal(SIGPIPE, SIG_IGN);
}


/* ----------------------------------------------------------------
   setup_sigaltstack: allocate and install an alternate signal stack
   for this thread (Linux only).
   ---------------------------------------------------------------- */
#ifdef USE_SIGALTSTACK
void
setup_sigaltstack(area *a)
{
  stack_t stack;

  stack.ss_size = SIGSTKSZ * 8;
  stack.ss_flags = 0;
  stack.ss_sp = mmap(NULL, stack.ss_size,
                     PROT_READ | PROT_WRITE,
                     MAP_ANON | MAP_PRIVATE, -1, 0);
  if (sigaltstack(&stack, NULL) != 0) {
    perror("sigaltstack");
    exit(-1);
  }
}
#endif


/* ----------------------------------------------------------------
   thread_kill_handler: handle SIG_KILL_THREAD by marking the
   TCR's stack areas as empty and calling pthread_exit.
   ---------------------------------------------------------------- */
void
thread_kill_handler(int signum, siginfo_t *info, ExceptionInformation *xp)
{
  TCR *tcr = get_tcr(false);
  area *a;
  sigset_t mask;

  sigemptyset(&mask);

  if (tcr) {
    tcr->valence = TCR_STATE_FOREIGN;
    a = tcr->vs_area;
    if (a) {
      a->active = a->high;
    }
    a = tcr->cs_area;
    if (a) {
      a->active = a->high;
    }
  }

  pthread_sigmask(SIG_SETMASK, &mask, NULL);
  pthread_exit(NULL);
}

#ifdef USE_SIGALTSTACK
void
altstack_thread_kill_handler(int signo, siginfo_t *info,
                             ExceptionInformation *xp)
{
  invoke_handler_on_main_stack(signo, info, xp,
                               __builtin_return_address(0),
                               thread_kill_handler);
}
#endif


/* ----------------------------------------------------------------
   thread_signal_setup: install per-thread signal handlers for
   suspend/resume and thread kill.
   ---------------------------------------------------------------- */
void
thread_signal_setup()
{
  thread_suspend_signal = SIG_SUSPEND_THREAD;
  thread_kill_signal = SIG_KILL_THREAD;

  install_signal_handler(thread_suspend_signal,
                         (void *)suspend_resume_handler,
                         RESERVE_FOR_LISP | RESTART_SYSCALLS);
  install_signal_handler(thread_kill_signal,
                         (void *)thread_kill_handler,
                         RESERVE_FOR_LISP);
}


/* ----------------------------------------------------------------
   unprotect_all_areas: walk the protected-area list and remove
   all memory protections.  Used before GC.
   ---------------------------------------------------------------- */
void
unprotect_all_areas()
{
  protected_area_ptr p;

  for (p = AllProtectedAreas, AllProtectedAreas = NULL; p; p = p->next) {
    unprotect_area(p);
  }
}


/* ----------------------------------------------------------------
   exception_init: top-level initialization of exception handling.
   ---------------------------------------------------------------- */
void
exception_init()
{
  install_pmcl_exception_handlers();
}

#ifdef DARWIN

/* ================================================================
   Darwin/Mach exception handling for ARM64.
   ================================================================ */

#define LISP_EXCEPTIONS_HANDLED_MASK \
 (EXC_MASK_SOFTWARE | EXC_MASK_BAD_ACCESS | EXC_MASK_BAD_INSTRUCTION | EXC_MASK_ARITHMETIC | EXC_MASK_BREAKPOINT)

#define NUM_LISP_EXCEPTIONS_HANDLED 5

typedef struct {
  int foreign_exception_port_count;
  exception_mask_t         masks[NUM_LISP_EXCEPTIONS_HANDLED];
  mach_port_t              ports[NUM_LISP_EXCEPTIONS_HANDLED];
  exception_behavior_t behaviors[NUM_LISP_EXCEPTIONS_HANDLED];
  thread_state_flavor_t  flavors[NUM_LISP_EXCEPTIONS_HANDLED];
} MACH_foreign_exception_state;

#define TCR_FROM_EXCEPTION_PORT(p) find_tcr_from_exception_port(p)
#define TCR_TO_EXCEPTION_PORT(t) (mach_port_name_t)((natural)(((TCR *)t)->io_datum))

#define C_STK_ALIGN 16
#define TRUNC_DOWN(a,b,c)  (((((natural)a)-(b))/(c)) * (c))

#define DARWIN_EXCEPTION_HANDLER signal_handler

void
fatal_mach_error(char *format, ...)
{
  va_list args;
  char s[512];

  va_start(args, format);
  vsnprintf(s, sizeof(s), format, args);
  va_end(args);

  Fatal("Mach error", s);
}

#define MACH_CHECK_ERROR(context,x) if (x != KERN_SUCCESS) {fatal_mach_error("Mach error while %s : %d", context, x);}


TCR *
find_tcr_from_exception_port(mach_port_t port)
{
  mach_port_context_t context = 0;
  kern_return_t kret;

  kret = mach_port_get_context(mach_task_self(), port, &context);
  MACH_CHECK_ERROR("finding TCR from exception port", kret);
  return (TCR *)(natural)context;
}

void
associate_tcr_with_exception_port(mach_port_t port, TCR *tcr)
{
  kern_return_t kret;

  kret = mach_port_set_context(mach_task_self(),
                               port, (mach_vm_address_t)tcr);
  MACH_CHECK_ERROR("associating TCR with exception port", kret);
}

void
disassociate_tcr_from_exception_port(mach_port_t port)
{
  kern_return_t kret;

  kret = mach_port_set_context(mach_task_self(), port, 0);
  MACH_CHECK_ERROR("disassociating TCR with exception port", kret);
}


LispObj *
find_foreign_rsp(LispObj rsp, area *foreign_area, TCR *tcr)
{
  if (((BytePtr)rsp < foreign_area->low) ||
      ((BytePtr)rsp > foreign_area->high)) {
    rsp = (LispObj)(foreign_area->active);
  }
  return (LispObj *) ((rsp & ~15));
}


void
restore_mach_thread_state(mach_port_t thread, ExceptionInformation *pseudosigcontext, native_thread_state_t *ts)
{
  kern_return_t kret;
  MCONTEXT_T mc = UC_MCONTEXT(pseudosigcontext);

  /* Set the thread's float/NEON state from the pseudosigcontext */
  kret = thread_set_state(thread,
                          NATIVE_FLOAT_STATE_FLAVOR,
                          (thread_state_t)&(mc->__ns),
                          NATIVE_FLOAT_STATE_COUNT);
  MACH_CHECK_ERROR("setting thread FP state", kret);
  *ts = mc->__ss;
}


kern_return_t
do_pseudo_sigreturn(mach_port_t thread, TCR *tcr, native_thread_state_t *out)
{
  ExceptionInformation *xp;

  xp = tcr->pending_exception_context;
  if (xp) {
    MCONTEXT_T mc = UC_MCONTEXT(xp);
    fprintf(dbgout, "DBG pseudo_sigreturn: restoring pc=%016lx sp=%016lx x15=%016lx x25=%016lx x10=%016lx\n",
            (unsigned long)mc->__ss.__pc, (unsigned long)mc->__ss.__sp,
            (unsigned long)mc->__ss.__x[15], (unsigned long)mc->__ss.__x[25],
            (unsigned long)mc->__ss.__x[10]);
    fflush(dbgout);
    tcr->pending_exception_context = NULL;
    tcr->valence = TCR_STATE_LISP;
    restore_mach_thread_state(thread, xp, out);
    raise_pending_interrupt(tcr);
  } else {
    Bug(NULL, "no xp here!\n");
  }
  return KERN_SUCCESS;
}


ExceptionInformation *
create_thread_context_frame(mach_port_t thread,
                            natural *new_stack_top,
                            siginfo_t **info_ptr,
                            TCR *tcr,
                            native_thread_state_t *ts)
{
  mach_msg_type_number_t thread_state_count;
  ExceptionInformation *pseudosigcontext;
  MCONTEXT_T mc;
  natural stackp;

  stackp = (LispObj) find_foreign_rsp(ts->__sp, tcr->cs_area, tcr);
  stackp = TRUNC_DOWN(stackp, sizeof(siginfo_t), C_STK_ALIGN);
  if (info_ptr) {
    *info_ptr = (siginfo_t *)stackp;
  }
  stackp = TRUNC_DOWN(stackp, sizeof(*pseudosigcontext), C_STK_ALIGN);
  pseudosigcontext = (ExceptionInformation *) ptr_from_lispobj(stackp);

  stackp = TRUNC_DOWN(stackp, sizeof(*mc), C_STK_ALIGN);
  mc = (MCONTEXT_T) ptr_from_lispobj(stackp);

  memmove(&(mc->__ss), ts, sizeof(*ts));

  thread_state_count = NATIVE_FLOAT_STATE_COUNT;
  thread_get_state(thread,
                   NATIVE_FLOAT_STATE_FLAVOR,
                   (thread_state_t)&(mc->__ns),
                   &thread_state_count);

  thread_state_count = NATIVE_EXCEPTION_STATE_COUNT;
  thread_get_state(thread,
                   NATIVE_EXCEPTION_STATE_FLAVOR,
                   (thread_state_t)&(mc->__es),
                   &thread_state_count);

  UC_MCONTEXT(pseudosigcontext) = mc;
  if (new_stack_top) {
    *new_stack_top = stackp;
  }
  return pseudosigcontext;
}


int
setup_signal_frame(mach_port_t thread,
                   void *handler_address,
                   int signum,
                   int code,
                   TCR *tcr,
                   native_thread_state_t *ts,
                   native_thread_state_t *new_ts)
{
  ExceptionInformation *pseudosigcontext;
  int old_valence = tcr->valence;
  natural stackp;
  siginfo_t *info;

  pseudosigcontext = create_thread_context_frame(thread, &stackp, &info, tcr, ts);
  bzero(info, sizeof(*info));
  info->si_code = code;
  info->si_addr = (void *)(UC_MCONTEXT(pseudosigcontext)->__es.__far);
  info->si_signo = signum;
  pseudosigcontext->uc_onstack = 0;
  pseudosigcontext->uc_sigmask = (sigset_t) 0;
  pseudosigcontext->uc_stack.ss_sp = 0;
  pseudosigcontext->uc_stack.ss_size = 0;
  pseudosigcontext->uc_stack.ss_flags = 0;
  pseudosigcontext->uc_link = NULL;
  pseudosigcontext->uc_mcsize = sizeof(*UC_MCONTEXT(pseudosigcontext));
  tcr->pending_exception_context = pseudosigcontext;
  tcr->valence = TCR_STATE_EXCEPTION_WAIT;

  /* Set up the new thread state to call the handler.
     ARM64 passes arguments in x0-x4, return address in lr, entry in pc. */
  *new_ts = *ts;
  new_ts->__pc = (natural) handler_address;
  new_ts->__lr = (natural) pseudo_sigreturn;
  fprintf(dbgout, "DBG setup_signal_frame: handler=0x%lx lr(pseudo_sigreturn)=0x%lx signum=%d sp=0x%lx\n",
          (unsigned long)new_ts->__pc, (unsigned long)new_ts->__lr, signum, (unsigned long)stackp);
  fflush(dbgout);
  new_ts->__x[0] = signum;
  new_ts->__x[1] = (natural) info;
  new_ts->__x[2] = (natural) pseudosigcontext;
  new_ts->__x[3] = (natural) tcr;
  new_ts->__x[4] = (natural) old_valence;
  new_ts->__sp = stackp;

  return 0;
}


kern_return_t
catch_mach_exception_raise(mach_port_t exception_port,
                           mach_port_t thread,
                           mach_port_t task,
                           exception_type_t exception,
                           mach_exception_data_t code,
                           mach_msg_type_number_t code_count)
{
  abort();
  return KERN_FAILURE;
}


kern_return_t
catch_mach_exception_raise_state(mach_port_t exception_port,
                                 exception_type_t exception,
                                 mach_exception_data_t code,
                                 mach_msg_type_number_t code_count,
                                 int *flavor,
                                 thread_state_t in_state,
                                 mach_msg_type_number_t in_state_count,
                                 thread_state_t out_state,
                                 mach_msg_type_number_t *out_state_count)
{
  int64_t code0 = code[0];
  int signum = 0;
  TCR *tcr = TCR_FROM_EXCEPTION_PORT(exception_port);
  mach_port_t thread = (mach_port_t)((natural)tcr->native_thread_id);
  kern_return_t kret;

#ifdef DEBUG_MACH_EXCEPTIONS
  fprintf(dbgout, "MACH_EXC: exception=%d code0=0x%llx pc=0x%lx tcr=%p\n",
          exception, (long long)code0,
          (unsigned long)((native_thread_state_t *)in_state)->__pc, tcr);
#endif

  native_thread_state_t
    *ts = (native_thread_state_t *)in_state,
    *out_ts = (native_thread_state_t *)out_state;

  if (tcr->flags & (1<<TCR_FLAG_BIT_PENDING_EXCEPTION)) {
    CLR_TCR_FLAG(tcr, TCR_FLAG_BIT_PENDING_EXCEPTION);
  }

  /* Check for pseudo-sigreturn: HLT generates EXC_BAD_INSTRUCTION on ARM64.
     When signal_handler returns, lr = pseudo_sigreturn, the HLT executes,
     and we get EXC_BAD_INSTRUCTION with PC at pseudo_sigreturn. */
  {
    static int dbg_exc_count = 0;
    static int initfn_dumped = 0;
    if (dbg_exc_count < 50) {
      dbg_exc_count++;
      fprintf(dbgout, "MACH[%d]: exc=%d code0=%lld pc=0x%lx lr=0x%lx vsp=0x%lx rnil=0x%lx rt=0x%lx fp=0x%lx catch_top=0x%lx",
              dbg_exc_count, exception, (long long)code0,
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__x[25],
              (unsigned long)ts->__x[6], (unsigned long)ts->__x[7],
              (unsigned long)ts->__fp,
              (unsigned long)(natural)tcr->catch_top);
      if (exception == EXC_BAD_ACCESS) {
        fprintf(dbgout, " addr=0x%llx x0=0x%lx x9=0x%lx x10=0x%lx x15=0x%lx sp=0x%lx",
                (long long)code[1],
                (unsigned long)ts->__x[0], (unsigned long)ts->__x[9],
                (unsigned long)ts->__x[10], (unsigned long)ts->__x[15],
                (unsigned long)ts->__sp);
        /* Dump function object slots when we crash with KERN_INVALID_ADDRESS */
        if (code0 == KERN_INVALID_ADDRESS) {
          natural nfn_tagged = ts->__x[10];
          natural nfn_raw = nfn_tagged & 0x00FFFFFFFFFFFFFF;
          fprintf(dbgout, "\n  nfn=0x%lx raw=0x%lx", (unsigned long)nfn_tagged, (unsigned long)nfn_raw);
          /* Try to read function's slots */
          if (nfn_raw > 0x100000000 && nfn_raw < 0x400000000000) {
            LispObj *fn = (LispObj *)nfn_raw;
            natural hdr = *(fn - 1);
            int nslots = hdr & 0x00FFFFFFFFFFFFFF;
            fprintf(dbgout, " hdr=0x%lx nslots=%d", (unsigned long)hdr, nslots);
            int i;
            for (i = 0; i < nslots && i < 10; i++) {
              fprintf(dbgout, "\n  slot[%d]=0x%lx", i, (unsigned long)fn[i]);
            }
            /* For slot[2], if it looks like a symbol, try to read its value cell */
            if (nslots > 2) {
              LispObj sym_tagged = fn[2];
              natural sym_raw = sym_tagged & 0x00FFFFFFFFFFFFFF;
              if (sym_raw > 0x100000000 && sym_raw < 0x400000000000) {
                LispObj *sym = (LispObj *)sym_raw;
                fprintf(dbgout, "\n  sym[2] vcell=0x%lx tlbidx=0x%lx pname=0x%lx",
                        (unsigned long)sym[1], (unsigned long)sym[6], (unsigned long)sym[3]);
              }
            }
          }
          /* Dump code around crash PC for KERN_INVALID_ADDRESS in lisp code */
          {
            natural pc_raw = ts->__pc & 0x00FFFFFFFFFFFFFF;
            if (pc_raw > 0x200000000ULL && pc_raw < 0x400000000000ULL) {
              opcode *pc_code = (opcode *)(pc_raw - 32);  /* 8 instrs before */
              int ci;
              fprintf(dbgout, "\n  code dump around crash pc=0x%lx:\n", (unsigned long)pc_raw);
              for (ci = 0; ci < 24; ci++) {
                char marker = ((ci == 8) ? '>' : ' ');
                fprintf(dbgout, "   %c[%+3d] 0x%lx: %08x\n", marker, (ci-8)*4, (unsigned long)(pc_raw + (ci-8)*4), pc_code[ci]);
              }
            }
            /* Also dump lisp frame contents from SP and walk frame chain */
            {
              natural sp = ts->__sp;
              if (sp > 0x100000000ULL && sp < 0x800000000000ULL) {
                LispObj *frame = (LispObj *)sp;
                fprintf(dbgout, "  lisp frame at sp=0x%lx:\n", (unsigned long)sp);
                fprintf(dbgout, "    [0] savevsp = 0x%lx\n", (unsigned long)frame[0]);
                fprintf(dbgout, "    [1] savelr  = 0x%lx\n", (unsigned long)frame[1]);
                fprintf(dbgout, "    [2] savefn  = 0x%lx\n", (unsigned long)frame[2]);
                fprintf(dbgout, "    [3] savefp  = 0x%lx\n", (unsigned long)frame[3]);
                /* Walk frame chain via savefp (x29 = __fp) */
                natural fp = ts->__fp;
                int fi;
                for (fi = 0; fi < 5 && fp > 0x100000000ULL && fp < 0x800000000000ULL; fi++) {
                  LispObj *fr = (LispObj *)fp;
                  fprintf(dbgout, "  frame[%d] at fp=0x%lx: savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                          fi, (unsigned long)fp, (unsigned long)fr[0], (unsigned long)fr[1],
                          (unsigned long)fr[2], (unsigned long)fr[3]);
                  fp = (natural)fr[3]; /* follow savefp chain */
                }
              }
            }
            fflush(dbgout);
            /* Dump vstack contents */
            {
              natural dbg_vsp = ts->__x[25];
              if (dbg_vsp > 0x100000000ULL && dbg_vsp < 0x800000000000ULL) {
                LispObj *vs = (LispObj *)dbg_vsp;
                int vi;
                fprintf(dbgout, "  vstack at vsp=0x%lx:\n", (unsigned long)dbg_vsp);
                for (vi = 0; vi < 12; vi++) {
                  fprintf(dbgout, "    [vsp+%d] = 0x%lx\n", vi*8, (unsigned long)vs[vi]);
                }
                fflush(dbgout);
              }
            }
            /* Dump LR code context too */
            {
              natural lr_raw = ts->__lr & 0x00FFFFFFFFFFFFFF;
              if (lr_raw > 0x200000000ULL && lr_raw < 0x400000000000ULL) {
                opcode *lr_code = (opcode *)(lr_raw - 16);
                int ci;
                fprintf(dbgout, "  code around lr=0x%lx:\n", (unsigned long)lr_raw);
                for (ci = 0; ci < 12; ci++) {
                  char marker = ((ci == 4) ? '>' : ' ');
                  fprintf(dbgout, "   %c[%+3d] 0x%lx: %08x\n", marker, (ci-4)*4, (unsigned long)(lr_raw + (ci-4)*4), lr_code[ci]);
                }
              }
            }
          }
        }
      }
      fprintf(dbgout, "\n");
      /* One-time dump of init function code around alloc trap */
      if (!initfn_dumped && exception == EXC_BAD_INSTRUCTION && ts->__pc > 0x200000000000ULL) {
        initfn_dumped = 1;
        opcode *code_start = (opcode *)((ts->__pc & 0x00FFFFFFFFFFFFFF) - 0x10);
        int ci;
        fprintf(dbgout, "  initfn code dump (24 instrs from pc-0x10):\n");
        for (ci = 0; ci < 24; ci++) {
          fprintf(dbgout, "    [%+3d] %08x\n", (ci-4)*4, code_start[ci]);
        }
        fflush(dbgout);
      }
      fflush(dbgout);
    }
  }
  /* Debug: fatal trap for nthrow with NULL catch_top (HLT #0xFFFC) */
  if (exception == EXC_BAD_INSTRUCTION) {
    natural pc = ts->__pc;
    opcode insn = *(opcode *)pc;
    unsigned imm16 = (insn >> 5) & 0xFFFF;
    if (imm16 == 0xFFFC) {
      fprintf(dbgout, "FATAL: nthrow with NULL catch_top pc=0x%lx lr=0x%lx temp2(x10)=0x%lx sp=0x%lx\n",
              (unsigned long)pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__x[10], (unsigned long)ts->__sp);
      fflush(dbgout);
      _exit(1);
    }
  }
  if ((exception == EXC_BAD_INSTRUCTION) &&
      ((natural)(ts->__pc) == (natural)pseudo_sigreturn)) {
    kret = do_pseudo_sigreturn(thread, tcr, out_ts);
  } else if (tcr->flags & (1<<TCR_FLAG_BIT_PROPAGATE_EXCEPTION)) {
    CLR_TCR_FLAG(tcr, TCR_FLAG_BIT_PROPAGATE_EXCEPTION);
    kret = 17;
  } else if ((exception == EXC_BAD_ACCESS) && (code0 == KERN_PROTECTION_FAILURE)) {
    /* W^X page toggle: handle protection faults directly in the Mach
       exception handler without going through the signal machinery.
       code[1] is the fault address on ARM64 macOS. */
    natural fault_addr = (natural)code[1] & 0x00FFFFFFFFFFFFFF;  /* strip TBI tag */
    area *a = active_dynamic_area;
    BytePtr heap_start = (BytePtr)(natural)lisp_global(HEAP_START);
    Boolean in_heap = (a && heap_start &&
                       (BytePtr)fault_addr >= heap_start &&
                       (BytePtr)fault_addr < a->high);
    Boolean in_static = ((BytePtr)fault_addr >= static_space_start &&
                         (BytePtr)fault_addr < static_space_limit);
    Boolean in_readonly = (readonly_area &&
                           (BytePtr)fault_addr >= (BytePtr)readonly_area->low &&
                           (BytePtr)fault_addr < (BytePtr)readonly_area->active);

    /* W^X debug logging removed — handler working correctly */
    if (in_heap || in_static || in_readonly) {
      natural page_start = truncate_to_power_of_2(fault_addr, log2_page_size);

      /* Determine if this is an instruction fetch (exec fault) or data write.
         For Mach exceptions, EXC_BAD_ACCESS with KERN_PROTECTION_FAILURE:
         Check if PC is at the fault address (exec fault) or elsewhere (data fault). */
      if ((natural)ts->__pc >= page_start &&
          (natural)ts->__pc < page_start + page_size) {
        /* PC is on the faulting page: instruction fetch fault.
           Page is RW, needs RX for code execution. */
        sys_icache_invalidate((void *)page_start, page_size);
        mprotect((void *)page_start, page_size, PROT_READ | PROT_EXEC);
      } else {
        /* Data write fault: page is RX, needs RW for data write. */
        mprotect((void *)page_start, page_size, PROT_READ | PROT_WRITE);
      }
      /* Copy input state to output state to resume the thread */
      *out_ts = *ts;
      kret = KERN_SUCCESS;
    } else {
      /* Protection fault outside heap (e.g. vstack guard) — dispatch as SIGBUS */
      signum = SIGBUS;
      if (tcr->valence != TCR_STATE_LISP) {
        fprintf(dbgout, "FATAL: protection fault while in exception handler "
                "(valence=%d, addr=0x%llx, pc=0x%lx)\n",
                tcr->valence, (long long)code[1], (unsigned long)ts->__pc);
        fflush(dbgout);
        _exit(1);
      }
      kret = setup_signal_frame(thread,
                                (void *)DARWIN_EXCEPTION_HANDLER,
                                signum,
                                code0,
                                tcr,
                                ts,
                                out_ts);
      goto done;
    }
    if (!signum) goto done;
  } else if ((exception == EXC_BAD_ACCESS) && (code0 == KERN_INVALID_ADDRESS)) {
    /* Check if this is an ff-call to nil/tagged address.
       SPeabi_ff_call sets valence=FOREIGN before blr x16.
       If x16 was nil (tagged), we get KERN_INVALID_ADDRESS. */
    natural faulting_pc = (natural)ts->__pc;
    natural return_lr = (natural)ts->__lr;
    if ((faulting_pc >> 56) != 0) {
      /* PC has TBI tag — this was a branch to a tagged lisp value.
         Check if instruction at lr-4 is 'blr x16' (0xd63f0200) */
      unsigned int *prev_insn = (unsigned int *)(return_lr - 4);
      if (*prev_insn == 0xd63f0200) {
        static int ff_nil_count = 0;
        ff_nil_count++;
        if (ff_nil_count <= 5 || (ff_nil_count % 500) == 0) {
          fprintf(dbgout, "ff-call to nil/tagged (#%d) x16=0x%lx\n", ff_nil_count,
                  (unsigned long)ts->__x[16]);
          /* Dump SPeabi_ff_call saved state from vsp */
          natural saved_vsp = (natural)tcr->save_vsp;
          if (saved_vsp > 0x100000000LL && saved_vsp < 0x800000000000LL) {
            LispObj *vsp_data = (LispObj *)saved_vsp;
            fprintf(dbgout, "  save_vsp=0x%lx: last_lisp_frame=0x%lx arg_x=0x%lx temp0=0x%lx temp1=0x%lx nfn=0x%lx saved_lr=0x%lx\n",
                    (unsigned long)saved_vsp,
                    (unsigned long)vsp_data[0], (unsigned long)vsp_data[1],
                    (unsigned long)vsp_data[2], (unsigned long)vsp_data[3],
                    (unsigned long)vsp_data[4], (unsigned long)vsp_data[5]);
          }
          /* Check KERNEL_IMPORTS global */
          natural kimports = (natural)lisp_global(KERNEL_IMPORTS);
          fprintf(dbgout, "  KERNEL_IMPORTS=0x%lx\n", (unsigned long)kimports);
          if (kimports > 0x100000000LL && kimports < 0x800000000000LL) {
            /* Print first few entries */
            natural *table = (natural *)kimports;
            fprintf(dbgout, "  import_table[0]=0x%lx [8]=0x%lx [31]=0x%lx\n",
                    (unsigned long)table[0], (unsigned long)table[8],
                    (unsigned long)table[31]);
          }
          fflush(dbgout);
        }
        if (ff_nil_count > 100) {
          /* Stuck in ff-call loop — pop the current lisp frame from the
             thread state's sp (NOT tcr->last_lisp_frame which may be stale).
             The lisp frame at sp was pushed by SPeabi_ff_call before blr x16. */
          natural cur_sp = ts->__sp;
          LispObj *frame = (LispObj *)cur_sp;
          fprintf(dbgout, "ff-call loop limit reached (%d) — popping frame at sp=0x%lx\n"
                  "  savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                  ff_nil_count, (unsigned long)cur_sp,
                  (unsigned long)frame[0], (unsigned long)frame[1],
                  (unsigned long)frame[2], (unsigned long)frame[3]);
          fflush(dbgout);
          *out_ts = *ts;
          /* Pop the lisp frame and return nil to the caller */
          out_ts->__x[25] = frame[0];  /* vsp = savevsp */
          out_ts->__x[10] = frame[2];  /* fn = savefn */
          out_ts->__x[15] = 0x200000200011008ULL;  /* arg_z = nil */
          out_ts->__pc = frame[1];     /* pc = savelr (return to caller) */
          out_ts->__sp = cur_sp + 32;  /* pop 32-byte lisp frame */
          out_ts->__fp = frame[3];     /* fp = savefp */
          out_ts->__x[6] = 0x200000200011008ULL;   /* rnil */
          out_ts->__x[7] = 0x200000200011018ULL;   /* rt */
          tcr->valence = TCR_STATE_LISP;
          ff_nil_count = 0;  /* reset for next function */
          kret = KERN_SUCCESS;
          goto done;
        }
        /* Skip the call: set x0=0 (return value) and resume at lr */
        *out_ts = *ts;
        out_ts->__x[0] = 0;
        out_ts->__pc = return_lr;
        kret = KERN_SUCCESS;
        goto done;
      }
    }
    /* Check for null pointer dereference (addr=0) during cold boot.
       Skip the faulting LDR instruction and set dest register to 0. */
    if ((natural)code[1] < 4096 && tcr->valence == TCR_STATE_LISP) {
      natural fault_pc = (natural)ts->__pc;
      unsigned int insn = *(unsigned int *)fault_pc;
      int dest_reg = insn & 0x1f;  /* bits 4:0 = destination register */
      static int null_deref_count = 0;
      null_deref_count++;
      if (null_deref_count <= 3 || (null_deref_count % 500) == 0)
        fprintf(dbgout, "null-deref skip: pc=0x%lx insn=0x%08x dest=x%d (#%d)\n",
                (unsigned long)fault_pc, insn, dest_reg, null_deref_count);
      if (null_deref_count > 50000) {
        fprintf(dbgout, "too many null-deref skips (%d), aborting\n", null_deref_count);
        fflush(dbgout);
        _exit(1);
      }
      *out_ts = *ts;
      out_ts->__x[dest_reg] = 0;
      out_ts->__pc = fault_pc + 4;
      kret = KERN_SUCCESS;
      goto done;
    }
    /* Not an ff-call or null-deref — dispatch as SIGBUS */
    signum = SIGBUS;
    if (tcr->valence != TCR_STATE_LISP) {
      fprintf(dbgout, "FATAL: KERN_INVALID_ADDRESS in non-lisp valence "
              "(valence=%d, pc=0x%lx, addr=0x%llx)\n",
              tcr->valence, (unsigned long)ts->__pc, (long long)code[1]);
      fflush(dbgout);
      _exit(1);
    }
    kret = setup_signal_frame(thread,
                              (void *)DARWIN_EXCEPTION_HANDLER,
                              signum,
                              code0,
                              tcr,
                              ts,
                              out_ts);
    goto done;
  } else {
    switch (exception) {
    case EXC_BAD_ACCESS:
      signum = SIGBUS;
      break;

    case EXC_BAD_INSTRUCTION:
      signum = SIGILL;
      break;

    case EXC_SOFTWARE:
      signum = SIGILL;
      break;

    case EXC_ARITHMETIC:
      signum = SIGFPE;
      break;

    case EXC_BREAKPOINT:
      /* BRK instructions generate EXC_BREAKPOINT on ARM64.
         HLT generates EXC_BAD_INSTRUCTION (handled above). */
      signum = SIGTRAP;
      break;

    default:
      break;
    }
    if (signum) {
      /* Recursion guard: if we're already in exception processing
         (valence != TCR_STATE_LISP), don't recurse into signal handler.
         This prevents infinite loops when the signal handler itself faults. */
      if (tcr->valence != TCR_STATE_LISP) {
        fprintf(dbgout, "FATAL: exception while already in exception handler "
                "(valence=%d, signum=%d, pc=0x%lx, addr=0x%llx)\n",
                tcr->valence, signum, (unsigned long)ts->__pc,
                (long long)(code_count > 1 ? code[1] : 0));
        fprintf(dbgout, "  catch_top=0x%lx rnil=0x%lx sp=0x%lx\n",
                (unsigned long)(natural)tcr->catch_top,
                (unsigned long)ts->__x[6],
                (unsigned long)ts->__sp);
        fflush(dbgout);
        _exit(1);
      }
      kret = setup_signal_frame(thread,
                                (void *)DARWIN_EXCEPTION_HANDLER,
                                signum,
                                code0,
                                tcr,
                                ts,
                                out_ts);
    } else {
      kret = 17;
    }
  }

done:
  if (kret) {
    *out_state_count = 0;
    *flavor = 0;
  } else {
    *out_state_count = NATIVE_THREAD_STATE_COUNT;
  }
  return kret;
}


kern_return_t
catch_mach_exception_raise_state_identity(mach_port_t exception_port,
                                          mach_port_t thread,
                                          mach_port_t task,
                                          exception_type_t exception,
                                          mach_exception_data_t code,
                                          mach_msg_type_number_t code_count,
                                          int *flavor,
                                          thread_state_t old_state,
                                          mach_msg_type_number_t old_count,
                                          thread_state_t new_state,
                                          mach_msg_type_number_t *new_count)
{
  abort();
  return KERN_FAILURE;
}


static mach_port_t mach_exception_thread = (mach_port_t)0;

void *
exception_handler_proc(void *arg)
{
  extern boolean_t mach_exc_server(mach_msg_header_t *, mach_msg_header_t *);
  mach_port_t p = (mach_port_t)((natural)arg);

  mach_exception_thread = pthread_mach_thread_np(pthread_self());
  /* ARM64: use 8192 buffer for large thread state messages.
     Custom mach_msg loop replaces mach_msg_server which was unreliable. */
  {
    kern_return_t kr;
    for (;;) {
      char buf[8192];
      char reply_buf[8192];
      mach_msg_header_t *msg = (mach_msg_header_t *)buf;
      mach_msg_header_t *reply = (mach_msg_header_t *)reply_buf;

      kr = mach_msg(msg, MACH_RCV_MSG | MACH_RCV_LARGE,
                    0, sizeof(buf), p,
                    MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
      if (kr != KERN_SUCCESS) {
        continue;
      }

      boolean_t handled = mach_exc_server(msg, reply);

      if (handled) {
        kr = mach_msg(reply, MACH_SEND_MSG,
                      reply->msgh_size, 0, MACH_PORT_NULL,
                      MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
      }
    }
  }
  /* Should never return. */
  abort();
}


void
mach_exception_thread_shutdown()
{
  kern_return_t kret;

  fprintf(dbgout, "terminating Mach exception thread, 'cause exit can't\n");
  kret = thread_terminate(mach_exception_thread);
  if (kret != KERN_SUCCESS) {
    fprintf(dbgout, "Couldn't terminate exception thread, kret = %d\n", kret);
  }
}


mach_port_t
mach_exception_port_set()
{
  static mach_port_t __exception_port_set = MACH_PORT_NULL;
  kern_return_t kret;
  if (__exception_port_set == MACH_PORT_NULL) {
    kret = mach_port_allocate(mach_task_self(),
                              MACH_PORT_RIGHT_PORT_SET,
                              &__exception_port_set);
    MACH_CHECK_ERROR("allocating thread exception_ports", kret);
    create_system_thread(0,
                         NULL,
                         exception_handler_proc,
                         (void *)((natural)__exception_port_set));
  }
  return __exception_port_set;
}


kern_return_t
tcr_establish_exception_port(TCR *tcr, mach_port_t thread)
{
  kern_return_t kret;
  MACH_foreign_exception_state *fxs = (MACH_foreign_exception_state *)tcr->native_thread_info;
  int i;
  unsigned n = NUM_LISP_EXCEPTIONS_HANDLED;
  mach_port_t lisp_port = TCR_TO_EXCEPTION_PORT(tcr), foreign_port;
  exception_mask_t mask = 0;

  kret = thread_swap_exception_ports(thread,
                                     LISP_EXCEPTIONS_HANDLED_MASK,
                                     lisp_port,
                                     MACH_EXCEPTION_CODES | EXCEPTION_STATE,
                                     ARM_THREAD_STATE64,
                                     fxs->masks,
                                     &n,
                                     fxs->ports,
                                     fxs->behaviors,
                                     fxs->flavors);
  if (kret == KERN_SUCCESS) {
    fxs->foreign_exception_port_count = n;
    for (i = 0; i < n; i++) {
      foreign_port = fxs->ports[i];
      if ((foreign_port != lisp_port) &&
          (foreign_port != MACH_PORT_NULL)) {
        mask |= fxs->masks[i];
      }
    }
    tcr->foreign_exception_status = (int) mask;
  }
  return kret;
}


kern_return_t
tcr_establish_lisp_exception_port(TCR *tcr)
{
  return tcr_establish_exception_port(tcr, (mach_port_t)((natural)tcr->native_thread_id));
}


kern_return_t
restore_foreign_exception_ports(TCR *tcr)
{
  exception_mask_t m = (exception_mask_t) tcr->foreign_exception_status;
  kern_return_t kret;

  if (m) {
    MACH_foreign_exception_state *fxs =
      (MACH_foreign_exception_state *) tcr->native_thread_info;
    int i, n = fxs->foreign_exception_port_count;
    exception_mask_t tm;

    for (i = 0; i < n; i++) {
      if ((tm = fxs->masks[i]) & m) {
        kret = thread_set_exception_ports((mach_port_t)((natural)tcr->native_thread_id),
                                          tm,
                                          fxs->ports[i],
                                          fxs->behaviors[i],
                                          fxs->flavors[i]);
        MACH_CHECK_ERROR("restoring thread exception ports", kret);
      }
    }
  }
  return KERN_SUCCESS;
}


kern_return_t
setup_mach_exception_handling(TCR *tcr)
{
  mach_port_t
    thread_exception_port = TCR_TO_EXCEPTION_PORT(tcr),
    task_self = mach_task_self();
  kern_return_t kret;

  kret = mach_port_insert_right(task_self,
                                thread_exception_port,
                                thread_exception_port,
                                MACH_MSG_TYPE_MAKE_SEND);
  MACH_CHECK_ERROR("adding send right to exception_port", kret);

  kret = tcr_establish_exception_port(tcr, (mach_port_t)((natural) tcr->native_thread_id));
  if (kret == KERN_SUCCESS) {
    mach_port_t exception_port_set = mach_exception_port_set();

    kret = mach_port_move_member(task_self,
                                 thread_exception_port,
                                 exception_port_set);
    MACH_CHECK_ERROR("moving exception port to port set", kret);
  }
  return kret;
}


void
darwin_exception_init(TCR *tcr)
{
  kern_return_t kret;
  MACH_foreign_exception_state *fxs =
    calloc(1, sizeof(MACH_foreign_exception_state));

  tcr->native_thread_info = (void *) fxs;

  if ((kret = setup_mach_exception_handling(tcr))
      != KERN_SUCCESS) {
    fprintf(dbgout, "Couldn't setup exception handler - error = %d\n", kret);
    terminate_lisp();
  }
}


void
darwin_exception_cleanup(TCR *tcr)
{
  mach_port_t exception_port;
  void *fxs = tcr->native_thread_info;

  if (fxs) {
    tcr->native_thread_info = NULL;
    free(fxs);
  }

  exception_port = TCR_TO_EXCEPTION_PORT(tcr);
  disassociate_tcr_from_exception_port(exception_port);
  mach_port_deallocate(mach_task_self(), exception_port);
  mach_port_destroy(mach_task_self(), exception_port);
}

#endif
