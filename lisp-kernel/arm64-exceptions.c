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

/* a distinguished UUO at a distinguished address */
extern void pseudo_sigreturn(ExceptionInformation *);
#endif


#include "threads.h"

#ifdef LINUX

void
enable_fp_exceptions()
{
}

void
disable_fp_exceptions()
{
}
#endif

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
page_size = 4096;

int
log2_page_size = 12;

TCR *gc_tcr = NULL;


/*
  On ARM64, the TCR stores bytes_consed as a split 32+32 field
  (bytes_consed_high, bytes_consed_low) rather than a single 64-bit
  bytes_allocated.  This helper updates the split counter.
*/
static inline void
add_bytes_consed(TCR *tcr, natural bytes)
{
  natural total = ((natural)tcr->bytes_consed_high << 32) | tcr->bytes_consed_low;
  total += bytes;
  tcr->bytes_consed_high = (unsigned int)(total >> 32);
  tcr->bytes_consed_low = (unsigned int)total;
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
      unsigned rt = STR_RT(instr);
      *(LispObj *)((char *)cur_allocptr + offset) = xpGPR(xp, rt);
    } else if (IS_STR_UOFF_TO_ALLOCPTR(instr)) {
      natural offset = STR_UOFF(instr);
      unsigned rt = STR_RT(instr);
      *(LispObj *)((char *)cur_allocptr + offset) = xpGPR(xp, rt);
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
      unsigned rt = STR_RT(instr);
      *(LispObj *)((char *)cur_allocptr + offset) = xpGPR(xp, rt);
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

  if (is_write_fault(xp, info)) {
    area = find_protected_area(addr);
    if (area != NULL) {
      handler = protection_handlers[area->why];
      return handler(xp, area, addr);
    } else {
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

  switch (format) {
  case hlt_code_nullary:
    {
      unsigned nullary_info = HLT_NULLARY_INFO(the_uuo);

      switch (nullary_info) {
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
   Unmask all signals so the thread can receive them again, then
   restore the old valence and last_lisp_frame.
   ---------------------------------------------------------------- */
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


/* ----------------------------------------------------------------
   signal_handler: the main signal handler for SIGILL, SIGSEGV,
   SIGBUS.  Acquires the exception lock, calls handle_exception,
   and cleans up.
   ---------------------------------------------------------------- */
void
signal_handler(int signum, siginfo_t *info, ExceptionInformation *context)
{
  xframe_list xframe_link;
  TCR *tcr = (TCR *)get_interrupt_tcr(false);
  natural old_last_lisp_frame = tcr->last_lisp_frame;
  int old_valence;

  /* On ARM64, SP is not a GPR.  Save it via xpSP(). */
  tcr->last_lisp_frame = xpSP(context);
  old_valence = prepare_to_wait_for_exception_lock(tcr, context);

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
  exit_signal_handler(tcr, old_valence, old_last_lisp_frame);
  raise_pending_interrupt(tcr);
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
