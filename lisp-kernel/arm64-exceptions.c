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

/* Bug 156: global scratch for SPgvector exit → SPgvset entry cross-check.
   These must be global (not TCR) because exception handling clobbers TCR fields. */
volatile natural bug156_saved_savefn = 0xBAD156;
volatile natural bug156_saved_x29 = 0xBAD156;

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
       The sub from allocptr is normally at [-3]:
         sub allocptr, allocptr, #size  ; [-3]
         cmp allocptr, allocbase        ; [-2]
         b.hi around                    ; [-1]
         hlt #0                         ; [0]
       But some sequences load allocbase from TCR between sub and cmp:
         sub allocptr, allocptr, #size  ; [-4]
         ldr x1, [rcontext, #save_allocbase]  ; [-3]
         cmp allocptr, x1              ; [-2]
         b.hi around                   ; [-1]
         hlt #0                        ; [0]
       Check both positions.  Misc_Alloc has an EXTRA sub $3,$3,#node_size
       before the sub allocptr,allocptr,$3, making SUB_REG at [-4]:
         sub imm2, imm2, #node_size    ; [-5]
         sub allocptr, allocptr, imm2  ; [-4]
         cmp allocptr, allocbase       ; [-3]
         b.hi around                   ; [-2]
         b around_hdr_store            ; [-1]  (optional)
         hlt #0                        ; [0]
       So check offsets -3, -4, -5. */
    int offsets[] = {-3, -4, -5};
    int i;
    {
      static int disp_dbg = 0;
      if (disp_dbg < 10) {
        disp_dbg++;
        fprintf(dbgout, "  allocptr_disp[%d]: pc=%p instr[-5..0]=", disp_dbg, program_counter);
        for (int j = -5; j <= 0; j++)
          fprintf(dbgout, " %08x", program_counter[j]);
        fprintf(dbgout, "\n");
        fflush(dbgout);
      }
    }
    for (i = 0; i < 3; i++) {
      prev_instr = program_counter[offsets[i]];

      if (IS_SUB_IMM_FROM_ALLOCPTR(prev_instr)) {
        natural imm12 = (prev_instr >> 10) & 0xFFF;
        return -((signed_natural)imm12);
      }

      if (IS_SUB_REG_FROM_ALLOCPTR(prev_instr)) {
        unsigned rm = (prev_instr >> 16) & 0x1F;
        /* Strip TBI tag from the size register — on ARM64 TBI, a tagged
           value in the size register would cause catastrophic misbehavior.
           The size should be a small positive integer (no tag). */
        natural size_val = xpGPR(xp, rm) & 0x00FFFFFFFFFFFFFFULL;
        {
          static int reg_dbg = 0;
          if (reg_dbg < 10) {
            reg_dbg++;
            fprintf(dbgout, "  SUB_REG match at [%d]: insn=0x%08x rm=x%u raw=0x%lx stripped=0x%lx\n",
                    offsets[i], prev_instr, rm, (unsigned long)xpGPR(xp, rm),
                    (unsigned long)size_val);
            fflush(dbgout);
          }
        }
        return -((signed_natural)size_val);
      }
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

  {
    static int alloc_dbg = 0;
    if (alloc_dbg < 20) {
      alloc_dbg++;
      area *da = active_dynamic_area;
      fprintf(dbgout, "alloc-trap[%d]: allocptr=0x%lx allocbase=0x%lx disp=%ld (0x%lx)\n",
              alloc_dbg, (unsigned long)cur_allocptr,
              (unsigned long)xpGPR(xp, allocbase), (long)disp, (unsigned long)disp);
      fprintf(dbgout, "  regs: x0=0x%lx x1=0x%lx x2=0x%lx x3=0x%lx x14=0x%lx x15=0x%lx\n",
              (unsigned long)xpGPR(xp, 0), (unsigned long)xpGPR(xp, 1),
              (unsigned long)xpGPR(xp, 2), (unsigned long)xpGPR(xp, 3),
              (unsigned long)xpGPR(xp, 14), (unsigned long)xpGPR(xp, 15));
      if (da) {
        fprintf(dbgout, "  dynarea: low=0x%lx active=0x%lx high=0x%lx\n",
                (unsigned long)(natural)da->low, (unsigned long)(natural)da->active,
                (unsigned long)(natural)da->high);
      } else {
        fprintf(dbgout, "  *** active_dynamic_area is NULL! ***\n");
      }
      fflush(dbgout);
    }
  }

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
    /* Bug 123 fix: strip TBI tag from addr before heap bounds check */
    natural addr_raw = (natural)addr & 0x00FFFFFFFFFFFFFFULL;
    Boolean in_heap = ((addr_raw >= dyn->low && addr_raw < dyn->high) ||
                       (addr_raw >= (natural)static_space_start &&
                        addr_raw < (natural)static_space_limit));

    if (!in_heap) {
      fprintf(dbgout, "W^X: addr=%p NOT in heap. dyn=[%p..%p) static=[%p..%p)\n",
              addr, (void*)dyn->low, (void*)dyn->high,
              (void*)(natural)static_space_start, (void*)(natural)static_space_limit);
      {
        struct area *adyn = (struct area *)((struct area *)all_areas)->succ;
        fprintf(dbgout, "  active_dyn: low=%p active=%p high=%p\n",
                (void*)adyn->low, (void*)adyn->active, (void*)adyn->high);
      }
      /* Dump code around faulting PC — extended range */
      {
        opcode *fpc = (opcode *)xpPC(xp);
        if ((natural)fpc > 0x100000000ULL) {
          int ci;
          fprintf(dbgout, "  code@pc-128:\n");
          for (ci=-32; ci<=16; ci++) {
            if (ci == 0) fprintf(dbgout, " >>>");
            fprintf(dbgout, " %08x", fpc[ci]);
            if (ci == 0) fprintf(dbgout, "<<<");
            if ((ci % 8) == 7) fprintf(dbgout, "\n");
          }
          fprintf(dbgout, "\n");
        }
      }
      /* Dump registers and vector header for diagnosis */
      {
        natural x14_raw = xpGPR(xp, 14) & 0x00FFFFFFFFFFFFFFULL;
        fprintf(dbgout, "  regs: x9=0x%lx x10=0x%lx x11=0x%lx x14=0x%lx x15=0x%lx x25=0x%lx\n",
                (unsigned long)xpGPR(xp, 9), (unsigned long)xpGPR(xp, 10),
                (unsigned long)xpGPR(xp, 11), (unsigned long)xpGPR(xp, 14),
                (unsigned long)xpGPR(xp, 15), (unsigned long)xpGPR(xp, 25));
        /* Dump hash vector overhead slots from x9 (the vector base in %hash-probe) */
        {
          natural x9_raw = xpGPR(xp, 9) & 0x00FFFFFFFFFFFFFFULL;
          /* Check if x9 points to somewhere in the full heap (including tenured) */
          natural heap_start = 0x302000000000ULL;  /* known dynamic area base */
          natural heap_end = (natural)dyn->high;
          if (x9_raw >= heap_start && x9_raw < heap_end) {
            LispObj *vec = (LispObj *)x9_raw;
            LispObj hdr = ((LispObj *)(x9_raw - 8))[0];
            int vi;
            fprintf(dbgout, "  hash-vector@0x%lx hdr=0x%lx (subtag=0x%lx count=%lu):\n",
                    (unsigned long)x9_raw, (unsigned long)hdr,
                    (unsigned long)(hdr >> 56),
                    (unsigned long)(hdr & 0x00FFFFFFFFFFFFFFULL));
            fprintf(dbgout, "  overhead slots [0..13]:");
            for (vi = 0; vi < 14; vi++)
              fprintf(dbgout, " [%d]=0x%lx", vi, (unsigned long)vec[vi]);
            fprintf(dbgout, "\n");
            fprintf(dbgout, "  entries(slot12)=%ld size-recip(slot13)=0x%lx\n",
                    (long)vec[12], (unsigned long)vec[13]);
          } else {
            fprintf(dbgout, "  x9_raw=0x%lx NOT in heap [0x%lx..0x%lx)\n",
                    (unsigned long)x9_raw, (unsigned long)heap_start, (unsigned long)heap_end);
          }
        }
        /* Dump stack slots around vsp for context */
        {
          LispObj *vsp_ptr = (LispObj *)xpGPR(xp, 25);
          int si;
          fprintf(dbgout, "  vsp dump:");
          for (si=0; si<16; si++)
            fprintf(dbgout, " [%d]=0x%lx", si, (unsigned long)vsp_ptr[si]);
          fprintf(dbgout, "\n");
        }
      }
    }

    if (in_heap) {
      natural page_start = truncate_to_power_of_2(addr_raw, log2_page_size);

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
    if ((natural)addr == 0xFFFFFFFFFFFFFFF8ULL) {
      fprintf(dbgout, "  FAULT@-8: pc=0x%lx lr=0x%lx sp=0x%lx fp=0x%lx\n"
              "  x6=0x%lx x7=0x%lx x9=0x%lx x10=0x%lx x15=0x%lx x25=0x%lx\n",
              (unsigned long)(natural)xpPC(xp), (unsigned long)xpGPR(xp, 30),
              (unsigned long)xpSP(xp), (unsigned long)xpFP(xp),
              (unsigned long)xpGPR(xp, 6), (unsigned long)xpGPR(xp, 7),
              (unsigned long)xpGPR(xp, 9), (unsigned long)xpGPR(xp, 10),
              (unsigned long)xpGPR(xp, 15), (unsigned long)xpGPR(xp, 25));
      /* Dump instruction at faulting PC */
      pc faulting_pc = xpPC(xp);
      if ((natural)faulting_pc > 0x100000000ULL) {
        opcode *insns = (opcode *)faulting_pc;
        fprintf(dbgout, "  insns: [%+4d] %08x [%+4d] %08x [%+4d] %08x [%+4d] %08x\n",
                -4, insns[-1], 0, insns[0], 4, insns[1], 8, insns[2]);
      }
      fflush(dbgout);
    }
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
  /* Try to print the symbol name from x9 (fname) and its fcell */
  {
    LispObj fname_tagged = xpGPR(xp, 9);
    natural fname_raw = fname_tagged & 0x00FFFFFFFFFFFFFF;
    fprintf(dbgout, "  fname: tagged=0x%lx raw=0x%lx\n",
            (unsigned long)fname_tagged, (unsigned long)fname_raw);
    if (fname_raw > 0x100000000 && fname_raw < 0x400000000000) {
      /* Dump raw 64-bit words at the fname address */
      LispObj *sym = (LispObj *)fname_raw;
      fprintf(dbgout, "  fname raw data: [-1]=%016lx [0]=%016lx [1]=%016lx [2]=%016lx [3]=%016lx [4]=%016lx [5]=%016lx [6]=%016lx\n",
              (unsigned long)sym[-1], (unsigned long)sym[0], (unsigned long)sym[1],
              (unsigned long)sym[2], (unsigned long)sym[3], (unsigned long)sym[4],
              (unsigned long)sym[5], (unsigned long)sym[6]);
      LispObj pname_tagged = sym[0]; /* symbol.pname */
      LispObj vcell = sym[1]; /* symbol.vcell */
      LispObj fcell = sym[2]; /* symbol.fcell */
      natural pname_raw = pname_tagged & 0x00FFFFFFFFFFFFFF;
      fprintf(dbgout, "  pname: tagged=0x%lx raw=0x%lx\n",
              (unsigned long)pname_tagged, (unsigned long)pname_raw);
      if (pname_raw > 0x100000000 && pname_raw < 0x400000000000) {
        LispObj pname_hdr = ((LispObj *)pname_raw)[-1];
        natural pname_len = pname_hdr & 0x00FFFFFFFFFFFFFF;
        char *pname_data = (char *)pname_raw;
        fprintf(dbgout, "  pname hdr=0x%lx len=%lu\n",
                (unsigned long)pname_hdr, (unsigned long)pname_len);
        if (pname_len > 0 && pname_len < 256) {
          unsigned char pname_subtag = (pname_hdr >> 56) & 0xFF;
          int char_size = (pname_subtag & 0x7F) == 7 ? 4 : 1;
          int pi;
          fprintf(dbgout, "  fname symbol name(%d-byte chars): \"", char_size);
          for (pi = 0; pi < (int)pname_len; pi++)
            fprintf(dbgout, "%c", pname_data[pi * char_size]);
          fprintf(dbgout, "\"\n");
        }
      } else {
        fprintf(dbgout, "  pname raw out of range\n");
      }
    }
  }
  /* Bug 136: Print type specifier from arg_z (may be symbol or cons) */
  {
    LispObj az = xpGPR(xp, 15);
    unsigned az_tag = (unsigned)(az >> 56);
    natural az_raw = az & 0x00FFFFFFFFFFFFFF;
    /* Follow cons cells to find the symbol name */
    LispObj type_sym = 0;
    if (az_tag == 0x63) {
      type_sym = az;  /* arg_z is directly a symbol */
    } else if (az_tag == 0x03 && az_raw > 0x100000000LL && az_raw < 0x400000000000LL) {
      /* arg_z is a cons — CAR might be the type symbol */
      LispObj car = ((LispObj *)az_raw)[0];
      unsigned car_tag = (unsigned)(car >> 56);
      if (car_tag == 0x63) type_sym = car;
      fprintf(dbgout, "  type-spec cons: car=0x%lx cdr=0x%lx\n",
              (unsigned long)((LispObj *)az_raw)[0],
              (unsigned long)((LispObj *)az_raw)[1]);
    }
    if (type_sym) {
      natural sym_raw = type_sym & 0x00FFFFFFFFFFFFFF;
      if (sym_raw > 0x100000000LL && sym_raw < 0x400000000000LL) {
        LispObj pname = ((LispObj *)sym_raw)[0];
        natural pname_raw = pname & 0x00FFFFFFFFFFFFFF;
        if (pname_raw > 0x100000000LL && pname_raw < 0x400000000000LL) {
          LispObj pname_hdr = *((LispObj *)pname_raw - 1);
          natural pname_len = pname_hdr & 0x00FFFFFFFFFFFFFF;
          unsigned char *pname_data = (unsigned char *)pname_raw;
          if (pname_len > 0 && pname_len < 256) {
            unsigned char pname_subtag = (pname_hdr >> 56) & 0xFF;
            int char_size = (pname_subtag & 0x7F) == 7 ? 4 : 1;
            int pi;
            fprintf(dbgout, "  type-spec symbol name(%d): \"", char_size);
            for (pi = 0; pi < (int)pname_len; pi++)
              fprintf(dbgout, "%c", pname_data[pi * char_size]);
            fprintf(dbgout, "\"\n");
          }
        }
      }
    }
    fprintf(dbgout, "  arg_y(object) = 0x%lx (tag=0x%02x)\n",
            (unsigned long)xpGPR(xp, 14), (unsigned)(xpGPR(xp, 14) >> 56));
  }
  /* MV protocol diagnostic: dump ret1valaddr and frame chain savelr values */
  {
      extern void ret1valn(void);
      LispObj ret1val_global = lisp_global(RET1VALN);
      fprintf(dbgout, "  MV-DIAG: ret1valaddr global = %016lx, &ret1valn = %016lx %s\n",
              (unsigned long)ret1val_global, (unsigned long)&ret1valn,
              (ret1val_global == (LispObj)&ret1valn) ? "MATCH" : "MISMATCH!");
      fprintf(dbgout, "  MV-DIAG: sp(xpSP)=%016lx fp(xpFP)=%016lx\n",
              (unsigned long)xpSP(xp), (unsigned long)xpFP(xp));
      /* Walk stack frames to show savelr values */
      LispObj *fp = (LispObj *)xpFP(xp);
      for (int fi = 0; fi < 8 && (natural)fp > 0x100000000LL && (natural)fp < 0x800000000000LL; fi++) {
        LispObj savevsp = fp[0];
        LispObj savelr  = fp[1];
        LispObj savefn  = fp[2];
        LispObj savefp  = fp[3];
        fprintf(dbgout, "  MV-DIAG frame[%d] @%016lx: savelr=%016lx %s savefn=%016lx\n",
                fi, (unsigned long)fp, (unsigned long)savelr,
                (savelr == ret1val_global) ? "==RET1VAL" : "",
                (unsigned long)savefn);
        fp = (LispObj *)(natural)savefp;
      }
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
          for (si = 0; si < (int)fn_nslots && si < 24; si++) {
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
      /* On ARM64 (fixnumshift=0), binding_idx IS a byte offset (l0-symbol increments by 8).
         Bug 124 fix: removed extra lsl #3 from spentry/symbol.lisp that double-scaled. */
      natural byte_offset = (natural)binding_idx;
      fprintf(dbgout, "  binding_idx=%ld (=byte_offset) tlb_limit=%lu\n",
              (long)binding_idx, (unsigned long)tcr->tlb_limit);
      if (byte_offset < (natural)tcr->tlb_limit) {
        LispObj tlb_val = *(LispObj *)((char *)tcr->tlb_pointer + byte_offset);
        fprintf(dbgout, "  TLB@[%lu]=%016lx (ntlb=%016lx)\n",
                (unsigned long)byte_offset, (unsigned long)tlb_val,
                (unsigned long)no_thread_local_binding_marker);
        if (tlb_val != no_thread_local_binding_marker) {
          pkglist = tlb_val;
        }
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
      natural pkg_byte_off = (natural)pkg_bidx;  /* already a byte offset */
      if (pkg_byte_off < (natural)tcr->tlb_limit) {
        LispObj pv = *(LispObj *)((char *)tcr->tlb_pointer + pkg_byte_off);
        fprintf(dbgout, "  *package* TLB@[%lu]=%016lx\n",
                (unsigned long)pkg_byte_off, (unsigned long)pv);
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
    LispObj arg_y_val = xpGPR(xp, 14);
    LispObj arg_z_val = xpGPR(xp, 15);
    {
      static int ubound_dbg = 0;
      if (ubound_dbg < 5) {
        fprintf(dbgout, "  errdisp=unbound: arg_y(x14)=%016lx arg_z(x15)=%016lx arg1=%u arg2=0x%x nargs(x5)=%lu\n",
                (unsigned long)arg_y_val, (unsigned long)arg_z_val,
                arg1, arg2, (unsigned long)xpGPR(xp, 5));
        ubound_dbg++;
      }
    }
    /* Dump XBADKEYS diagnostics */
    if (arg_y_val == 0x99) { /* $XBADKEYS = 153 */
      fprintf(dbgout, "  $XBADKEYS: arg_z (bad keyword list) = %016lx\n",
              (unsigned long)arg_z_val);
      /* Walk the consed list of bad keyword pairs */
      LispObj bl = arg_z_val;
      int bi = 0;
      while (fulltag_of(bl) == fulltag_cons && bi < 20) {
        LispObj key = car(bl);
        fprintf(dbgout, "    badkey[%d] = %016lx (tag=0x%02lx)", bi, (unsigned long)key, (unsigned long)(key >> 56));
        /* If it's a symbol (tag 0x63), try to print its name */
        natural key_raw = key & 0x00FFFFFFFFFFFFFF;
        if ((key >> 56) == 0x63 && key_raw > 0x100000000LL && key_raw < 0x400000000000LL) {
          LispObj pn = ((LispObj *)key_raw)[0]; /* pname at slot 0 (slot 1 from tagged) */
          natural pn_raw = pn & 0x00FFFFFFFFFFFFFF;
          if (pn_raw > 0x100000000LL && pn_raw < 0x400000000000LL) {
            LispObj pn_hdr = ((LispObj *)pn_raw)[-1];
            natural pn_len = pn_hdr & 0x00FFFFFFFFFFFFFF;
            if (pn_len > 0 && pn_len < 256) {
              int cs = ((pn_hdr >> 56) & 0x7F) == 7 ? 4 : 1;
              fprintf(dbgout, " \"");
              for (int ci = 0; ci < (int)pn_len; ci++)
                fprintf(dbgout, "%c", ((char *)pn_raw)[ci * cs]);
              fprintf(dbgout, "\"");
            }
          }
        }
        fprintf(dbgout, "\n");
        bl = cdr(bl);
        bi++;
      }
      /* Also dump the caller's fn constants to see the keywords vector */
      {
        LispObj *frame = (LispObj *)xpFP(xp);
        LispObj savefn = frame[2];
        natural fn_raw = savefn & 0x00FFFFFFFFFFFFFF;
        if (fn_raw > 0x100000000LL && fn_raw < 0x400000000000LL) {
          LispObj fn_hdr = ((LispObj *)fn_raw)[-1];
          natural fn_nslots = fn_hdr & 0x00FFFFFFFFFFFFFF;
          fprintf(dbgout, "  caller fn=%016lx hdr=%016lx nslots=%lu\n",
                  (unsigned long)savefn, (unsigned long)fn_hdr, (unsigned long)fn_nslots);
          /* Slot 2 should be the keywords vector */
          if (fn_nslots >= 3) {
            LispObj kwvec = ((LispObj *)fn_raw)[2];
            fprintf(dbgout, "  kwvec (fn.slot[2]) = %016lx (tag=0x%02lx)\n",
                    (unsigned long)kwvec, (unsigned long)(kwvec >> 56));
            natural kv_raw = kwvec & 0x00FFFFFFFFFFFFFF;
            if (kv_raw > 0x100000000LL && kv_raw < 0x400000000000LL) {
              LispObj kv_hdr = ((LispObj *)kv_raw)[-1];
              natural kv_len = kv_hdr & 0x00FFFFFFFFFFFFFF;
              fprintf(dbgout, "  kwvec hdr=%016lx len=%lu\n",
                      (unsigned long)kv_hdr, (unsigned long)kv_len);
              for (natural ki = 0; ki < kv_len && ki < 20; ki++) {
                LispObj kw = ((LispObj *)kv_raw)[ki];
                fprintf(dbgout, "    kw[%lu] = %016lx (tag=0x%02lx)", ki,
                        (unsigned long)kw, (unsigned long)(kw >> 56));
                natural kw_raw = kw & 0x00FFFFFFFFFFFFFF;
                if ((kw >> 56) == 0x63 && kw_raw > 0x100000000LL && kw_raw < 0x400000000000LL) {
                  LispObj pn = ((LispObj *)kw_raw)[0];
                  natural pn_raw = pn & 0x00FFFFFFFFFFFFFF;
                  if (pn_raw > 0x100000000LL && pn_raw < 0x400000000000LL) {
                    LispObj pn_hdr = ((LispObj *)pn_raw)[-1];
                    natural pn_len = pn_hdr & 0x00FFFFFFFFFFFFFF;
                    if (pn_len > 0 && pn_len < 256) {
                      int cs = ((pn_hdr >> 56) & 0x7F) == 7 ? 4 : 1;
                      fprintf(dbgout, " \"");
                      for (int ci = 0; ci < (int)pn_len; ci++)
                        fprintf(dbgout, "%c", ((char *)pn_raw)[ci * cs]);
                      fprintf(dbgout, "\"");
                    }
                  }
                }
                fprintf(dbgout, "\n");
              }
            }
          }
        }
      }
      fflush(dbgout);
    }
    /* During cold boot, %err-disp is unbound.  Try to handle $xnopkg
       (package-not-found) by looking up the package at the C level and
       returning it as the result of %kernel-restart. */
    if (arg_y_val == 0x82) {  /* $xnopkg = 130 */
      static int xnopkg_count = 0;
      xnopkg_count++;
      if (xnopkg_count <= 5 || (xnopkg_count % 100) == 0) {
        fprintf(dbgout, "  $xnopkg attempt #%d, LR=%016lx arg_z=%016lx\n", xnopkg_count,
                (unsigned long)xpGPR(xp, 30), (unsigned long)arg_z_val);
        /* Print the package name string */
        natural sraw = untag(arg_z_val);
        if (sraw > 0x100000000LL && sraw < 0x400000000000LL) {
          LispObj shdr = *((LispObj *)sraw - 1);
          natural slen = header_element_count(shdr);
          unsigned char ssub = header_subtag(shdr);
          int scs = (ssub & 0x7F) == 7 ? 4 : 1;
          if (slen > 0 && slen < 256) {
            fprintf(dbgout, "    looking for: \"");
            for (natural si = 0; si < slen; si++)
              fprintf(dbgout, "%c", ((char *)sraw)[si * scs]);
            fprintf(dbgout, "\"\n");
          }
        }
      }
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
            /* Dump a few instructions at the return address */
            {
              opcode *ret_code = (opcode *)(natural)savelr;
              fprintf(dbgout, "  code at return addr %016lx:\n", (unsigned long)savelr);
              for (int di = -2; di < 10; di++) {
                fprintf(dbgout, "    [%+3d] %08x\n", di*4, ret_code[di]);
              }
              /* Also dump what's at [fp+16] (caller's savefn for reload-self) */
              LispObj *fp_frame = (LispObj *)savefp;
              fprintf(dbgout, "  caller frame at fp=%016lx: savevsp=%016lx savelr=%016lx savefn=%016lx savefp=%016lx\n",
                      (unsigned long)savefp,
                      (unsigned long)fp_frame[0], (unsigned long)fp_frame[1],
                      (unsigned long)fp_frame[2], (unsigned long)fp_frame[3]);
              /* Current register state at the time of UUO */
              fprintf(dbgout, "  regs at UUO: rnil(x6)=%016lx rt(x7)=%016lx x0=%016lx x1=%016lx x2=%016lx x3=%016lx\n",
                      (unsigned long)xpGPR(xp, 6), (unsigned long)xpGPR(xp, 7),
                      (unsigned long)xpGPR(xp, 0), (unsigned long)xpGPR(xp, 1),
                      (unsigned long)xpGPR(xp, 2), (unsigned long)xpGPR(xp, 3));
              fflush(dbgout);
            }
            /* Dump vsp contents at return point */
            {
              LispObj *vsp_at = (LispObj *)(natural)savevsp;
              fprintf(dbgout, "  vsp at return (savevsp=%016lx):\n", (unsigned long)savevsp);
              for (int vi = -2; vi < 6; vi++) {
                fprintf(dbgout, "    [%+2d] %016lx (tag=0x%02lx)\n",
                        vi, (unsigned long)vsp_at[vi], (unsigned long)(vsp_at[vi] >> 56));
              }
            }
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
    /* During early boot, %err-disp is unbound.  Handle errors at kernel level. */
    {
      static int early_err_count = 0;
      early_err_count++;

      if (early_err_count <= 30 || (early_err_count % 100) == 0) {
        fprintf(dbgout, "early-boot-err #%d: arg1=%u arg2=0x%x PC=%016lx LR=%016lx\n",
                early_err_count, arg1, arg2,
                (unsigned long)(natural)xpPC(xp), (unsigned long)xpGPR(xp, 30));
        if (arg1 == 0 && arg2 != 0) {
          /* UUO-based error: decode the HLT instruction */
          unsigned imm16 = HLT_IMM16(arg2);
          fprintf(dbgout, "  UUO: imm16=0x%x fmt=%u reg=x%u info=%u\n",
                  imm16, imm16 & 7, (imm16 >> 3) & 0x1F, (imm16 >> 8) & 0xFF);
        } else {
          fprintf(dbgout, "  non-UUO error: code=%u\n", arg1);
        }
        fflush(dbgout);
      }
      if (early_err_count > 500) {
        fprintf(dbgout, "early-boot-err: too many errors (%d), aborting\n", early_err_count);
        fflush(dbgout);
        _exit(1);
      }

      if (arg1 == 0 && arg2 != 0) {
        /* UUO error */
        unsigned imm16 = HLT_IMM16(arg2);
        unsigned fmt = imm16 & 7;
        unsigned info = (imm16 >> 8) & 0xFF;
        /* hlt_code_unary_misc=5, uuo_misc_not_callable info=0 (from arm64-uuo.s) */
        if (fmt == 5 && info == 0) {
          /* Check if this is %kernel-restart being called */
          natural fname_raw = untag(xpGPR(xp, 9));
          natural kr_addr = (natural)&nrs_KERNELRESTART.pname;
          natural nargs_val = xpGPR(xp, 5);

          if (fname_raw == kr_addr) {
            /* %kernel-restart called but undefined.  Handle restart types. */
            /* nargs convention: n * node_size (8).
               2 args (16): arg_y=type, arg_z=data
               3 args (24): arg_x=type, arg_y=data1, arg_z=data2 */
            LispObj restart_type;
            if (nargs_val == 3 * node_size)
              restart_type = xpGPR(xp, 13); /* arg_x = x13 */
            else
              restart_type = xpGPR(xp, 14); /* arg_y = x14 */

            if (early_err_count <= 5) {
              fprintf(dbgout, "  %%kernel-restart workaround: type=%ld nargs=%lu\n",
                      (long)restart_type, (unsigned long)nargs_val);
            }

            if (restart_type == 130) { /* $xnopkg */
              /* Package not found — look it up from %all-packages% */
              LispObj pkg_name = xpGPR(xp, 15); /* arg_z */
              natural sraw = untag(pkg_name);
              if (sraw > 0x100000000LL && sraw < 0x400000000000LL) {
                LispObj shdr = *((LispObj *)sraw - 1);
                natural slen = header_element_count(shdr);
                int scs = ((header_subtag(shdr) & 0x7F) == 7) ? 4 : 1;
                char *sdata = (char *)sraw;

                LispObj pkglist = nrs_ALL_PACKAGES.vcell;
                LispObj found_pkg = 0;
                while (fulltag_of(pkglist) == fulltag_cons) {
                  LispObj pkg = car(pkglist);
                  LispObj names = deref(pkg, 5);
                  LispObj nl = names;
                  while (fulltag_of(nl) == fulltag_cons) {
                    LispObj ns = car(nl);
                    natural ns_raw = untag(ns);
                    if (ns_raw > 0x100000000LL) {
                      LispObj ns_hdr = *((LispObj *)ns_raw - 1);
                      natural ns_len = header_element_count(ns_hdr);
                      int ns_cs = ((header_subtag(ns_hdr) & 0x7F) == 7) ? 4 : 1;
                      if (ns_len == slen) {
                        int match = 1;
                        for (natural ci = 0; ci < slen; ci++) {
                          if (((unsigned char *)sraw)[ci * scs] !=
                              ((unsigned char *)ns_raw)[ci * ns_cs]) {
                            match = 0; break;
                          }
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
                  if (early_err_count <= 5)
                    fprintf(dbgout, "  $xnopkg: found package %016lx\n",
                            (unsigned long)found_pkg);
                  xpPC(xp) = (pc)(natural)xpGPR(xp, 30);
                  xpGPR(xp, 15) = found_pkg;
                  xpGPR(xp, 5) = node_size;
                  *bumpP = 0;
                  early_err_count--;  /* don't count successful workarounds */
                  return true;
                }
              }
            }

            if (restart_type == 157) { /* $xwrongtype */
              /* Type mismatch — log details and return NIL.
                 Note: returning the object as-is causes infinite loops
                 because the caller retries the type check. */
              static int xwt_count = 0;
              xwt_count++;
              LispObj obj = xpGPR(xp, 14); /* arg_y = the mistyped object */
              LispObj expected = xpGPR(xp, 15); /* arg_z = expected type */
              if (xwt_count <= 10) {
                fprintf(dbgout, "  $xwrongtype #%d: obj=%016lx expected=%016lx LR=%016lx\n",
                        xwt_count, (unsigned long)obj, (unsigned long)expected,
                        (unsigned long)xpGPR(xp, 30));
                /* Try to print expected type name if it's a symbol */
                natural exp_raw = untag(expected);
                if ((expected >> 56) == 0x63 && exp_raw > 0x100000000LL && exp_raw < 0x400000000000LL) {
                  LispObj pn = ((LispObj *)exp_raw)[0]; /* pname */
                  natural pn_raw = untag(pn);
                  if (pn_raw > 0x100000000LL && pn_raw < 0x400000000000LL) {
                    LispObj pn_hdr = ((LispObj *)pn_raw)[-1];
                    natural pn_len = header_element_count(pn_hdr);
                    int cs = ((header_subtag(pn_hdr) & 0x7F) == 7) ? 4 : 1;
                    if (pn_len > 0 && pn_len < 256) {
                      fprintf(dbgout, "    expected type: \"");
                      for (natural i = 0; i < pn_len; i++)
                        fprintf(dbgout, "%c", ((char *)pn_raw)[i * cs]);
                      fprintf(dbgout, "\"\n");
                    }
                  }
                }
                fflush(dbgout);
              }
              if (xwt_count > 1000) {
                fprintf(dbgout, "  $xwrongtype: too many (%d), aborting\n", xwt_count);
                fflush(dbgout);
                _exit(1);
              }
              /* Return a type-appropriate default value */
              {
                LispObj retval = lisp_nil;
                /* Check expected type name to return something appropriate */
                natural exp_raw2 = untag(expected);
                if ((expected >> 56) == 0x63 && exp_raw2 > 0x100000000LL && exp_raw2 < 0x400000000000LL) {
                  LispObj pn2 = ((LispObj *)exp_raw2)[0];
                  natural pn2_raw = untag(pn2);
                  if (pn2_raw > 0x100000000LL && pn2_raw < 0x400000000000LL) {
                    LispObj pn2_hdr = ((LispObj *)pn2_raw)[-1];
                    natural pn2_len = header_element_count(pn2_hdr);
                    int cs2 = ((header_subtag(pn2_hdr) & 0x7F) == 7) ? 4 : 1;
                    char *pd2 = (char *)pn2_raw;
                    /* NUMBER/INTEGER/FIXNUM/REAL → return 0 */
                    if ((pn2_len >= 6 && pd2[0*cs2]=='N' && pd2[1*cs2]=='U' && pd2[2*cs2]=='M') ||
                        (pn2_len >= 4 && pd2[0*cs2]=='R' && pd2[1*cs2]=='E' && pd2[2*cs2]=='A' && pd2[3*cs2]=='L') ||
                        (pn2_len >= 7 && pd2[0*cs2]=='I' && pd2[1*cs2]=='N' && pd2[2*cs2]=='T') ||
                        (pn2_len >= 6 && pd2[0*cs2]=='F' && pd2[1*cs2]=='I' && pd2[2*cs2]=='X'))
                      retval = 0;
                  }
                }
                xpPC(xp) = (pc)(natural)xpGPR(xp, 30);
                xpGPR(xp, 15) = retval;
                xpGPR(xp, 5) = node_size;
                *bumpP = 0;
                return true;
              }
            }

            if (restart_type == 96) { /* $xvunbnd */
              /* Unbound variable — return NIL */
              if (early_err_count <= 5)
                fprintf(dbgout, "  $xvunbnd: returning NIL\n");
              xpPC(xp) = (pc)(natural)xpGPR(xp, 30);
              xpGPR(xp, 15) = lisp_nil;
              xpGPR(xp, 5) = node_size;
              *bumpP = 0;
              early_err_count--;
              return true;
            }
          }

          /* Check if this is %err-disp being called (level-1, undefined in early boot) */
          {
            natural ed_addr = (natural)&nrs_ERRDISP.pname;
            if (fname_raw == ed_addr) {
              /* %err-disp called but undefined.  The first arg is the error number.
                 For FASL errors, print info and abort.
                 For type/simple errors, return NIL and continue. */
              LispObj err_num = xpGPR(xp, 15); /* arg_z = last arg = error number (1-arg case) */
              if (nargs_val > node_size)
                err_num = xpGPR(xp, 14); /* arg_y for 2-arg case */
              if (nargs_val > 2 * node_size)
                err_num = xpGPR(xp, 13); /* arg_x for 3+ arg case */

              fprintf(dbgout, "early-boot %%err-disp: err_num=%ld nargs=%lu arg_z=%016lx\n",
                      (long)err_num, (unsigned long)nargs_val,
                      (unsigned long)xpGPR(xp, 15));
              fflush(dbgout);

              /* Return NIL to caller — many callers check for error return.
                 This is imperfect but allows boot to continue past non-fatal errors. */
              xpPC(xp) = (pc)(natural)xpGPR(xp, 30);
              xpGPR(xp, 15) = lisp_nil;
              xpGPR(xp, 5) = node_size;
              *bumpP = 0;
              return true;
            }
          }

          /* Other not-callable during early boot (Bug 161).
             Don't just return NIL — the caller likely can't handle it
             (e.g., ERROR is not supposed to return).  Print diagnostic
             info and abort cleanly. */
          {
            natural fn_raw = untag(xpGPR(xp, 9));
            char fn_name[64] = {0};
            /* Try to extract the function name from the symbol's pname */
            if (fn_raw > 0x100000000LL && fn_raw < 0x400000000000LL) {
              LispObj pn = ((LispObj *)fn_raw)[0]; /* pname */
              natural pn_raw = untag(pn);
              if (pn_raw > 0x100000000LL && pn_raw < 0x400000000000LL) {
                LispObj pn_hdr = ((LispObj *)pn_raw)[-1];
                natural pn_len = header_element_count(pn_hdr);
                int cs = ((header_subtag(pn_hdr) & 0x7F) == 7) ? 4 : 1;
                if (pn_len > 0 && pn_len < 60) {
                  for (natural i = 0; i < pn_len; i++)
                    fn_name[i] = ((char *)pn_raw)[i * cs];
                  fn_name[pn_len] = 0;
                }
              }
            }
            fprintf(dbgout, "early-boot-err: undefined function '%s' called during boot\n",
                    fn_name[0] ? fn_name : "???");
            /* Bug 165: Dump the hash table that caused the GETHASH failure */
            {
              /* arg_y at the time of the inner call is the hash table (key for GETHASH) */
              /* But by now registers have been modified. Let's dump istruct objects from the vstack */
              natural vsp_val = xpGPR(xp, 25);
              fprintf(dbgout, "  Bug165 vstack scan for istructs:\n");
              for (int vi = 0; vi < 16; vi++) {
                natural v = *(natural *)(vsp_val + vi * 8);
                natural v_tag = v >> 56;
                if (v_tag == 0x6e) { /* reference tag for istruct */
                  natural v_raw = v & 0x00FFFFFFFFFFFFFFULL;
                  if (v_raw > 0x100000000ULL && v_raw < 0x400000000000ULL) {
                    LispObj hdr = *((LispObj *)v_raw - 1);
                    natural hdr_subtag = hdr >> 56;
                    natural hdr_count = hdr & 0x00FFFFFFFFFFFFFFULL;
                    if (hdr_subtag == 0xae && hdr_count == 16) {
                      fprintf(dbgout, "  Found hash table at vsp[%d]=0x%lx:\n", vi, (unsigned long)v);
                      LispObj *data = (LispObj *)v_raw;
                      for (int si = 0; si < 16; si++) {
                        const char *name = "";
                        switch (si) {
                          case 0: name = " (type)"; break;
                          case 1: name = " (keytransF)"; break;
                          case 2: name = " (compareF)"; break;
                          case 3: name = " (rehash-bits)"; break;
                          case 4: name = " (vector)"; break;
                          case 5: name = " (lock)"; break;
                          case 6: name = " (owner)"; break;
                          case 7: name = " (grow-threshold)"; break;
                          case 8: name = " (rehash-ratio)"; break;
                          case 9: name = " (rehash-size)"; break;
                          case 10: name = " (puthash-count)"; break;
                          case 11: name = " (exclusion-lock)"; break;
                          case 12: name = " (nhash.find)"; break;
                          case 13: name = " (nhash.find-new)"; break;
                          case 14: name = " (read-only)"; break;
                          case 15: name = " (min-size)"; break;
                        }
                        fprintf(dbgout, "    slot[%2d] = %016lx (tag=0x%02lx)%s\n",
                                si, (unsigned long)data[si], (unsigned long)(data[si] >> 56), name);
                      }
                    }
                  }
                }
              }
            }
            fprintf(dbgout, "  PC=%016lx LR=%016lx SP=%016lx\n",
                    (unsigned long)(natural)xpPC(xp),
                    (unsigned long)xpGPR(xp, 30),
                    (unsigned long)xpGPR(xp, 31));
            /* Print arg_z which often has an error message string */
            {
              LispObj errarg = xpGPR(xp, 15);
              natural az_raw = untag(errarg);
              if (az_raw > 0x100000000LL && az_raw < 0x400000000000LL) {
                LispObj az_hdr = ((LispObj *)az_raw)[-1];
                natural az_tag = header_subtag(az_hdr);
                /* Check if it's a simple-base-string (subtag 0x87) */
                if (az_tag == 0x87) {
                  natural slen = header_element_count(az_hdr);
                  if (slen > 0 && slen < 256) {
                    fprintf(dbgout, "  arg_z (string): \"");
                    for (natural i = 0; i < slen; i++)
                      fprintf(dbgout, "%c", ((char *)az_raw)[i * 4]);
                    fprintf(dbgout, "\"\n");
                  }
                }
              }
            }
            /* Print catch_top for debugging */
            {
              TCR *tcr = get_tcr(false);
              if (tcr) {
                fprintf(dbgout, "  catch_top=%016lx vsp=%016lx\n",
                        (unsigned long)(natural)tcr->catch_top,
                        (unsigned long)xpGPR(xp, 25));
              }
            }
            fflush(dbgout);
            fprintf(dbgout, "early-boot-err: aborting (undefined function cannot safely return)\n");
            fflush(dbgout);
            _exit(1);
          }
        }
        /* Other UUO errors: skip HLT and continue */
        *bumpP = 4;
        return true;
      }
      /* Non-UUO errors (alloc failure, stack overflow, etc.): abort */
      fprintf(dbgout, "early-boot-err: fatal non-UUO error %u, aborting\n", arg1);
      fflush(dbgout);
      _exit(1);
    }
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
  fprintf(dbgout, "  imm0(x0)=%016lx imm1(x1)=%016lx imm2(x2)=%016lx sp=%016lx fp=%016lx\n",
          (unsigned long)xpGPR(xp, 0), (unsigned long)xpGPR(xp, 1),
          (unsigned long)xpGPR(xp, 2), (unsigned long)xpSP(xp), (unsigned long)xpFP(xp));
  fflush(dbgout);

  /* Bug 158: lr NOT in nfn's cv — nfn is the wrong function */
  if (HLT_IMM16(the_uuo) == 0xFFE2) {
    fprintf(dbgout, "  *** BUG158: lr NOT in nfn's cv! nfn is WRONG at mkunwind entry ***\n");
    natural nfn_val = xpGPR(xp, 10);
    natural lr_val = xpGPR(xp, 30);
    natural fp_val = xpFP(xp);
    fprintf(dbgout, "  nfn=0x%lx lr=0x%lx fp=0x%lx\n",
            (unsigned long)nfn_val, (unsigned long)lr_val, (unsigned long)fp_val);
    /* Walk frame chain from x29 */
    LispObj *fp = (LispObj *)fp_val;
    for (int fi = 0; fi < 8 && (natural)fp > 0x100000000LL && (natural)fp < 0x800000000000LL; fi++) {
      natural savevsp = fp[0], savelr = fp[1], savefn = fp[2], savefp = fp[3];
      fprintf(dbgout, "  frame[%d] @0x%lx: savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
              fi, (unsigned long)fp, (unsigned long)savelr, (unsigned long)savefn, (unsigned long)savefp);
      /* Try to identify savefn's name */
      natural sfn_tag = savefn >> 56;
      natural sfn_raw = savefn & 0x00FFFFFFFFFFFFFFULL;
      if (sfn_tag == 0x62 && sfn_raw > 0x100000000ULL && sfn_raw < 0x400000000000ULL) {
        LispObj *sfn_obj = (LispObj *)sfn_raw;
        natural sfn_hdr = *(sfn_obj - 1);
        natural sfn_ep = sfn_obj[0] & 0x00FFFFFFFFFFFFFFULL;
        int sfn_nslots = sfn_hdr & 0x00FFFFFFFFFFFFFFLL;
        fprintf(dbgout, "    fn hdr=0x%lx nslots=%d ep=0x%lx",
                (unsigned long)sfn_hdr, sfn_nslots, (unsigned long)sfn_ep);
        /* Check if savelr is within this fn's cv range */
        natural sfn_cv_raw = sfn_obj[1] & 0x00FFFFFFFFFFFFFFULL;
        if (sfn_cv_raw > 0x100000000ULL && sfn_cv_raw < 0x400000000000ULL) {
          natural sfn_cv_hdr = *((LispObj *)sfn_cv_raw - 1);
          natural sfn_cv_count = sfn_cv_hdr & 0x00FFFFFFFFFFFFFFULL;
          natural sfn_cv_bytes = sfn_cv_count * 4;
          int lr_in_cv = (savelr >= sfn_cv_raw && savelr < sfn_cv_raw + sfn_cv_bytes);
          fprintf(dbgout, " cv=[0x%lx..0x%lx) savelr %s",
                  (unsigned long)sfn_cv_raw, (unsigned long)(sfn_cv_raw + sfn_cv_bytes),
                  lr_in_cv ? "IN CV" : "NOT IN CV");
        }
        fprintf(dbgout, "\n");
        /* Print symbol constants */
        for (int si = 2; si < sfn_nslots && si < 8; si++) {
          natural sym = sfn_obj[si];
          if ((sym >> 56) == 0x63) {
            natural sym_raw = sym & 0x00FFFFFFFFFFFFFFULL;
            if (sym_raw > 0x100000000ULL && sym_raw < 0x400000000000ULL) {
              LispObj *sp2 = (LispObj *)sym_raw;
              natural pn = sp2[0] & 0x00FFFFFFFFFFFFFFULL;
              char nbuf[64] = {0};
              if (pn > 0x100000000ULL && pn < 0x400000000000ULL) {
                natural pnh = *((LispObj *)pn - 1);
                int pnl = pnh & 0x00FFFFFFFFFFFFFFLL;
                if (pnl > 0 && pnl < 60) {
                  unsigned int *c = (unsigned int *)pn;
                  for (int i = 0; i < pnl && i < 60; i++) {
                    char ch = c[i] & 0x7f;
                    nbuf[i] = (ch >= 0x20 && ch < 0x7f) ? ch : '?';
                  }
                }
              }
              fprintf(dbgout, "      slot[%d]=sym '%s'\n", si, nbuf);
            }
          }
        }
      }
      if ((natural)fp == savefp) break; /* self-loop = bottom */
      fp = (LispObj *)savefp;
    }
    /* Also try to find the REAL function by scanning for functions whose cv contains lr */
    {
      natural lr_raw = lr_val & 0x00FFFFFFFFFFFFFFULL;
      /* Scan backward from lr to find cv header */
      natural scan = lr_raw & ~7ULL;
      while (scan > 0x300000000000ULL && (lr_raw - scan) < 0x40000) {
        scan -= 8;
        natural val = *(natural *)scan;
        if ((val >> 56) == 0x88) { /* xcode_vector header */
          natural cv_count = val & 0x00FFFFFFFFFFFFFFULL;
          natural cv_data = scan + 8;
          natural cv_bytes = cv_count * 4;
          if (lr_raw >= cv_data && lr_raw < cv_data + cv_bytes) {
            fprintf(dbgout, "  REAL cv: header@0x%lx count=%lu data=[0x%lx..0x%lx)\n",
                    (unsigned long)scan, (unsigned long)cv_count,
                    (unsigned long)cv_data, (unsigned long)(cv_data + cv_bytes));
            /* Find owner function in dynamic area */
            area *da = active_dynamic_area;
            if (da) {
              LispObj *q = (LispObj *)0x302000000000ULL;
              LispObj *qend = (LispObj *)da->active;
              for (; q < qend; q++) {
                natural qraw = *q & 0x00FFFFFFFFFFFFFFULL;
                if ((qraw == cv_data || qraw == scan) && q >= (LispObj *)0x302000000000ULL + 2) {
                  natural prev_hdr = *(q - 2);
                  if ((prev_hdr >> 56) == 0xa2) {
                    LispObj *fo = q - 1;
                    natural fo_ep = fo[0] & 0x00FFFFFFFFFFFFFFULL;
                    natural fo_nslots = prev_hdr & 0x00FFFFFFFFFFFFFFULL;
                    fprintf(dbgout, "  REAL fn at 0x%lx nslots=%lu ep=0x%lx\n",
                            (unsigned long)(natural)fo, (unsigned long)fo_nslots,
                            (unsigned long)fo_ep);
                    break;
                  }
                }
              }
            }
            break;
          }
        }
      }
    }
    fflush(dbgout);
    /* Don't skip — let this be fatal */
  }

  /* TEMP DIAGNOSTIC: called-for-mv-p mismatch trap */
  if (HLT_IMM16(the_uuo) == 0x4242) {
    static int mv_diag_count = 0;
    mv_diag_count++;
    extern void ret1valn(void);
    if (mv_diag_count <= 5) {
    fprintf(dbgout, "  *** called-for-mv-p MISMATCH #%d ***\n", mv_diag_count);
    fprintf(dbgout, "  savelr (imm0/x0) = %016lx\n", (unsigned long)xpGPR(xp, 0));
    fprintf(dbgout, "  ret1valaddr global (imm1/x1) = %016lx\n", (unsigned long)xpGPR(xp, 1));
    fprintf(dbgout, "  &ret1valn (C symbol) = %016lx\n", (unsigned long)&ret1valn);
    fprintf(dbgout, "  [sp+8] = %016lx\n", (unsigned long)((LispObj *)xpSP(xp))[1]);
    /* Walk frame chain */
    LispObj *fp = (LispObj *)xpFP(xp);
    for (int fi = 0; fi < 6 && (natural)fp > 0x100000000LL && (natural)fp < 0x800000000000LL; fi++) {
      fprintf(dbgout, "  frame[%d] @%016lx: savevsp=%016lx savelr=%016lx savefn=%016lx\n",
              fi, (unsigned long)fp, (unsigned long)fp[0], (unsigned long)fp[1], (unsigned long)fp[2]);
      fp = (LispObj *)(natural)fp[3];
    }
    fflush(dbgout);
    } /* end if mv_diag_count <= 5 */
    /* Skip the HLT and continue (fall through to return NIL) */
    adjust_exception_pc(xp, 4);
    return true;
  }

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
  /* Skip if allocptr is VOID_ALLOCPTR (GC sentinel, not an allocation) */
  if (cur_allocptr == VOID_ALLOCPTR) {
    return;
  }
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
    fprintf(dbgout, "DBG pseudo_sigreturn: restoring pc=%016lx sp=%016lx x15=%016lx x25=%016lx x10=%016lx x26=%016lx\n"
            "  rnil(x6)=%016lx rt(x7)=%016lx lr=%016lx fp=%016lx x0=%016lx x9=%016lx\n",
            (unsigned long)mc->__ss.__pc, (unsigned long)mc->__ss.__sp,
            (unsigned long)mc->__ss.__x[15], (unsigned long)mc->__ss.__x[25],
            (unsigned long)mc->__ss.__x[10], (unsigned long)mc->__ss.__x[26],
            (unsigned long)mc->__ss.__x[6], (unsigned long)mc->__ss.__x[7],
            (unsigned long)mc->__ss.__lr, (unsigned long)mc->__ss.__fp,
            (unsigned long)mc->__ss.__x[0], (unsigned long)mc->__ss.__x[9]);
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
    if (0 && dbg_exc_count < 50) {
      dbg_exc_count++;
      fprintf(dbgout, "MACH[%d]: exc=%d code0=%lld pc=0x%lx lr=0x%lx vsp=0x%lx rnil=0x%lx rt=0x%lx fp=0x%lx catch_top=0x%lx allocptr=0x%lx x10=0x%lx",
              dbg_exc_count, exception, (long long)code0,
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__x[25],
              (unsigned long)ts->__x[6], (unsigned long)ts->__x[7],
              (unsigned long)ts->__fp,
              (unsigned long)(natural)tcr->catch_top,
              (unsigned long)ts->__x[26],
              (unsigned long)ts->__x[10]);
      /* Check for allocptr contamination */
      if ((ts->__x[26] >> 56) != 0 && ts->__x[26] != (natural)VOID_ALLOCPTR) {
        fprintf(dbgout, "\n  *** ALLOCPTR CONTAMINATED: tag=0x%02lx ***",
                (unsigned long)(ts->__x[26] >> 56));
      }
      /* Bug 162: Check FASL cursor corruption */
      {
        extern volatile void *dbg_fasl_cursor_addr;
        if (dbg_fasl_cursor_addr) {
          unsigned long long cv = *(unsigned long long *)dbg_fasl_cursor_addr;
          if (cv != 0 && cv < 0x10000) {
            fprintf(dbgout, "\n  *** CURSOR CORRUPT @MACH[%d]: addr=%p val=0x%llx sp=0x%lx ***",
                    dbg_exc_count, dbg_fasl_cursor_addr, cv, (unsigned long)ts->__sp);
          }
        }
      }
      if (exception == EXC_BAD_ACCESS) {
        fprintf(dbgout, " addr=0x%llx x0=0x%lx x9=0x%lx x10=0x%lx x15=0x%lx sp=0x%lx",
                (long long)code[1],
                (unsigned long)ts->__x[0], (unsigned long)ts->__x[9],
                (unsigned long)ts->__x[10], (unsigned long)ts->__x[15],
                (unsigned long)ts->__sp);
        /* Bug 143 debug: if PC is in static area (bad entrypoint), dump fn at x10 */
        if ((natural)ts->__pc >= 0x200010000ULL && (natural)ts->__pc < 0x200012000ULL) {
          natural nfn_tagged = ts->__x[10];
          natural nfn_raw = nfn_tagged & 0x00FFFFFFFFFFFFFFULL;
          fprintf(dbgout, "\n  BAD-EP: pc=0x%lx nfn=0x%lx lr=0x%lx",
                  (unsigned long)ts->__pc, (unsigned long)nfn_tagged, (unsigned long)ts->__lr);
          if (nfn_raw > 0x100000000ULL && nfn_raw < 0x400000000000ULL) {
            LispObj *fn = (LispObj *)nfn_raw;
            natural hdr = *(fn - 1);
            int nslots = hdr & 0x00FFFFFFFFFFFFFFLL;
            fprintf(dbgout, "\n  fn hdr=0x%lx nslots=%d", (unsigned long)hdr, nslots);
            for (int si = 0; si < nslots && si < 8; si++) {
              fprintf(dbgout, "\n  slot[%d]=0x%lx", si, (unsigned long)fn[si]);
            }
            /* If this looks like a closure (slot[2] is a function), dump inner fn */
            if (nslots > 2 && (fn[2] >> 56) == 0x62) {
              natural inner_raw = fn[2] & 0x00FFFFFFFFFFFFFFULL;
              if (inner_raw > 0x100000000ULL && inner_raw < 0x400000000000ULL) {
                LispObj *inner = (LispObj *)inner_raw;
                natural ihdr = *(inner - 1);
                int islots = ihdr & 0x00FFFFFFFFFFFFFFLL;
                fprintf(dbgout, "\n  inner fn hdr=0x%lx islots=%d ep=0x%lx cv=0x%lx",
                        (unsigned long)ihdr, islots, (unsigned long)inner[0], (unsigned long)inner[1]);
                /* Try to find name: usually in last-2 slot of inner fn */
                if (islots > 3) {
                  LispObj name_slot = inner[islots - 2];
                  natural name_raw = name_slot & 0x00FFFFFFFFFFFFFFULL;
                  if ((name_slot >> 56) == 0x63 && name_raw > 0x100000000ULL) {
                    LispObj *sym = (LispObj *)name_raw;
                    natural pn_raw = sym[0] & 0x00FFFFFFFFFFFFFFULL;
                    if (pn_raw > 0x100000000ULL && pn_raw < 0x400000000000ULL) {
                      char *chars = (char *)pn_raw;
                      natural pn_hdr = ((LispObj *)(pn_raw - 8))[0];
                      int len = pn_hdr & 0x00FFFFFFFFFFFFFFLL;
                      if (len > 60) len = 60;
                      fprintf(dbgout, "\n  inner name='");
                      for (int i = 0; i < len; i++) {
                        char ch = chars[i * 4];
                        if (ch >= 0x20 && ch < 0x7f) fputc(ch, dbgout);
                      }
                      fprintf(dbgout, "'");
                    }
                  }
                }
              }
            }
            /* Also dump %closure-code% NRS value for comparison */
            {
              natural rnil_raw = ts->__x[6] & 0x00FFFFFFFFFFFFFFULL;
              /* %closure-code% vcell is at rnil + symbol.vcell(8) + nrs-offset(1552) = rnil + 1560 */
              natural cc_vcell_addr = rnil_raw + 1560;
              fprintf(dbgout, "\n  %%closure-code%% vcell addr=0x%lx val=0x%lx",
                      (unsigned long)cc_vcell_addr, (unsigned long)*(LispObj*)cc_vcell_addr);
            }
          }
          fprintf(dbgout, "\n");
        }
        /* Bug 158: when PC is invalid (< 0x100000 or has TBI tag), the code
           jumped to a non-function's slot[0].  Trace back via frame savefn to
           find which symbol has the bad fcell. */
        {
          natural pc_raw = ts->__pc & 0x00FFFFFFFFFFFFFFULL;
          natural pc_tag = ts->__pc >> 56;
          if (pc_raw < 0x100000ULL || pc_tag != 0) {
            natural fp_val = ts->__fp;
            natural savefn = 0;
            if (fp_val > 0x100000000ULL && fp_val < 0x800000000000ULL) {
              savefn = *(natural *)(fp_val + 16);
            }
            natural savefn_tag = savefn >> 56;
            natural savefn_raw = savefn & 0x00FFFFFFFFFFFFFFULL;
            fprintf(dbgout, "\n  BUG158: invalid PC! pc=0x%lx (raw=0x%lx tag=0x%lx) lr=0x%lx\n",
                    (unsigned long)ts->__pc, (unsigned long)pc_raw, (unsigned long)pc_tag,
                    (unsigned long)ts->__lr);
            fprintf(dbgout, "  BUG158: frame savefn=0x%lx (tag=0x%lx) x10=0x%lx (tag=0x%lx)\n",
                    (unsigned long)savefn, (unsigned long)savefn_tag,
                    (unsigned long)ts->__x[10], (unsigned long)(ts->__x[10] >> 56));
            /* If savefn is a valid function, dump EP, code vector, and symbol constants */
            if (savefn_tag == 0x62 && savefn_raw > 0x100000000ULL && savefn_raw < 0x400000000000ULL) {
              LispObj *fn = (LispObj *)savefn_raw;
              natural hdr = *(fn - 1);
              int nslots = hdr & 0x00FFFFFFFFFFFFFFLL;
              natural ep = fn[0] & 0x00FFFFFFFFFFFFFFULL;
              natural cv_tagged = fn[1];
              natural cv_raw = cv_tagged & 0x00FFFFFFFFFFFFFFULL;
              natural cv_hdr = 0;
              int cv_len = 0;
              if (cv_raw > 0x100000000ULL && cv_raw < 0x400000000000ULL) {
                cv_hdr = *((LispObj *)cv_raw - 1);
                cv_len = cv_hdr & 0x00FFFFFFFFFFFFFFLL;
              }
              fprintf(dbgout, "  BUG158: fn ep=0x%lx cv=0x%lx cv_hdr=0x%lx cv_len=%d\n",
                      (unsigned long)ep, (unsigned long)cv_tagged,
                      (unsigned long)cv_hdr, cv_len);
              /* Check if crash LR is within this function's code vector */
              natural lr_raw = ts->__lr & 0x00FFFFFFFFFFFFFFULL;
              if (cv_raw > 0 && cv_len > 0) {
                /* xcode_vector (subtag 0x88) has 32-bit elements */
                natural cv_byte_len = cv_len * 4;
                natural cv_end = cv_raw + cv_byte_len;
                fprintf(dbgout, "  BUG158: cv range [0x%lx..0x%lx), lr_raw=0x%lx, %s\n",
                        (unsigned long)cv_raw, (unsigned long)cv_end, (unsigned long)lr_raw,
                        (lr_raw >= cv_raw && lr_raw < cv_end) ? "LR IN CV" : "LR NOT IN CV");
              }
              /* Scan backwards from LR in readonly area to find xcode_vector header */
              {
                natural scan = lr_raw & ~7ULL; /* 8-byte align */
                int found_cv = 0;
                while (scan > 0x300000000000ULL && (lr_raw - scan) < 0x40000) {
                  scan -= 8;
                  natural val = *(natural *)scan;
                  natural val_tag = val >> 56;
                  if (val_tag == 0x88) { /* xcode_vector header */
                    natural cv_count = val & 0x00FFFFFFFFFFFFFFULL;
                    natural cv_data = scan + 8;
                    natural cv_bytes = cv_count * 4;
                    if (lr_raw >= cv_data && lr_raw < cv_data + cv_bytes) {
                      fprintf(dbgout, "  BUG158: found cv header at 0x%lx count=%lu bytes=%lu range=[0x%lx..0x%lx)\n",
                              (unsigned long)scan, (unsigned long)cv_count,
                              (unsigned long)cv_bytes, (unsigned long)cv_data,
                              (unsigned long)(cv_data + cv_bytes));
                      /* Now find which function references this cv (scan dynamic area) */
                      natural cv_tagged_target = cv_data; /* we'll look for cv pointers matching this */
                      area *da2 = active_dynamic_area;
                      /* Dump first 8 instructions of the code vector */
                      {
                        opcode *cvcode = (opcode *)cv_data;
                        fprintf(dbgout, "  BUG158: cv first instrs:");
                        for (int ci = 0; ci < 8 && ci < (int)cv_count; ci++)
                          fprintf(dbgout, " %08x", cvcode[ci]);
                        fprintf(dbgout, "\n");
                      }
                      if (da2) {
                        /* Brute-force: scan for ANY word whose low 56 bits match cv_data */
                        natural alloc_raw = ts->__x[26] & 0x00FFFFFFFFFFFFFFULL;
                        /* Scan the ENTIRE dynamic range: from mapped start to allocptr.
                           da->low may not include boot image data. Use 0x302000000000 directly. */
                        LispObj *q = (LispObj *)0x302000000000ULL;
                        LispObj *qend = (alloc_raw > 0x302000000000ULL && alloc_raw < (natural)da2->high)
                          ? (LispObj *)alloc_raw : (LispObj *)da2->active;
                        int found_owner = 0;
                        natural cv_hdr_addr = cv_data - 8; /* also try header address */
                        fprintf(dbgout, "  BUG158: scanning [0x%lx..0x%lx) for cv_data=0x%lx or hdr=0x%lx\n",
                                (unsigned long)(natural)q, (unsigned long)(natural)qend,
                                (unsigned long)cv_data, (unsigned long)cv_hdr_addr);
                        for (; q < qend; q++) {
                          natural qraw = *q & 0x00FFFFFFFFFFFFFFULL;
                          if ((qraw == cv_data || qraw == cv_hdr_addr) && q >= (LispObj *)0x302000000000ULL + 2) {
                            natural match_tag = *q >> 56;
                            natural prev_hdr = *(q - 2);
                            if ((prev_hdr >> 56) == 0xa2) {
                              natural qcount = prev_hdr & 0x00FFFFFFFFFFFFFFULL;
                              LispObj *fobj2 = q - 1;
                              natural f2_ep = fobj2[0] & 0x00FFFFFFFFFFFFFFULL;
                              fprintf(dbgout, "  BUG158: OWNER at 0x%lx nslots=%lu ep=0x%lx cv_tag=0x%02lx\n",
                                      (unsigned long)(natural)fobj2, (unsigned long)qcount,
                                      (unsigned long)f2_ep, (unsigned long)match_tag);
                              /* Dump first 40 instructions from OWNER's ep */
                              if (f2_ep > 0x200000000ULL && f2_ep < 0x400000000000ULL) {
                                opcode *ep_code = (opcode *)f2_ep;
                                fprintf(dbgout, "  BUG158: OWNER ep instrs (40):\n");
                                for (int ei = 0; ei < 40 && ei < (int)cv_count; ei++) {
                                  fprintf(dbgout, "    [%3d] 0x%lx: %08x", ei,
                                          (unsigned long)(f2_ep + ei*4), ep_code[ei]);
                                  /* Annotate save-lisp-context pattern */
                                  if (ep_code[ei] == 0xa9be7bf9)
                                    fprintf(dbgout, "  ← STP vsp,lr,[sp,#-32]! (save-lisp-context)");
                                  else if (ep_code[ei] == 0xa90177ea)
                                    fprintf(dbgout, "  ← STP nfn,x29,[sp,#16] (save fn/fp)");
                                  else if (ep_code[ei] == 0x910003fd)
                                    fprintf(dbgout, "  ← ADD x29,sp,#0 (set frame ptr)");
                                  else if (ep_code[ei] == 0xf9400baa)
                                    fprintf(dbgout, "  ← LDR x10,[x29,#16] (reload-self)");
                                  else if (ep_code[ei] == 0xd63f03c0)
                                    fprintf(dbgout, "  ← BLR x30 (call)");
                                  else if (ep_code[ei] == 0xd65f03c0)
                                    fprintf(dbgout, "  ← RET");
                                  fprintf(dbgout, "\n");
                                }
                              }
                              /* Dump OWNER's symbol constants */
                              fprintf(dbgout, "  BUG158: OWNER constants (%lu slots):\n", (unsigned long)qcount);
                              for (int oi = 2; oi < (int)qcount && oi < 30; oi++) {
                                natural os = fobj2[oi];
                                natural os_tag = os >> 56;
                                natural os_raw = os & 0x00FFFFFFFFFFFFFFULL;
                                if (os_tag == 0x63 && os_raw > 0x100000000ULL && os_raw < 0x400000000000ULL) {
                                  LispObj *osym = (LispObj *)os_raw;
                                  natural opn = osym[0] & 0x00FFFFFFFFFFFFFFULL;
                                  char oname[64] = {0};
                                  if (opn > 0x100000000ULL && opn < 0x400000000000ULL) {
                                    LispObj *opnobj = (LispObj *)opn;
                                    natural opn_hdr = *(opnobj - 1);
                                    int opn_len = opn_hdr & 0x00FFFFFFFFFFFFFFLL;
                                    if (opn_len > 0 && opn_len < 60) {
                                      unsigned int *ochars = (unsigned int *)opnobj;
                                      for (int i = 0; i < opn_len && i < 60; i++) {
                                        char ch = ochars[i] & 0x7F;
                                        oname[i] = (ch >= 0x20 && ch < 0x7f) ? ch : '?';
                                      }
                                    }
                                  }
                                  /* Also dump fcell */
                                  natural ofcell = osym[2];
                                  natural ofcell_tag = ofcell >> 56;
                                  natural ofcell_raw = ofcell & 0x00FFFFFFFFFFFFFFULL;
                                  fprintf(dbgout, "    slot[%d]=sym '%s' fcell=0x%lx (tag=0x%02lx)",
                                          oi, oname, (unsigned long)ofcell, (unsigned long)ofcell_tag);
                                  if (ofcell_raw == (natural)fobj2)
                                    fprintf(dbgout, " *** SELF ***");
                                  fprintf(dbgout, "\n");
                                }
                              }
                              /* Also dump the savefn's code (the 5-slot %SIMPLE-FASL-INIT-BUFFER) */
                              {
                                fprintf(dbgout, "  BUG158: savefn ep=0x%lx cv_len=%d instrs:\n",
                                        (unsigned long)ep, cv_len);
                                if (ep > 0x200000000ULL && ep < 0x400000000000ULL) {
                                  opcode *savefn_code = (opcode *)ep;
                                  for (int si3 = 0; si3 < cv_len && si3 < 20; si3++) {
                                    fprintf(dbgout, "    [%3d] 0x%lx: %08x",
                                            si3, (unsigned long)(ep + si3*4), savefn_code[si3]);
                                    if (savefn_code[si3] == 0xa9be7bf9)
                                      fprintf(dbgout, "  ← STP vsp,lr,[sp,#-32]!");
                                    else if (savefn_code[si3] == 0xa90177ea)
                                      fprintf(dbgout, "  ← STP nfn,x29,[sp,#16]");
                                    else if (savefn_code[si3] == 0x910003fd)
                                      fprintf(dbgout, "  ← ADD x29,sp,#0");
                                    else if (savefn_code[si3] == 0xf9400baa)
                                      fprintf(dbgout, "  ← LDR x10,[x29,#16]");
                                    else if (savefn_code[si3] == 0xd63f03c0)
                                      fprintf(dbgout, "  ← BLR x30");
                                    else if (savefn_code[si3] == 0xd65f03c0)
                                      fprintf(dbgout, "  ← RET");
                                    fprintf(dbgout, "\n");
                                  }
                                }
                              }
                              /* Dump catch chain */
                              {
                                natural catch_top = ts->__x[28] ? ((natural *)((ts->__x[28] & 0x00FFFFFFFFFFFFFFULL)))[offsetof(TCR, catch_top)/sizeof(natural)] : 0;
                                /* Actually use rcontext to get catch_top */
                                natural rctx = ts->__x[28] & 0x00FFFFFFFFFFFFFFULL;
                                if (rctx > 0x100000000ULL && rctx < 0x800000000000ULL) {
                                  natural ct = *(natural *)(rctx + offsetof(TCR, catch_top));
                                  natural ct_raw = ct & 0x00FFFFFFFFFFFFFFULL;
                                  fprintf(dbgout, "  BUG158: catch_top=0x%lx (raw=0x%lx)\n",
                                          (unsigned long)ct, (unsigned long)ct_raw);
                                }
                              }
                              /* Dump cstack between sp and frame[0].fp */
                              {
                                natural sp_val = ts->__sp;
                                natural fp_val2 = ts->__fp;
                                if (fp_val2 > sp_val && (fp_val2 - sp_val) <= 0x200) {
                                  fprintf(dbgout, "  BUG158: cstack [sp=0x%lx..fp=0x%lx) (%lu bytes):\n",
                                          (unsigned long)sp_val, (unsigned long)fp_val2,
                                          (unsigned long)(fp_val2 - sp_val));
                                  natural *stp = (natural *)sp_val;
                                  natural *ste = (natural *)fp_val2;
                                  for (int si2 = 0; stp + si2 < ste + 4; si2++) {
                                    fprintf(dbgout, "    [sp+%3d] 0x%lx: 0x%lx\n",
                                            si2 * 8, (unsigned long)(sp_val + si2*8),
                                            (unsigned long)stp[si2]);
                                  }
                                }
                              }
                              found_owner = 1;
                            }
                          }
                        }
                        if (!found_owner)
                          fprintf(dbgout, "  BUG158: no owner for cv_data=0x%lx in [0x%lx..0x%lx)\n",
                                  (unsigned long)cv_data, (unsigned long)(natural)da2->low,
                                  (unsigned long)(natural)qend);
                      }
                      found_cv = 1;
                      break;
                    }
                  }
                }
                if (!found_cv) {
                  fprintf(dbgout, "  BUG158: no cv header found near lr=0x%lx\n", (unsigned long)lr_raw);
                }
              }
              /* Also scan dynamic area for ALL functions with ep near the crash LR */
              if (lr_raw > 0x300000000000ULL && lr_raw < 0x3000010000000ULL) {
                area *da = active_dynamic_area;
                if (da) {
                  LispObj *p = (LispObj *)da->low;
                  LispObj *end = (LispObj *)da->active;
                  while (p < end) {
                    natural h = *p;
                    natural htag = h >> 56;
                    natural hcount = h & 0x00FFFFFFFFFFFFFFULL;
                    if (htag == 0xa2 && hcount > 2) { /* function header */
                      LispObj *fobj = p + 1;
                      natural f_ep = fobj[0] & 0x00FFFFFFFFFFFFFFULL;
                      natural f_cv = fobj[1] & 0x00FFFFFFFFFFFFFFULL;
                      /* Check if ep is within 4KB of the crash LR (same code vector) */
                      int ep_near = (f_ep > 0x200000000ULL && f_ep < 0x400000000000ULL &&
                                     lr_raw >= f_ep && (lr_raw - f_ep) < 0x2000);
                      int cv_match = 0;
                      natural f_cv_bytes = 0;
                      if (f_cv > 0x100000000ULL && f_cv < 0x400000000000ULL) {
                        natural f_cv_hdr = *((LispObj *)f_cv - 1);
                        natural f_cv_count = f_cv_hdr & 0x00FFFFFFFFFFFFFFULL;
                        f_cv_bytes = f_cv_count * 4; /* xcode_vector has 32-bit elements */
                        cv_match = (lr_raw >= f_cv && lr_raw < f_cv + f_cv_bytes);
                      }
                      if (ep_near || cv_match) {
                          fprintf(dbgout, "  BUG158: REAL fn at 0x%lx nslots=%lu ep=0x%lx cv=[0x%lx..0x%lx) %s%s\n",
                                  (unsigned long)(natural)(p+1), (unsigned long)hcount,
                                  (unsigned long)f_ep, (unsigned long)f_cv,
                                  (unsigned long)(f_cv + f_cv_bytes),
                                  ep_near ? "EP-NEAR" : "", cv_match ? "CV-MATCH" : "");
                          /* Dump its name if possible */
                          for (int ri = 2; ri < (int)hcount && ri < 30; ri++) {
                            natural rs = fobj[ri];
                            if ((rs >> 56) == 0x63) { /* symbol */
                              natural rs_raw = rs & 0x00FFFFFFFFFFFFFFULL;
                              if (rs_raw > 0x100000000ULL && rs_raw < 0x400000000000ULL) {
                                LispObj *rsym = (LispObj *)rs_raw;
                                natural rpn = rsym[0] & 0x00FFFFFFFFFFFFFFULL;
                                if (rpn > 0x100000000ULL && rpn < 0x400000000000ULL) {
                                  LispObj *rpnobj = (LispObj *)rpn;
                                  natural rpn_hdr = *(rpnobj - 1);
                                  int rpn_len = rpn_hdr & 0x00FFFFFFFFFFFFFFLL;
                                  if (rpn_len > 0 && rpn_len < 60) {
                                    unsigned int *rchars = (unsigned int *)rpnobj;
                                    char rname[64] = {0};
                                    for (int i = 0; i < rpn_len && i < 60; i++) {
                                      char ch = rchars[i] & 0x7F;
                                      rname[i] = (ch >= 0x20 && ch < 0x7f) ? ch : '?';
                                    }
                                    fprintf(dbgout, "    slot[%d]=sym '%s'\n", ri, rname);
                                  }
                                }
                              }
                            }
                          }
                          break; /* found the real function */
                        }
                      }
                    /* Advance past the object: handle gvectors and ivectors differently */
                    if (htag >= 0x80) {
                      natural obj_words;
                      if (htag & 0x20) {
                        /* gvector: word-sized elements */
                        obj_words = hcount + 1;
                      } else {
                        /* ivector: compute byte size from subtag group */
                        natural data_bytes;
                        if (htag <= 0x88) data_bytes = hcount * 4;       /* 32-bit */
                        else if (htag <= 0x91) data_bytes = hcount * 8;  /* 64-bit */
                        else if (htag <= 0x97) data_bytes = hcount;      /* 8-bit */
                        else if (htag <= 0x9B) data_bytes = hcount * 2;  /* 16-bit */
                        else data_bytes = (hcount + 7) / 8;             /* bit vector */
                        obj_words = (8 + data_bytes + 7) / 8;  /* header + data, 8-byte aligned */
                      }
                      if (obj_words & 1) obj_words++; /* dnode align */
                      p += obj_words;
                    } else {
                      p += 2; /* skip dnode (cons cell or other non-header) */
                    }
                  }
                }
              }
              fprintf(dbgout, "  BUG158: fn hdr=0x%lx nslots=%d\n", (unsigned long)hdr, nslots);
              /* Dump all slots that look like symbols (tag 0x63) with their fcells */
              for (int si = 2; si < nslots && si < 30; si++) {
                natural slot = fn[si];
                natural slot_tag = slot >> 56;
                if (slot_tag == 0x63) {  /* symbol */
                  natural sym_raw = slot & 0x00FFFFFFFFFFFFFFULL;
                  if (sym_raw > 0x100000000ULL && sym_raw < 0x400000000000ULL) {
                    LispObj *sym = (LispObj *)sym_raw;
                    natural pname = sym[0];
                    natural fcell = sym[2];
                    natural fcell_tag = fcell >> 56;
                    natural fcell_raw = fcell & 0x00FFFFFFFFFFFFFFULL;
                    /* Try to read pname string */
                    natural pname_raw = pname & 0x00FFFFFFFFFFFFFFULL;
                    char name_buf[64] = {0};
                    if (pname_raw > 0x100000000ULL && pname_raw < 0x400000000000ULL) {
                      LispObj *pn = (LispObj *)pname_raw;
                      natural pn_hdr = *(pn - 1);
                      int pn_len = pn_hdr & 0x00FFFFFFFFFFFFFFLL;
                      if (pn_len > 0 && pn_len < 60) {
                        /* 32-bit chars in simple-base-string */
                        unsigned int *chars = (unsigned int *)pn;
                        for (int i = 0; i < pn_len && i < 60; i++) {
                          char ch = chars[i] & 0x7F;
                          name_buf[i] = (ch >= 0x20 && ch < 0x7f) ? ch : '?';
                        }
                      }
                    }
                    fprintf(dbgout, "  BUG158: slot[%d]=sym '%s' fcell=0x%lx (tag=0x%02lx)",
                            si, name_buf, (unsigned long)fcell, (unsigned long)fcell_tag);
                    if (fcell_tag != 0x62) {
                      fprintf(dbgout, " *** NOT A FUNCTION ***");
                      if (fcell_raw > 0x100000000ULL && fcell_raw < 0x400000000000ULL) {
                        natural fcell_hdr = *((LispObj *)fcell_raw - 1);
                        fprintf(dbgout, " hdr=0x%lx", (unsigned long)fcell_hdr);
                        fprintf(dbgout, " slot[0]=0x%lx", (unsigned long)*(LispObj *)fcell_raw);
                      }
                    }
                    fprintf(dbgout, "\n");
                  }
                }
              }
            }
            fflush(dbgout);
          }
        }
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
            /* Priority: dump slot[6] callee (the 3-arg hash function call) */
            if (nslots > 6) {
              LispObj s6 = fn[6];
              natural s6_raw = s6 & 0x00FFFFFFFFFFFFFF;
              fprintf(dbgout, "\n  === SLOT[6] target: 0x%lx raw=0x%lx ===", (unsigned long)s6, (unsigned long)s6_raw);
              if (s6_raw > 0x100000000ULL && s6_raw < 0x400000000000ULL) {
                LispObj *s6_obj = (LispObj *)s6_raw;
                fprintf(dbgout, "\n    [0]=0x%lx [1]=0x%lx [2]=0x%lx [3]=0x%lx [4]=0x%lx [5]=0x%lx [6]=0x%lx",
                        (unsigned long)s6_obj[0], (unsigned long)s6_obj[1], (unsigned long)s6_obj[2],
                        (unsigned long)s6_obj[3], (unsigned long)s6_obj[4], (unsigned long)s6_obj[5],
                        (unsigned long)s6_obj[6]);
                /* pname at [0] */
                natural pn = s6_obj[0] & 0x00FFFFFFFFFFFFFF;
                if (pn > 0x100000000ULL && pn < 0x400000000000ULL) {
                  unsigned char *chars = (unsigned char *)pn;
                  fprintf(dbgout, "\n    pname=\"");
                  int ci;
                  for (ci = 0; ci < 40; ci++) {
                    unsigned char ch = chars[ci * 4];
                    if (ch == 0) break;
                    if (ch >= 0x20 && ch < 0x7f) fputc(ch, dbgout);
                    else fputc('.', dbgout);
                  }
                  fprintf(dbgout, "\"");
                }
                /* fcell at [2] — dump its code */
                LispObj fc = s6_obj[2];
                natural fc_raw = fc & 0x00FFFFFFFFFFFFFF;
                if (fc_raw > 0x100000000ULL && fc_raw < 0x400000000000ULL) {
                  LispObj *callee = (LispObj *)fc_raw;
                  natural cep = callee[0] & 0x00FFFFFFFFFFFFFF;
                  fprintf(dbgout, "\n    fcell=0x%lx ep=0x%lx", (unsigned long)fc, (unsigned long)cep);
                  if (cep > 0x200000000ULL && cep < 0x400000000000ULL) {
                    opcode *ep = (opcode *)cep;
                    fprintf(dbgout, " code:");
                    int ci2;
                    for (ci2 = 0; ci2 < 24; ci2++) {
                      fprintf(dbgout, " %08x", ep[ci2]);
                    }
                  }
                }
              }
              fflush(dbgout);
            }
            /* Dump callee info for slots that look like symbols (to identify called functions) */
            {
              int si;
              for (si = 2; si < nslots && si < 10; si++) {
                LispObj slot_val = fn[si];
                natural slot_raw = slot_val & 0x00FFFFFFFFFFFFFF;
                natural slot_tag = slot_val >> 56;
                if (slot_raw > 0x100000000ULL && slot_raw < 0x400000000000ULL) {
                  LispObj *slot_obj = (LispObj *)slot_raw;
                  fprintf(dbgout, "\n  slot[%d] tag=0x%02lx", si, (unsigned long)slot_tag);
                  /* Try to read pname (offset 0 from tagged = slot[0]) for symbols */
                  LispObj pname = slot_obj[0];
                  natural pname_raw = pname & 0x00FFFFFFFFFFFFFF;
                  fprintf(dbgout, " pname_raw=0x%lx", (unsigned long)pname_raw);
                  if (pname_raw > 0x100000000ULL && pname_raw < 0x400000000000ULL) {
                    LispObj *pstr = (LispObj *)pname_raw;
                    LispObj pstr_hdr = *(pstr - 1);
                    unsigned char *chars = (unsigned char *)pstr;
                    int maxc = 40;
                    fprintf(dbgout, " hdr=0x%lx \"", (unsigned long)pstr_hdr);
                    int ci;
                    for (ci = 0; ci < maxc; ci++) {
                      unsigned char ch = chars[ci * 4]; /* 32-bit chars, low byte */
                      if (ch == 0) break;
                      if (ch >= 0x20 && ch < 0x7f) fputc(ch, dbgout);
                      else fputc('.', dbgout);
                    }
                    fprintf(dbgout, "\"");
                  }
                  /* Always try fcell at offset 16 for callee code dump */
                  LispObj fcell = slot_obj[2]; /* offset 16 = symbol.fcell */
                  natural fcell_raw = fcell & 0x00FFFFFFFFFFFFFF;
                  if (fcell_raw > 0x100000000ULL && fcell_raw < 0x400000000000ULL) {
                    LispObj *callee = (LispObj *)fcell_raw;
                    natural callee_ep = callee[0] & 0x00FFFFFFFFFFFFFF;
                    if (callee_ep > 0x200000000ULL && callee_ep < 0x400000000000ULL) {
                      opcode *ep = (opcode *)callee_ep;
                      fprintf(dbgout, "\n    callee ep=0x%lx code:", (unsigned long)callee_ep);
                      int ci2;
                      for (ci2 = 0; ci2 < 20; ci2++) {
                        fprintf(dbgout, " %08x", ep[ci2]);
                      }
                    }
                  }
                }
              }
            }
          }
          /* Dump code from function entrypoint to crash PC + margin */
          {
            natural pc_raw = ts->__pc & 0x00FFFFFFFFFFFFFF;
            if (pc_raw > 0x200000000ULL && pc_raw < 0x400000000000ULL) {
              /* Try to get entrypoint from nfn (x10) slot[0] */
              natural nfn_raw = ts->__x[10] & 0x00FFFFFFFFFFFFFF;
              natural ep_raw = 0;
              if (nfn_raw > 0x100000000ULL && nfn_raw < 0x400000000000ULL) {
                LispObj *nfn_obj = (LispObj *)nfn_raw;
                ep_raw = nfn_obj[0] & 0x00FFFFFFFFFFFFFF;  /* slot[0] = entrypoint */
              }
              if (ep_raw == 0 || ep_raw > pc_raw) ep_raw = pc_raw - 512;
              int total_instrs = ((pc_raw - ep_raw) / 4) + 80;
              if (total_instrs > 300) total_instrs = 300;
              opcode *ep_code = (opcode *)ep_raw;
              int crash_idx = (pc_raw - ep_raw) / 4;
              int ci;
              fprintf(dbgout, "\n  code dump ep=0x%lx to pc=0x%lx (+%d instrs):\n",
                      (unsigned long)ep_raw, (unsigned long)pc_raw, total_instrs);
              for (ci = 0; ci < total_instrs; ci++) {
                char marker = ((ci == crash_idx) ? '>' : ' ');
                fprintf(dbgout, "   %c[%+4d] 0x%lx: %08x\n", marker, (ci - crash_idx)*4,
                        (unsigned long)(ep_raw + ci*4), ep_code[ci]);
              }
            }
            /* Dump csp frame chain when nfn=0 */
            if (nfn_tagged == 0) {
              natural fp = ts->__fp;
              fprintf(dbgout, "\n  CSP frame chain (nfn=0 diag): fp=0x%lx sp=0x%lx\n",
                      (unsigned long)fp, (unsigned long)ts->__sp);
              int fi;
              for (fi = 0; fi < 10 && fp > 0x100000000ULL && fp < 0x800000000000ULL; fi++) {
                LispObj *frame = (LispObj *)fp;
                /* lisp_frame: [+0]=savevsp [+8]=savelr [+16]=savefn [+24]=savefp(x29) */
                fprintf(dbgout, "    frame[%d] @0x%lx: savevsp=0x%lx savelr=0x%lx savefn=0x%lx next_fp=0x%lx\n",
                        fi, (unsigned long)fp,
                        (unsigned long)frame[0], (unsigned long)frame[1],
                        (unsigned long)frame[2], (unsigned long)frame[3]);
                natural next_fp = frame[3]; /* savefp = next frame pointer */
                if (next_fp == 0 || next_fp == fp) break;
                fp = next_fp;
              }
              /* Also dump code around MACH lr */
              natural lr_raw = ts->__lr & 0x00FFFFFFFFFFFFFF;
              if (lr_raw > 0x200000000ULL && lr_raw < 0x400000000000ULL) {
                opcode *lr_code = (opcode *)lr_raw;
                fprintf(dbgout, "  code around MACH LR=0x%lx:\n", (unsigned long)ts->__lr);
                for (int ci = -16; ci <= 16; ci++) {
                  fprintf(dbgout, "   %c[%+4d] 0x%lx: %08x\n",
                          ci == 0 ? '>' : ' ', ci*4,
                          (unsigned long)(lr_raw + ci*4), lr_code[ci]);
                }
              }
              fflush(dbgout);
            }
            /* Dump macptr contents if x9 looks like a macptr */
            {
              natural x9 = ts->__x[9];
              natural x9_tag = x9 >> 56;
              natural x9_raw = x9 & 0x00FFFFFFFFFFFFFF;
              if ((x9_tag & 0x40) && x9_raw > 0x100000000ULL && x9_raw < 0x400000000000ULL) {
                LispObj *obj = (LispObj *)x9_raw;
                fprintf(dbgout, "  macptr at x9=0x%lx (raw=0x%lx):\n", (unsigned long)x9, (unsigned long)x9_raw);
                fprintf(dbgout, "    header  = 0x%lx\n", (unsigned long)obj[-1]);
                fprintf(dbgout, "    address = 0x%lx\n", (unsigned long)obj[0]);
                fprintf(dbgout, "    domain  = 0x%lx\n", (unsigned long)obj[1]);
                fprintf(dbgout, "    type    = 0x%lx\n", (unsigned long)obj[2]);
                /* Scan heap from allocptr upward to find all macptrs */
                {
                  natural ap = ts->__x[26] & 0x00FFFFFFFFFFFFFF;
                  if (ap > 0x100000000ULL && ap < 0x400000000000ULL) {
                    LispObj *scan = (LispObj *)ap;
                    int found = 0;
                    fprintf(dbgout, "    heap scan from allocptr=0x%lx (32 dwords):\n", (unsigned long)ap);
                    int si;
                    for (si = 0; si < 32; si++) {
                      LispObj w = scan[si];
                      char mark = ' ';
                      if ((w >> 56) == 0x8a && (w & 0xFF) == 3) mark = 'M'; /* macptr header */
                      fprintf(dbgout, "    %c[%+3d] 0x%lx: 0x%lx\n", mark, si*8, (unsigned long)(ap + si*8), (unsigned long)w);
                    }
                  }
                }
                fflush(dbgout);
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
  /* Bug 157: check frame savefn after EVERY exception to detect corruption.
     If [fp+16] (savefn) doesn't have function tag 0x62, the frame is corrupted. */
  {
    natural fp_val = ts->__fp;
    if (fp_val > 0x100000000ULL && fp_val < 0x800000000000ULL) {
      natural savefn = *(natural *)(fp_val + 16);
      natural savefn_tag = savefn >> 56;
      if (savefn_tag != 0x62 && savefn_tag != 0x00 && savefn != 0) {
        static int framechk_count = 0;
        if (framechk_count < 5) {
          framechk_count++;
          fprintf(dbgout, "\n  *** BUG157: FRAME SAVEFN CORRUPT! fp=0x%lx savefn=0x%lx tag=0x%02lx nfn=0x%lx pc=0x%lx lr=0x%lx ***\n",
                  (unsigned long)fp_val, (unsigned long)savefn,
                  (unsigned long)savefn_tag,
                  (unsigned long)ts->__x[10],
                  (unsigned long)ts->__pc, (unsigned long)ts->__lr);
          /* Also dump what x10 (nfn register) currently holds */
          fprintf(dbgout, "  x10_tag=0x%02lx frame[0-3]: 0x%lx 0x%lx 0x%lx 0x%lx\n",
                  (unsigned long)(ts->__x[10] >> 56),
                  (unsigned long)*(natural *)(fp_val),
                  (unsigned long)*(natural *)(fp_val + 8),
                  (unsigned long)*(natural *)(fp_val + 16),
                  (unsigned long)*(natural *)(fp_val + 24));
          fflush(dbgout);
        }
      }
    }
  }
  /* Debug: fatal trap for nthrow with NULL catch_top (HLT #0xFFFC) */
  if (exception == EXC_BAD_INSTRUCTION) {
    natural pc = ts->__pc;
    opcode insn = *(opcode *)pc;
    unsigned imm16 = (insn >> 5) & 0xFFFF;
    if (imm16 == 0xFFE8) {
      /* Bug 165: x29 corrupted — loaded from frame with non-stack address */
      natural fp_val = (natural)ts->__fp;
      natural sp_val = (natural)ts->__sp;
      fprintf(dbgout, "\n*** BUG165: x29 CORRUPTED in frame restore! ***\n");
      fprintf(dbgout, "  x29=0x%lx sp=0x%lx lr=0x%lx pc=0x%lx\n",
              (unsigned long)fp_val, (unsigned long)sp_val,
              (unsigned long)ts->__lr, (unsigned long)pc);
      fprintf(dbgout, "  nfn(x10)=0x%lx vsp(x25)=0x%lx allocptr(x15)=0x%lx\n",
              (unsigned long)ts->__x[10], (unsigned long)ts->__x[25],
              (unsigned long)ts->__x[15]);
      fprintf(dbgout, "  imm0(x9)=0x%lx imm1(x12)=0x%lx imm2(x13)=0x%lx\n",
              (unsigned long)ts->__x[9], (unsigned long)ts->__x[12],
              (unsigned long)ts->__x[13]);
      fprintf(dbgout, "  temp0(x0)=0x%lx temp1(x1)=0x%lx temp2(x2)=0x%lx\n",
              (unsigned long)ts->__x[0], (unsigned long)ts->__x[1],
              (unsigned long)ts->__x[2]);
      fprintf(dbgout, "  arg_x(x3)=0x%lx arg_y(x4)=0x%lx arg_z(x5)=0x%lx\n",
              (unsigned long)ts->__x[3], (unsigned long)ts->__x[4],
              (unsigned long)ts->__x[5]);
      fprintf(dbgout, "  fname(x6)=0x%lx rnil(x11)=0x%lx imm3(x14)=0x%lx\n",
              (unsigned long)ts->__x[6], (unsigned long)ts->__x[11],
              (unsigned long)ts->__x[14]);
      /* The HLT fires AFTER ldp nfn,x29,[sp,#savefn] but BEFORE ldp vsp,lr,[sp],#size
         So sp still points to the frame. Dump frame contents. */
      fprintf(dbgout, "  Frame at sp (pre-pop):\n");
      if (sp_val > 0x100000000ULL && sp_val < 0x800000000ULL) {
        LispObj *f = (LispObj *)sp_val;
        fprintf(dbgout, "    [sp+0]  savevsp=0x%lx\n", (unsigned long)f[0]);
        fprintf(dbgout, "    [sp+8]  savelr =0x%lx\n", (unsigned long)f[1]);
        fprintf(dbgout, "    [sp+16] savefn =0x%lx\n", (unsigned long)f[2]);
        fprintf(dbgout, "    [sp+24] savefp =0x%lx\n", (unsigned long)f[3]);
        /* Walk backwards through frames from the savefp slot */
        fprintf(dbgout, "  Frame chain (from savefp):\n");
        natural prev_fp = (natural)f[3];  /* This is the corrupted x29 */
        fprintf(dbgout, "    [0] fp=0x%lx (CORRUPTED — this triggered the halt)\n",
                (unsigned long)prev_fp);
        /* Try the PREVIOUS frame (the one that saved this corrupted x29).
           That frame's savefp is in f[3]. But f[3] is the corrupted value.
           Instead, walk sp backwards to find earlier frames. */
        fprintf(dbgout, "  Stack dump sp-0x80 to sp+0x80:\n");
        natural dump_start = (sp_val > 0x80) ? sp_val - 0x80 : sp_val;
        natural dump_end = sp_val + 0x80;
        natural addr;
        for (addr = dump_start; addr < dump_end; addr += 8) {
          if (addr >= 0x100000000ULL && addr < 0x800000000ULL) {
            LispObj val = *(LispObj *)addr;
            const char *label = "";
            if (addr == sp_val) label = " <- sp (savevsp)";
            else if (addr == sp_val + 8) label = " <- sp+8 (savelr)";
            else if (addr == sp_val + 16) label = " <- sp+16 (savefn)";
            else if (addr == sp_val + 24) label = " <- sp+24 (savefp)";
            else if (addr == sp_val + 32) label = " <- sp+32 (prev frame start?)";
            fprintf(dbgout, "    [0x%lx] = 0x%016lx%s\n",
                    (unsigned long)addr, (unsigned long)val, label);
          }
        }
      }
      /* Dump code around lr to identify the calling function */
      {
        natural lr_val = (natural)ts->__lr;
        fprintf(dbgout, "  Code at lr-0x40..lr+0x10 (lr=0x%lx):\n", (unsigned long)lr_val);
        if (lr_val > 0x200000000000ULL && lr_val < 0x400000000000ULL) {
          unsigned int *code = (unsigned int *)(lr_val - 0x40);
          int ci;
          for (ci = 0; ci < 24; ci++) {
            natural code_addr = lr_val - 0x40 + ci * 4;
            fprintf(dbgout, "    [0x%lx]: 0x%08x%s\n",
                    (unsigned long)code_addr, code[ci],
                    (code_addr == lr_val) ? " <- lr" : "");
          }
        }
      }
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFFC) {
      fprintf(dbgout, "FATAL: nthrow with NULL catch_top pc=0x%lx lr=0x%lx temp2(x10)=0x%lx sp=0x%lx\n",
              (unsigned long)pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__x[10], (unsigned long)ts->__sp);
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFD0) {
      /* Bug 165: nfn invalid in SPmvpass — trap BEFORE build_lisp_frame
         so sp/x29/lr still reflect the CALLER's state */
      natural sp_val = (natural)ts->__sp;
      natural fp_val = (natural)ts->__fp;  /* x29 = caller's frame */
      natural lr_val = (natural)ts->__lr;  /* return address in caller */
      natural nfn_val = (natural)ts->__x[10];
      natural vsp_val = (natural)ts->__x[25];
      fprintf(dbgout, "\n*** BUG165-MVPASS: nfn invalid in SPmvpass! ***\n");
      fprintf(dbgout, "  nfn(x10)=0x%lx (tag=0x%02lx) pc=0x%lx lr=0x%lx\n",
              (unsigned long)nfn_val, (unsigned long)(nfn_val >> 56),
              (unsigned long)pc, (unsigned long)lr_val);
      fprintf(dbgout, "  sp=0x%lx x29=0x%lx vsp=0x%lx nargs(x5)=0x%lx\n",
              (unsigned long)sp_val, (unsigned long)fp_val,
              (unsigned long)vsp_val, (unsigned long)ts->__x[5]);
      fprintf(dbgout, "  fname(x9)=0x%lx arg_z(x15)=0x%lx arg_y(x14)=0x%lx\n",
              (unsigned long)ts->__x[9], (unsigned long)ts->__x[15],
              (unsigned long)ts->__x[14]);
      /* Caller's frame at x29 */
      if (fp_val > 0x100000000ULL && fp_val < 0x800000000000ULL) {
        LispObj *f = (LispObj *)fp_val;
        fprintf(dbgout, "  Caller frame at x29=0x%lx:\n", (unsigned long)fp_val);
        fprintf(dbgout, "    savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                (unsigned long)f[0], (unsigned long)f[1],
                (unsigned long)f[2], (unsigned long)f[3]);
        /* Check if caller's fn is valid */
        natural caller_fn = f[2];
        natural caller_fn_tag = caller_fn >> 56;
        fprintf(dbgout, "  Caller fn tag=0x%02lx (%s)\n",
                (unsigned long)caller_fn_tag,
                caller_fn_tag == 0x62 ? "function" :
                caller_fn_tag == 0x00 ? "fixnum/entrypoint" : "INVALID");
        /* If caller's fn is a valid function, dump some of its constants */
        if (caller_fn_tag == 0x62) {
          natural fn_raw = caller_fn & 0x00FFFFFFFFFFFFFFULL;  /* strip TBI tag */
          if (fn_raw > 0x100000000ULL && fn_raw < 0x800000000000ULL) {
            LispObj *fslots = (LispObj *)fn_raw;
            fprintf(dbgout, "  Caller fn constants (first 8 slots):\n");
            int si;
            for (si = 0; si < 8 && si < 20; si++) {
              fprintf(dbgout, "    [%d] = 0x%016lx (tag=0x%02lx)\n",
                      si, (unsigned long)fslots[si],
                      (unsigned long)(fslots[si] >> 56));
            }
          }
        }
      }
      /* Dump code around lr to identify the calling instruction */
      if (lr_val > 0x20 && lr_val < 0x800000000000ULL) {
        fprintf(dbgout, "  Code around lr (return addr in caller):\n");
        unsigned int *code = (unsigned int *)(lr_val - 0x20);
        int ci;
        for (ci = 0; ci < 20; ci++) {
          natural code_addr = lr_val - 0x20 + ci * 4;
          fprintf(dbgout, "    [0x%lx]: 0x%08x%s\n",
                  (unsigned long)code_addr, code[ci],
                  (code_addr == lr_val) ? " <- lr (return)" :
                  (code_addr == lr_val - 4) ? " <- bl SPmvpass" : "");
        }
      }
      /* Also dump vstack around current vsp */
      fprintf(dbgout, "  Vstack around vsp=0x%lx:\n", (unsigned long)vsp_val);
      if (vsp_val > 0x40 && vsp_val < 0x800000000000ULL) {
        int vi;
        for (vi = -4; vi <= 8; vi++) {
          natural vaddr = vsp_val + vi * 8;
          if (vaddr > 0x100000000ULL && vaddr < 0x800000000000ULL) {
            LispObj val = *(LispObj *)vaddr;
            fprintf(dbgout, "    [vsp%+d] = 0x%016lx (tag=0x%02lx)%s\n",
                    vi * 8, (unsigned long)val, (unsigned long)(val >> 56),
                    vi == 0 ? " <- vsp" : "");
          }
        }
      }
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFE9) {
      /* Bug 156: SP is above x29 at SPstack_misc_alloc entry!
         The zeroing loop will overwrite the lisp frame. */
      fprintf(dbgout, "BUG156-ROOT: SP > x29 at stack_misc_alloc entry!\n");
      fprintf(dbgout, "  sp=0x%lx x29=0x%lx delta=%ld lr=0x%lx pc=0x%lx\n",
              (unsigned long)ts->__sp, (unsigned long)ts->__fp,
              (long)((natural)ts->__sp - (natural)ts->__fp),
              (unsigned long)ts->__lr, (unsigned long)ts->__pc);
      fprintf(dbgout, "  arg_y(count)=0x%lx arg_z(subtag)=0x%lx nfn=0x%lx\n",
              (unsigned long)ts->__x[14], (unsigned long)ts->__x[15],
              (unsigned long)ts->__x[10]);
      /* Dump frame to verify it's still intact */
      {
        natural fp_val = (natural)ts->__fp;
        if (fp_val > 0x100000000ULL && fp_val < 0x200000000ULL) {
          LispObj *f = (LispObj *)fp_val;
          fprintf(dbgout, "  frame (still intact!): savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                  (unsigned long)f[0], (unsigned long)f[1],
                  (unsigned long)f[2], (unsigned long)f[3]);
        }
      }
      /* Dump a few words at SP to see what's there */
      {
        natural sp_val = (natural)ts->__sp;
        if (sp_val > 0x100000000ULL && sp_val < 0x200000000ULL) {
          LispObj *s = (LispObj *)sp_val;
          fprintf(dbgout, "  at SP: [0]=0x%lx [1]=0x%lx [2]=0x%lx [3]=0x%lx\n",
                  (unsigned long)s[0], (unsigned long)s[1],
                  (unsigned long)s[2], (unsigned long)s[3]);
        }
      }
      /* Identify the callee that corrupted SP.
         At call time: x9 = [nfn+0x48], x10 = [x9+0x10], x30 = [x10+0], blr x30.
         Follow the chain from nfn. Strip TBI (upper byte) only; keep low tag bits
         since ldr offsets are relative to the tagged pointer. */
      {
        natural nfn_raw = (natural)ts->__x[10] & 0x00FFFFFFFFFFFFFFULL;
        fprintf(dbgout, "  nfn_raw=0x%lx\n", (unsigned long)nfn_raw);
        if (nfn_raw > 0x100000000ULL) {
          LispObj const_slot = *(LispObj *)(nfn_raw + 0x48);
          natural x9_val = const_slot & 0x00FFFFFFFFFFFFFFULL;
          fprintf(dbgout, "  const@nfn+0x48=0x%lx (x9 raw=0x%lx)\n",
                  (unsigned long)const_slot, (unsigned long)x9_val);
          if (x9_val > 0x100000000ULL) {
            LispObj callee_nfn_tagged = *(LispObj *)(x9_val + 0x10);
            natural callee_nfn_raw = callee_nfn_tagged & 0x00FFFFFFFFFFFFFFULL;
            fprintf(dbgout, "  [x9+0x10]=0x%lx (callee_nfn raw=0x%lx)\n",
                    (unsigned long)callee_nfn_tagged, (unsigned long)callee_nfn_raw);
            if (callee_nfn_raw > 0x100000000ULL) {
              LispObj entrypoint = *(LispObj *)(callee_nfn_raw);
              natural ep_raw = entrypoint & 0x00FFFFFFFFFFFFFFULL;
              fprintf(dbgout, "  [callee_nfn]=0x%lx (entrypoint raw=0x%lx)\n",
                      (unsigned long)entrypoint, (unsigned long)ep_raw);
              /* Dump callee's code */
              if (ep_raw > 0x100000000ULL) {
                unsigned int *callee_code = (unsigned int *)ep_raw;
                fprintf(dbgout, "  Callee code at 0x%lx:\n", (unsigned long)ep_raw);
                int ci;
                for (ci = 0; ci < 32; ci++) {
                  fprintf(dbgout, "    [0x%lx]: 0x%08x\n",
                          (unsigned long)(ep_raw + ci * 4), callee_code[ci]);
                }
              }
            }
          }
          /* Also dump a few words of nfn to see constant layout */
          fprintf(dbgout, "  nfn slots (raw hex):\n");
          int si;
          for (si = 0; si < 12; si++) {
            LispObj slot = *(LispObj *)(nfn_raw + si * 8);
            fprintf(dbgout, "    [nfn+0x%02x]=0x%lx\n", si * 8, (unsigned long)slot);
          }
        }
      }
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFEB) {
      /* Bug 156 cross-check: savefn=0 at SPgvset entry.
         Global variables have the savefn + x29 saved at SPgvector exit. */
      natural fp_eb = (natural)ts->__fp;
      natural saved_savefn = bug156_saved_savefn;
      natural saved_x29 = bug156_saved_x29;
      fprintf(dbgout, "BUG156-GVSET-XCHK: savefn=0 at gvset entry!\n");
      fprintf(dbgout, "  current: x29=0x%lx lr=0x%lx sp=0x%lx pc=0x%lx\n",
              (unsigned long)fp_eb, (unsigned long)ts->__lr,
              (unsigned long)ts->__sp, (unsigned long)ts->__pc);
      fprintf(dbgout, "  saved@gvector_exit: savefn=0x%lx x29=0x%lx same_frame=%d\n",
              (unsigned long)saved_savefn, (unsigned long)saved_x29,
              (int)(saved_x29 == fp_eb));
      /* Also check TCR.nfp marker from SPgvector entry */
      fprintf(dbgout, "  tcr.nfp(gvector_entry_marker)=0x%lx\n",
              (unsigned long)tcr->nfp);
      if (fp_eb > 0x100000000ULL && fp_eb < 0x200000000ULL) {
        LispObj *f = (LispObj *)fp_eb;
        fprintf(dbgout, "  frame NOW: savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                (unsigned long)f[0], (unsigned long)f[1],
                (unsigned long)f[2], (unsigned long)f[3]);
        /* Check wider memory around frame */
        fprintf(dbgout, "  Memory dump x29-0x80 to x29+0x40:\n");
        LispObj *base = (LispObj *)(fp_eb - 0x80);
        int mi;
        for (mi = 0; mi < 24; mi++) {
          natural addr = fp_eb - 0x80 + mi * 8;
          fprintf(dbgout, "    [0x%lx] = 0x%016lx%s\n",
                  (unsigned long)addr, (unsigned long)base[mi],
                  (addr == fp_eb) ? " <- x29 (savevsp)" :
                  (addr == fp_eb + 8) ? " <- savelr" :
                  (addr == fp_eb + 16) ? " <- savefn" :
                  (addr == fp_eb + 24) ? " <- savefp" : "");
        }
      }
      /* Also show page info */
      natural page_of_frame = fp_eb & ~(natural)0x3FFF;
      fprintf(dbgout, "  page: 0x%lx offset_in_page=0x%lx\n",
              (unsigned long)page_of_frame, (unsigned long)(fp_eb & 0x3FFF));
      /* Dump instructions at caller — wide range to see branches */
      {
        natural lr_val = (natural)ts->__lr;
        natural lr_raw = lr_val & 0x00FFFFFFFFFFFFFFULL;
        /* Dump from lr-0x200 to lr+0x200 to see full function including cleanup */
        fprintf(dbgout, "  Instructions lr-0x200 to lr+0x200 (lr=0x%lx):\n",
                (unsigned long)lr_raw);
        if (lr_raw > 0x200 && lr_raw < 0x400000000000ULL) {
          unsigned int *code = (unsigned int *)(lr_raw - 0x200);
          int ci;
          for (ci = 0; ci < 256; ci++) {
            natural code_addr = lr_raw - 0x200 + ci * 4;
            unsigned int insn = code[ci];
            /* Decode branch targets for B/BL/B.cond instructions */
            char branch_info[64] = "";
            if ((insn & 0xFC000000) == 0x14000000) {
              /* B: bits[25:0] is signed offset in instructions */
              int offset = (insn & 0x03FFFFFF);
              if (offset & 0x02000000) offset |= 0xFC000000; /* sign extend */
              natural target = code_addr + (long)offset * 4;
              snprintf(branch_info, sizeof(branch_info), " -> 0x%lx", (unsigned long)target);
            } else if ((insn & 0xFF000010) == 0x54000000) {
              /* B.cond: bits[23:5] is signed offset in instructions */
              int offset = (insn >> 5) & 0x7FFFF;
              if (offset & 0x40000) offset |= 0xFFF80000; /* sign extend */
              natural target = code_addr + (long)offset * 4;
              snprintf(branch_info, sizeof(branch_info), " -> 0x%lx", (unsigned long)target);
            } else if ((insn & 0x7F000000) == 0x35000000 || (insn & 0x7F000000) == 0x34000000) {
              /* CBZ/CBNZ: bits[23:5] is signed offset */
              int offset = (insn >> 5) & 0x7FFFF;
              if (offset & 0x40000) offset |= 0xFFF80000;
              natural target = code_addr + (long)offset * 4;
              snprintf(branch_info, sizeof(branch_info), " -> 0x%lx", (unsigned long)target);
            } else if ((insn & 0x7F000000) == 0x37000000 || (insn & 0x7F000000) == 0x36000000) {
              /* TBZ/TBNZ: bits[18:5] is signed offset */
              int offset = (insn >> 5) & 0x3FFF;
              if (offset & 0x2000) offset |= 0xFFFFC000;
              natural target = code_addr + (long)offset * 4;
              snprintf(branch_info, sizeof(branch_info), " -> 0x%lx", (unsigned long)target);
            }
            fprintf(dbgout, "    [0x%lx]: 0x%08x%s%s\n",
                    (unsigned long)code_addr, insn,
                    (code_addr == lr_raw) ? " <- lr" :
                    (code_addr == lr_raw - 4) ? " <- blr to SPgvset" : "",
                    branch_info);
          }
        }
      }
      /* Dump wider stack: from sp to x29+0x40 */
      if (fp_eb > 0x100000000ULL && fp_eb < 0x200000000ULL) {
        natural sp_val = (natural)ts->__sp;
        fprintf(dbgout, "  Full stack sp(0x%lx) to x29+0x40:\n", (unsigned long)sp_val);
        /* Start from sp, dump every 32 bytes until x29+0x40 */
        natural start = sp_val;
        natural end = fp_eb + 0x40;
        int count = 0;
        natural addr;
        for (addr = start; addr < end && count < 128; addr += 8, count++) {
          LispObj val = *(LispObj *)addr;
          int is_zero = (val == 0);
          /* Only print non-zero entries and boundary markers to keep output manageable */
          if (!is_zero || addr == sp_val || addr == fp_eb ||
              addr == fp_eb + 8 || addr == fp_eb + 16 || addr == fp_eb + 24) {
            fprintf(dbgout, "    [0x%lx] = 0x%016lx%s\n",
                    (unsigned long)addr, (unsigned long)val,
                    (addr == sp_val) ? " <- sp" :
                    (addr == fp_eb) ? " <- x29 (savevsp)" :
                    (addr == fp_eb + 8) ? " <- savelr" :
                    (addr == fp_eb + 16) ? " <- savefn" :
                    (addr == fp_eb + 24) ? " <- savefp" : "");
          }
        }
        /* Count total zero bytes between sp and x29 */
        int zero_count = 0;
        for (addr = sp_val; addr < fp_eb + 32; addr += 8) {
          if (*(LispObj *)addr == 0) zero_count++;
        }
        fprintf(dbgout, "  Zero 8-byte words from sp to x29+32: %d out of %d\n",
                zero_count, (int)((fp_eb + 32 - sp_val) / 8));
      }
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFED) {
      natural fp_ed = (natural)ts->__fp;
      fprintf(dbgout, "BUG156-GVEXIT: savefn zeroed DURING SPgvector! pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx arg_z=0x%lx\n",
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)fp_ed, (unsigned long)ts->__sp,
              (unsigned long)ts->__x[15]);
      if (fp_ed > 0x100000000ULL && fp_ed < 0x200000000ULL) {
        LispObj *f = (LispObj *)fp_ed;
        fprintf(dbgout, "  frame: savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                (unsigned long)f[0], (unsigned long)f[1],
                (unsigned long)f[2], (unsigned long)f[3]);
        fprintf(dbgout, "  Memory dump from x29-0x40:\n");
        LispObj *base = (LispObj *)(fp_ed - 0x40);
        int mi;
        for (mi = 0; mi < 16; mi++) {
          fprintf(dbgout, "    [x29%+5d]=0x%016lx%s\n",
                  (mi - 8) * 8, (unsigned long)base[mi],
                  (mi == 8) ? " <- savevsp" :
                  (mi == 9) ? " <- savelr" :
                  (mi == 10) ? " <- savefn" :
                  (mi == 11) ? " <- savefp" : "");
        }
      }
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFEC) {
      natural fp_ec = (natural)ts->__fp;
      fprintf(dbgout, "BUG156-GVEXIT2: savelr zeroed (but savefn OK) DURING SPgvector! pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx\n",
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)fp_ec, (unsigned long)ts->__sp);
      if (fp_ec > 0x100000000ULL && fp_ec < 0x200000000ULL) {
        LispObj *f = (LispObj *)fp_ec;
        fprintf(dbgout, "  frame: savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                (unsigned long)f[0], (unsigned long)f[1],
                (unsigned long)f[2], (unsigned long)f[3]);
      }
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFEE) {
      fprintf(dbgout, "BUG156-FRAME: build_lisp_frame verify FAILED! pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx nfn=0x%lx\n",
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__fp, (unsigned long)ts->__sp,
              (unsigned long)ts->__x[10]);
      {
        natural fpe = (natural)ts->__fp;
        if (fpe > 0x100000000ULL && fpe < 0x200000000ULL) {
          LispObj *f = (LispObj *)fpe;
          fprintf(dbgout, "  frame: [0]=0x%lx [1]=0x%lx [2]=0x%lx [3]=0x%lx\n",
                  (unsigned long)f[0], (unsigned long)f[1],
                  (unsigned long)f[2], (unsigned long)f[3]);
        }
      }
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFEF) {
      fprintf(dbgout, "BUG156-GVENTRY: frame zeros at gvset ENTRY! pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx x13=0x%lx x14=%lu x15=0x%lx\n",
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__fp, (unsigned long)ts->__sp,
              (unsigned long)ts->__x[13], (unsigned long)ts->__x[14],
              (unsigned long)ts->__x[15]);
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFF0) {
      natural gv_dest = ((natural)ts->__x[13] & 0x00FFFFFFFFFFFFFFULL) + (ts->__x[14] << 3);
      fprintf(dbgout, "BUG156-GVSET: gvset writing to frame! dest=0x%lx x29=0x%lx arg_x=0x%lx arg_y=%lu arg_z=0x%lx lr=0x%lx\n",
              (unsigned long)gv_dest,
              (unsigned long)ts->__fp,
              (unsigned long)ts->__x[13], (unsigned long)ts->__x[14],
              (unsigned long)ts->__x[15], (unsigned long)ts->__lr);
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFF1) {
      fprintf(dbgout, "BUG156-GV: frame zeros at SPgvector entry! pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx\n",
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__fp, (unsigned long)ts->__sp);
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFF2) {
      fprintf(dbgout, "BUG156-MKBLK: frame zeros at SPmakestackblock entry! pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx\n",
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__fp, (unsigned long)ts->__sp);
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFF3) {
      fprintf(dbgout, "BUG156-STKGV: frame zeros at SPstkgvector entry! pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx nargs=0x%lx\n",
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__fp, (unsigned long)ts->__sp,
              (unsigned long)ts->__x[5]);
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFF4) {
      fprintf(dbgout, "BUG156-EARLY: frame zeros at SPopt_supplied_p entry! pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx\n",
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__fp, (unsigned long)ts->__sp);
      {
        natural fp4 = (natural)ts->__fp;
        if (fp4 > 0x100000000ULL && fp4 < 0x200000000ULL) {
          LispObj *f = (LispObj *)fp4;
          fprintf(dbgout, "  frame: [0]=0x%lx [1]=0x%lx [2]=0x%lx [3]=0x%lx\n",
                  (unsigned long)f[0], (unsigned long)f[1],
                  (unsigned long)f[2], (unsigned long)f[3]);
        }
      }
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFF5) {
      fprintf(dbgout, "BUG156-SP: sp > x29 in stkgvector! sp=0x%lx x29=0x%lx x10=0x%lx lr=0x%lx pc=0x%lx\n",
              (unsigned long)ts->__sp, (unsigned long)ts->__fp,
              (unsigned long)ts->__x[10], (unsigned long)ts->__lr,
              (unsigned long)ts->__pc);
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFF7) {
      natural fp7 = (natural)ts->__fp;
      fprintf(dbgout, "BUG156-NFN0: nfn=0 but [x29+0x10] was nonzero! pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx nfn=0x%lx frame_fn=0x%lx\n",
              (unsigned long)ts->__pc, (unsigned long)ts->__lr,
              (unsigned long)fp7, (unsigned long)ts->__sp,
              (unsigned long)ts->__x[10],
              fp7 > 0x100000000ULL ? (unsigned long)((LispObj *)(fp7))[2] : 0);
      fflush(dbgout);
      _exit(1);
    }
    if (imm16 == 0xFFF6) {
      fprintf(dbgout, "BUG156-TRAP: frame[savefn]=0 at pc=0x%lx lr=0x%lx x29=0x%lx sp=0x%lx\n",
              (unsigned long)pc, (unsigned long)ts->__lr,
              (unsigned long)ts->__fp, (unsigned long)ts->__sp);
      /* Dump frame at x29 */
      natural fp_val = (natural)ts->__fp;
      if (fp_val > 0x100000000ULL && fp_val < 0x200000000ULL) {
        LispObj *fp_slots = (LispObj *)fp_val;
        fprintf(dbgout, "  [x29+0x00]=0x%lx [x29+0x08]=0x%lx [x29+0x10]=0x%lx [x29+0x18]=0x%lx\n",
                (unsigned long)fp_slots[0], (unsigned long)fp_slots[1],
                (unsigned long)fp_slots[2], (unsigned long)fp_slots[3]);
        /* Walk 3 frames back */
        int fi;
        natural cfp = fp_val;
        for (fi = 0; fi < 5 && cfp > 0x100000000ULL && cfp < 0x200000000ULL; fi++) {
          LispObj *f = (LispObj *)cfp;
          fprintf(dbgout, "  frame[%d] @0x%lx: savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                  fi, (unsigned long)cfp,
                  (unsigned long)f[0], (unsigned long)f[1],
                  (unsigned long)f[2], (unsigned long)f[3]);
          cfp = (natural)f[3]; /* next fp */
        }
      }
      /* Dump memory around x29 - wider range */
      if (fp_val > 0x100000000ULL && fp_val < 0x200000000ULL) {
        fprintf(dbgout, "  Memory dump from x29-0x100:\n");
        LispObj *base = (LispObj *)(fp_val - 0x100);
        int mi;
        for (mi = 0; mi < 48; mi++) {
          fprintf(dbgout, "    [x29%+5d]=0x%016lx%s\n",
                  (mi - 32) * 8, (unsigned long)base[mi],
                  (mi == 32) ? " ← x29 (savevsp)" :
                  (mi == 33) ? " ← x29+8 (savelr)" :
                  (mi == 34) ? " ← x29+0x10 (savefn)" :
                  (mi == 35) ? " ← x29+0x18 (savefp)" : "");
        }
      }
      /* Dump registers */
      fprintf(dbgout, "  x0=0x%lx x1=0x%lx x2=0x%lx x5=0x%lx x9=0x%lx x11=0x%lx x12=0x%lx x25=0x%lx\n",
              (unsigned long)ts->__x[0], (unsigned long)ts->__x[1],
              (unsigned long)ts->__x[2], (unsigned long)ts->__x[5],
              (unsigned long)ts->__x[9], (unsigned long)ts->__x[11],
              (unsigned long)ts->__x[12], (unsigned long)ts->__x[25]);
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
    /* First check: if PC has a TBI tag (bits 56-63 != 0), this is a branch
       to a tagged lisp object (e.g., nil, a symbol), not a legitimate code
       address.  Treat like ff-call-to-nil: skip the call and resume at lr. */
    natural pc_tag = (natural)ts->__pc >> 56;
    if (pc_tag != 0) {
      /* Branch to tagged lisp pointer.  Check if lr-4 is 'blr x16' (ff-call)
         or if this is a lisp-level branch-to-nil. */
      unsigned int *prev_insn = (unsigned int *)((natural)ts->__lr - 4);
      natural prev_pc = (natural)ts->__lr;
      static int tagged_branch_count = 0;
      tagged_branch_count++;
      if (tagged_branch_count <= 5)
        fprintf(dbgout, "branch-to-tagged: pc=0x%lx lr=0x%lx tag=0x%lx (#%d)\n",
                (unsigned long)ts->__pc, (unsigned long)ts->__lr,
                (unsigned long)pc_tag, tagged_branch_count);
      if (tagged_branch_count > 50000) {
        fprintf(dbgout, "too many branch-to-tagged (%d), aborting\n", tagged_branch_count);
        fflush(dbgout);
        _exit(1);
      }
      /* Skip: set x0=0 and resume at lr */
      *out_ts = *ts;
      out_ts->__x[0] = 0;
      out_ts->__pc = prev_pc;
      kret = KERN_SUCCESS;
      goto done;
    }
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
      natural pc_untagged = (natural)ts->__pc & 0x00FFFFFFFFFFFFFF;

      /* Determine if this is an instruction fetch (exec fault) or data write.
         For Mach exceptions, EXC_BAD_ACCESS with KERN_PROTECTION_FAILURE:
         Check if PC is at the fault address (exec fault) or elsewhere (data fault).
         Must strip TBI tag from PC before comparing to page address. */
      if (pc_untagged >= page_start &&
          pc_untagged < page_start + page_size) {
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
      /* Bug 156: check if W^X toggle corrupted the lisp frame */
      {
        natural fp156 = (natural)ts->__fp;
        if (fp156 > 0x100000000ULL && fp156 < 0x200000000ULL) {
          LispObj savelr = ((LispObj *)fp156)[1];
          LispObj savefn = ((LispObj *)fp156)[2];
          if (savelr == 0 && savefn == 0) {
            static int frame_zero_wxcount = 0;
            if (frame_zero_wxcount == 0) {
              frame_zero_wxcount++;
              fprintf(dbgout, "BUG156-WX: frame zeroed after W^X! fp=0x%lx pc=0x%lx fault=0x%lx page=0x%lx %s\n",
                      (unsigned long)fp156, (unsigned long)ts->__pc,
                      (unsigned long)fault_addr, (unsigned long)page_start,
                      (pc_untagged >= page_start && pc_untagged < page_start + page_size) ? "EXEC" : "DATA");
              fflush(dbgout);
            }
          }
        }
      }
      kret = KERN_SUCCESS;
    } else {
      /* Protection fault outside heap (e.g. vstack guard) — dispatch as SIGBUS */
      /* Dump function name from x10 (nfn) for debugging */
      {
        natural nfn_raw = ts->__x[10] & 0x00FFFFFFFFFFFFFFULL;
        if (nfn_raw >= (natural)heap_start && nfn_raw < (natural)a->high) {
          /* Function object: slot 0=entrypoint, slot 1=codevector, ... */
          /* Try to find lfun-info or name in the function's constants */
          LispObj *fn_slots = (LispObj *)nfn_raw;
          /* Slot 2 is usually the function name or lfun-info */
          fprintf(dbgout, "  fn@0x%lx slots:", (unsigned long)nfn_raw);
          int fi;
          for (fi = 0; fi < 8 && (natural)(fn_slots + fi) < (natural)a->high; fi++) {
            fprintf(dbgout, " [%d]=0x%lx", fi, (unsigned long)fn_slots[fi]);
          }
          fprintf(dbgout, "\n");
          /* If slot[2] looks like a symbol (TBI tag 0x63=tag-symbol), read its pname */
          natural s2 = fn_slots[2];
          natural s2_tag = s2 >> 56;
          if (s2_tag == 0x63) {
            natural sym_raw = s2 & 0x00FFFFFFFFFFFFFFULL;
            LispObj *sym = (LispObj *)sym_raw;
            /* Symbol pname is slot 0 (misc-data-offset=0 on ARM64) */
            LispObj pname = sym[0];
            natural pname_raw = pname & 0x00FFFFFFFFFFFFFFULL;
            /* pname should be in heap or readonly area */
            if (pname_raw >= 0x200000000ULL && pname_raw < (natural)a->high) {
              /* Read string header at pname_raw - 8 (misc-header-offset=-8) */
              LispObj pname_hdr = ((LispObj *)(pname_raw - 8))[0];
              natural pname_len = pname_hdr & 0x00FFFFFFFFFFFFFFULL;
              if (pname_len > 64) pname_len = 64;
              char *pname_data = (char *)pname_raw;
              fprintf(dbgout, "  fn name: '");
              int pi;
              for (pi = 0; pi < (int)pname_len && pname_data[pi] >= 0x20 && pname_data[pi] < 0x7f; pi++)
                fputc(pname_data[pi], dbgout);
              fprintf(dbgout, "' (len=%lu)\n", (unsigned long)pname_len);
            }
          } else {
            fprintf(dbgout, "  slot[2] tag=0x%lx (expected 0x63 for symbol)\n",
                    (unsigned long)s2_tag);
          }
        }
      }
      /* Bug 133 diagnostic: dump hash-vector from x11 if it's in dynamic area */
      {
        natural x11 = ts->__x[11];
        natural x11_raw = x11 & 0x00FFFFFFFFFFFFFFULL;
        natural x11_tag = x11 >> 56;
        if (x11_tag == 0x67 && x11_raw >= (natural)heap_start && x11_raw < (natural)a->high) {
          LispObj *hv = (LispObj *)x11_raw;
          LispObj hv_hdr = *(hv - 1);
          natural hv_count = hv_hdr & 0x00FFFFFFFFFFFFFFULL;
          fprintf(dbgout, "  Bug133: hash-vector x11=0x%lx raw=0x%lx hdr=0x%lx count=%lu\n",
                  (unsigned long)x11, (unsigned long)x11_raw, (unsigned long)hv_hdr, (unsigned long)hv_count);
          /* Dump overhead slots 0-13 */
          int hi;
          for (hi = 0; hi < 14 && (natural)(hv + hi) < (natural)a->high; hi++) {
            fprintf(dbgout, "    hv[%d]=0x%lx\n", hi, (unsigned long)hv[hi]);
          }
          fprintf(dbgout, "  x14(entries)=0x%lx x15(length)=0x%lx x0(byteoff)=0x%lx\n",
                  (unsigned long)ts->__x[14], (unsigned long)ts->__x[15], (unsigned long)ts->__x[0]);
          fflush(dbgout);
        }
      }
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
    if ((faulting_pc >> 56) != 0 || faulting_pc == 0) {
      /* PC has TBI tag (branch to tagged lisp value) or is NULL (branch
         to null C function pointer).  Check if lr-4 is 'blr x16'. */
      unsigned int *prev_insn = (return_lr > 4) ? (unsigned int *)(return_lr - 4) : NULL;
      if (prev_insn && *prev_insn == 0xd63f0200) {
        static int ff_nil_count = 0;
        ff_nil_count++;
        if (ff_nil_count <= 5 || (ff_nil_count % 500) == 0) {
          fprintf(dbgout, "ff-call to nil/tagged (#%d) x16=0x%lx\n", ff_nil_count,
                  (unsigned long)ts->__x[16]);
          /* Dump SPeabi_ff_call saved state from vsp */
          natural saved_vsp = (natural)tcr->save_vsp;
          if (saved_vsp > 0x100000000LL && saved_vsp < 0x800000000000LL) {
            LispObj *vsp_data = (LispObj *)saved_vsp;
            fprintf(dbgout, "  save_vsp=0x%lx: nfn=0x%lx saved_lr=0x%lx\n",
                    (unsigned long)saved_vsp,
                    (unsigned long)vsp_data[4], (unsigned long)vsp_data[5]);
            /* Try to identify the calling function and its constants */
            LispObj nfn_val = vsp_data[4];
            natural nfn_tag = nfn_val >> 56;
            if (nfn_tag != 0) {  /* has TBI tag = lisp object */
              natural nfn_base = untag(nfn_val) - node_size; /* header address */
              LispObj *fn_slots = (LispObj *)nfn_base;
              LispObj fn_header = fn_slots[0];
              natural fn_num_slots = fn_header & 0x00FFFFFFFFFFFFFFLL;
              fprintf(dbgout, "  fn header=0x%lx num_slots=%lu\n",
                      (unsigned long)fn_header, (unsigned long)fn_num_slots);
              /* Print constants (slots after entrypoint + codevector) */
              if (fn_num_slots >= 5) {
                for (int ci = 3; ci <= (int)fn_num_slots && ci <= 8; ci++) {
                  LispObj cval = fn_slots[ci];
                  natural ctag = cval >> 56;
                  fprintf(dbgout, "  fn.slot[%d]=0x%lx (tag=0x%lx)\n",
                          ci, (unsigned long)cval, (unsigned long)ctag);
                  /* If this looks like a symbol (tag 0x63), try to print pname */
                  if (ctag == 0x63) {
                    natural sym_base = untag(cval) - node_size;
                    LispObj *sym_slots = (LispObj *)sym_base;
                    LispObj pname = sym_slots[1]; /* pname is first data slot */
                    LispObj vcell = sym_slots[2]; /* vcell is second */
                    fprintf(dbgout, "    sym pname=0x%lx vcell=0x%lx\n",
                            (unsigned long)pname, (unsigned long)vcell);
                    /* Try to read pname string characters */
                    natural pname_tag = pname >> 56;
                    if (pname_tag != 0) {
                      natural pn_base = untag(pname) - node_size;
                      LispObj *pn_slots = (LispObj *)pn_base;
                      LispObj pn_header = pn_slots[0];
                      natural pn_len = pn_header & 0x00FFFFFFFFFFFFFFLL;
                      /* simple-string: 32-bit chars starting at pn_base+8 */
                      unsigned int *chars = (unsigned int *)(pn_base + node_size);
                      char buf[64];
                      int max = pn_len > 60 ? 60 : (int)pn_len;
                      for (int k = 0; k < max; k++) {
                        buf[k] = (char)(chars[k] & 0x7F);
                      }
                      buf[max] = 0;
                      fprintf(dbgout, "    pname=\"%s\" (len=%lu)\n", buf, (unsigned long)pn_len);
                    }
                  }
                }
              }
            }
          }
          /* Check KERNEL_IMPORTS global */
          natural kimports = (natural)lisp_global(KERNEL_IMPORTS);
          fprintf(dbgout, "  KERNEL_IMPORTS=0x%lx\n", (unsigned long)kimports);
          fflush(dbgout);
        }
        if (ff_nil_count > 500000) {
          fprintf(dbgout, "too many ff-call-to-nil (%d), aborting\n", ff_nil_count);
          fflush(dbgout);
          _exit(1);
        }
        /* After several retries from the same call site, skip past the entire
           ff-call by restoring from SPeabi_ff_call's vstack frame and returning
           nil to the lisp caller.  SPeabi_ff_call saves on vstack:
           [0]=cs_area [8]=arg_x [16]=imm2 [24]=imm1 [32]=fn [40]=lr */
        {
          static natural last_ff_nil_lr = 0;
          static int same_site_count = 0;
          if (return_lr == last_ff_nil_lr) {
            same_site_count++;
          } else {
            last_ff_nil_lr = return_lr;
            same_site_count = 1;
          }
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
      /* Bug 156: dump stack context when x10 first becomes 0 */
      {
        static int first_x10_zero = 1;
        if (first_x10_zero && ts->__x[10] == 0 && fault_pc > 4096) {
          first_x10_zero = 0;
          natural fp_val = (natural)ts->__fp;
          natural lr_val = (natural)ts->__lr;
          natural sp_val = (natural)ts->__sp;
          fprintf(dbgout, "BUG156: x10=0 at pc=0x%lx lr=0x%lx fp=0x%lx sp=0x%lx\n",
                  (unsigned long)fault_pc, (unsigned long)lr_val,
                  (unsigned long)fp_val, (unsigned long)sp_val);
          /* Dump stack frame: [fp] and surrounding */
          if (fp_val > 0x100000000ULL && fp_val < 0x200000000ULL) {
            LispObj *fp_slots = (LispObj *)fp_val;
            fprintf(dbgout, "  [fp-0x10]=0x%lx [fp-0x08]=0x%lx [fp+0x00]=0x%lx [fp+0x08]=0x%lx [fp+0x10]=0x%lx [fp+0x18]=0x%lx\n",
                    (unsigned long)fp_slots[-2], (unsigned long)fp_slots[-1],
                    (unsigned long)fp_slots[0], (unsigned long)fp_slots[1],
                    (unsigned long)fp_slots[2], (unsigned long)fp_slots[3]);
          }
          /* Dump catch frame from tcr->catch_top */
          {
            natural ct = (natural)tcr->catch_top & 0x00FFFFFFFFFFFFFFULL;
            if (ct > 0x100000000ULL) {
              LispObj *cf = (LispObj *)ct;
              fprintf(dbgout, "  catch_frame: hdr=0x%lx link=0x%lx mvflag=0x%lx tag=0x%lx\n",
                      (unsigned long)cf[-1], (unsigned long)cf[0],
                      (unsigned long)cf[1], (unsigned long)cf[2]);
            }
          }
          /* Walk back one frame: check previous fp and its saved nfn */
          if (fp_val > 0x100000000ULL && fp_val < 0x200000000ULL) {
            LispObj *fp_slots = (LispObj *)fp_val;
            /* In lisp frame: [sp+0]=savevsp [sp+8]=savelr [sp+16]=savefn [sp+24]=savefp */
            /* But fp (x29) points to sp, so fp[0]=savevsp, fp[1]=savelr, fp[2]=savefn, fp[3]=savefp */
            natural prev_fp = (natural)fp_slots[3]; /* x29 saved at fp+0x18 */
            natural saved_fn = (natural)fp_slots[2]; /* nfn saved at fp+0x10 */
            natural saved_lr = (natural)fp_slots[1]; /* lr saved at fp+0x08 */
            natural saved_vsp = (natural)fp_slots[0]; /* vsp saved at fp+0x00 */
            fprintf(dbgout, "  frame: savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                    (unsigned long)saved_vsp, (unsigned long)saved_lr,
                    (unsigned long)saved_fn, (unsigned long)prev_fp);
            /* Walk one more frame back */
            if (prev_fp > 0x100000000ULL && prev_fp < 0x200000000ULL) {
              LispObj *pfp = (LispObj *)prev_fp;
              fprintf(dbgout, "  prev_frame: savevsp=0x%lx savelr=0x%lx savefn=0x%lx savefp=0x%lx\n",
                      (unsigned long)pfp[0], (unsigned long)pfp[1],
                      (unsigned long)pfp[2], (unsigned long)pfp[3]);
            }
          }
          /* Dump 16 words of stack from sp */
          if (sp_val > 0x100000000ULL && sp_val < 0x200000000ULL) {
            LispObj *sp_words = (LispObj *)sp_val;
            fprintf(dbgout, "  stack from sp:\n");
            int si;
            for (si = 0; si < 16; si++) {
              fprintf(dbgout, "    [sp+0x%02x]=0x%lx\n", si*8, (unsigned long)sp_words[si]);
            }
          }
          fflush(dbgout);
        }
      }
      /* Bug 140: If PC itself is 0 (branch-to-null via blr to 0), we can't
         read the instruction.  Resume at lr instead. */
      if (fault_pc < 4096) {
        static int call_null_count = 0;
        call_null_count++;
        if (call_null_count <= 5 || (call_null_count % 100) == 0) {
          natural lr_val = (natural)ts->__lr;
          fprintf(dbgout, "call-to-null[%d]: pc=0x%lx lr=0x%lx x2=0x%lx x28=0x%lx\n",
                  call_null_count,
                  (unsigned long)fault_pc, (unsigned long)lr_val,
                  (unsigned long)ts->__x[2], (unsigned long)ts->__x[28]);
          /* Dump memory at x28+0x240 (sptab[24]) */
          if (ts->__x[28] > 0x100000000ULL && ts->__x[28] < 0x200000000ULL) {
            natural tcr_addr = ts->__x[28];
            fprintf(dbgout, "  mem@x28+0x240=0x%lx mem@x28+0x238=0x%lx mem@x28+0x248=0x%lx\n",
                    (unsigned long)((LispObj*)tcr_addr)[0x240/8],
                    (unsigned long)((LispObj*)tcr_addr)[0x238/8],
                    (unsigned long)((LispObj*)tcr_addr)[0x248/8]);
          }
          /* Dump instructions around lr */
          if (lr_val > 0x200000000000ULL && lr_val < 0x400000000000ULL) {
            opcode *lr_insns = (opcode *)lr_val;
            fprintf(dbgout, "  insn@lr: [-4]=%08x [-3]=%08x [-2]=%08x [-1]=%08x [0]=%08x [1]=%08x [2]=%08x [3]=%08x\n",
                    lr_insns[-4], lr_insns[-3], lr_insns[-2], lr_insns[-1],
                    lr_insns[0], lr_insns[1], lr_insns[2], lr_insns[3]);
          }
          /* Dump nrs_CLOSURE_CODE from C and from rnil */
          {
            lispsymbol *cc_sym = &nrs_CLOSURE_CODE;
            natural rnil_raw = ts->__x[6] & 0x00FFFFFFFFFFFFFFULL;
            fprintf(dbgout, "  nrs_CLOSURE_CODE(C): hdr=0x%lx pname=0x%lx vcell=0x%lx (addr=%p)\n",
                    (unsigned long)cc_sym->header, (unsigned long)cc_sym->pname,
                    (unsigned long)cc_sym->vcell, (void*)cc_sym);
            fprintf(dbgout, "  rnil=0x%lx (raw=0x%lx) nil_base=0x%lx sizeof(lispsymbol)=%lu\n",
                    (unsigned long)ts->__x[6], (unsigned long)rnil_raw,
                    (unsigned long)nil_base_address, (unsigned long)sizeof(lispsymbol));
            /* What Lisp would load: rnil + nrs-offset + symbol.vcell
               nrs-offset for pos=24 = (24-1)*symbol.size = 23*64 = 1472
               symbol.vcell = 8
               total = 1480 */
            natural lisp_vcell_addr = rnil_raw + 1480;
            fprintf(dbgout, "  Lisp vcell addr=0x%lx value=0x%lx\n",
                    (unsigned long)lisp_vcell_addr,
                    (unsigned long)*(LispObj*)lisp_vcell_addr);
            /* Also dump NRS[0] (T) pname to verify alignment */
            lispsymbol *t_sym = &nrs_T;
            fprintf(dbgout, "  nrs_T(C): hdr=0x%lx pname=0x%lx (addr=%p)\n",
                    (unsigned long)t_sym->header, (unsigned long)t_sym->pname, (void*)t_sym);
            /* Dump function nfn's slot[0] and slot[1] headers */
            natural nfn_raw = ts->__x[10] & 0x00FFFFFFFFFFFFFFULL;
            if (nfn_raw > 0x100000000ULL) {
              LispObj *fn = (LispObj *)nfn_raw;
              fprintf(dbgout, "  nfn[0]=0x%lx nfn[1]=0x%lx\n",
                      (unsigned long)fn[0], (unsigned long)fn[1]);
              /* Check slot[1] - if it's a code-vector, dump its header */
              natural s1_raw = fn[1] & 0x00FFFFFFFFFFFFFFULL;
              if (s1_raw > 0x100000000ULL) {
                LispObj s1_hdr = ((LispObj *)s1_raw)[-1];
                fprintf(dbgout, "  nfn[1] hdr=0x%lx subtag=0x%02lx\n",
                        (unsigned long)s1_hdr, (unsigned long)(s1_hdr >> 56));
              }
            }
          }
          fflush(dbgout);
        }
        if (call_null_count > 1000) {
          fprintf(dbgout, "FATAL: %d call-to-null repeats, aborting\n", call_null_count);
          fflush(dbgout);
          _exit(1);
        }
        *out_ts = *ts;
        out_ts->__x[0] = 0;
        out_ts->__pc = ts->__lr;
        kret = KERN_SUCCESS;
        goto done;
      }
      unsigned int insn = *(unsigned int *)fault_pc;
      int dest_reg = insn & 0x1f;  /* bits 4:0 = destination register */
      static int null_deref_count = 0;
      null_deref_count++;
      fprintf(dbgout, "null-deref #%d: pc=0x%lx insn=0x%08x dest=x%d addr=0x%llx\n",
              null_deref_count, (unsigned long)fault_pc, insn, dest_reg, (long long)code[1]);
      fprintf(dbgout, "  x0=0x%llx x1=0x%llx x2=0x%llx x3=0x%llx\n",
              (unsigned long long)ts->__x[0], (unsigned long long)ts->__x[1],
              (unsigned long long)ts->__x[2], (unsigned long long)ts->__x[3]);
      fprintf(dbgout, "  x9=0x%llx x10=0x%llx x11=0x%llx x12=0x%llx\n",
              (unsigned long long)ts->__x[9], (unsigned long long)ts->__x[10],
              (unsigned long long)ts->__x[11], (unsigned long long)ts->__x[12]);
      fprintf(dbgout, "  x13=0x%llx x14=0x%llx x15=0x%llx\n",
              (unsigned long long)ts->__x[13], (unsigned long long)ts->__x[14],
              (unsigned long long)ts->__x[15]);
      fprintf(dbgout, "  lr=0x%llx sp=0x%llx fp=0x%llx vsp=0x%llx allocptr=0x%llx\n",
              (unsigned long long)ts->__lr, (unsigned long long)ts->__sp,
              (unsigned long long)ts->__fp, (unsigned long long)ts->__x[25],
              (unsigned long long)ts->__x[26]);
      /* Dump code around PC */
      {
        unsigned int *pc_ptr = (unsigned int *)(uintptr_t)fault_pc;
        fprintf(dbgout, "  code:");
        for (int ci = -8; ci <= 8; ci++)
          fprintf(dbgout, " %s%08x%s", ci==0?">>>":"", pc_ptr[ci], ci==0?"<<<":"");
        fprintf(dbgout, "\n");
      }
      /* Walk lisp frames via fp chain */
      {
        unsigned long long fp_val = ts->__fp;
        fprintf(dbgout, "  frames:");
        for (int fi = 0; fi < 8 && fp_val > 0x100000000ULL; fi++) {
          unsigned long long *fp_ptr = (unsigned long long *)fp_val;
          unsigned long long saved_lr = fp_ptr[1];    /* lisp frame: [0]=savevsp [1]=savelr [2]=savefn [3]=savefp */
          unsigned long long saved_fn = fp_ptr[2];
          fprintf(dbgout, " [lr=0x%llx fn=0x%llx]", saved_lr, saved_fn);
          fp_val = fp_ptr[3];  /* next frame */
        }
        fprintf(dbgout, "\n");
      }
      fflush(dbgout);
      if (null_deref_count > 5) {
        fprintf(dbgout, "FATAL: too many null-deref skips (%d), aborting\n", null_deref_count);
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
    fprintf(dbgout, "KERN_INVALID_ADDRESS→SIGBUS: pc=0x%lx lr=0x%lx addr=0x%llx sp=0x%lx fp=0x%lx\n"
            "  x6=0x%lx x9=0x%lx x10=0x%lx x15=0x%lx x25=0x%lx valence=%d\n",
            (unsigned long)ts->__pc, (unsigned long)ts->__lr,
            (long long)code[1],
            (unsigned long)ts->__sp, (unsigned long)ts->__fp,
            (unsigned long)ts->__x[6], (unsigned long)ts->__x[9],
            (unsigned long)ts->__x[10], (unsigned long)ts->__x[15],
            (unsigned long)ts->__x[25], tcr->valence);
    /* Dump instruction at faulting PC if in lisp code */
    if (ts->__pc > 0x200000000000ULL && ts->__pc < 0x400000000000ULL) {
      opcode *insns = (opcode *)ts->__pc;
      fprintf(dbgout, "  insn@pc: [-4]=%08x [0]=%08x [+4]=%08x [+8]=%08x\n",
              insns[-1], insns[0], insns[1], insns[2]);
    }
    /* Decode function name from nfn (x10) */
    {
      natural nfn_raw = ts->__x[10] & 0x00FFFFFFFFFFFFFFULL;
      if (nfn_raw > 0x200000000ULL && nfn_raw < 0x400000000000ULL) {
        LispObj fn_hdr = ((LispObj *)nfn_raw)[-1];
        natural fn_nslots = fn_hdr & 0x00FFFFFFFFFFFFFFULL;
        if (fn_nslots > 2 && fn_nslots < 100) {
          LispObj *fn_slots = (LispObj *)nfn_raw;
          LispObj name_slot = fn_slots[fn_nslots - 2];
          natural name_raw = name_slot & 0x00FFFFFFFFFFFFFFULL;
          if (name_raw > 0x200000000ULL && name_raw < 0x400000000000ULL) {
            LispObj pname = ((LispObj *)name_raw)[0];
            natural pname_raw = pname & 0x00FFFFFFFFFFFFFFULL;
            if (pname_raw > 0x200000000ULL && pname_raw < 0x400000000000ULL) {
              LispObj ph = ((LispObj *)pname_raw)[-1];
              natural plen = ph & 0x00FFFFFFFFFFFFFFULL;
              if (plen > 0 && plen < 256) {
                int cs = ((ph >> 56) & 0x7F) == 7 ? 4 : 1;
                char *pd = (char *)pname_raw;
                fprintf(dbgout, "  crash fn (nfn): \"");
                for (int pi = 0; pi < (int)plen; pi++)
                  fprintf(dbgout, "%c", pd[pi * cs]);
                fprintf(dbgout, "\"\n");
              }
            }
          }
        }
      }
    }
    /* Decode lisp frame chain for backtrace */
    {
      natural fp = ts->__fp;
      for (int fi = 0; fi < 8 && fp > 0x100000000ULL && fp < 0x200000000000ULL; fi++) {
        LispObj *frame = (LispObj *)fp;
        LispObj savevsp = frame[0], savelr = frame[1], savefn = frame[2], savefp = frame[3];
        natural fn_raw = savefn & 0x00FFFFFFFFFFFFFFULL;
        fprintf(dbgout, "  bt[%d] lr=%016lx fn=%016lx", fi,
                (unsigned long)savelr, (unsigned long)savefn);
        if (fn_raw > 0x200000000ULL && fn_raw < 0x400000000000ULL) {
          LispObj fh = ((LispObj *)fn_raw)[-1];
          natural ns = fh & 0x00FFFFFFFFFFFFFFULL;
          if (ns > 2 && ns < 100) {
            LispObj nm = ((LispObj *)fn_raw)[ns - 2];
            natural nm_raw = nm & 0x00FFFFFFFFFFFFFFULL;
            if (nm_raw > 0x200000000ULL && nm_raw < 0x400000000000ULL) {
              LispObj pn = ((LispObj *)nm_raw)[0];
              natural pn_raw = pn & 0x00FFFFFFFFFFFFFFULL;
              if (pn_raw > 0x200000000ULL && pn_raw < 0x400000000000ULL) {
                LispObj ph = ((LispObj *)pn_raw)[-1];
                natural pl = ph & 0x00FFFFFFFFFFFFFFULL;
                if (pl > 0 && pl < 256) {
                  int cs = ((ph >> 56) & 0x7F) == 7 ? 4 : 1;
                  char *pd = (char *)pn_raw;
                  fprintf(dbgout, " \"");
                  for (int pi = 0; pi < (int)pl; pi++)
                    fprintf(dbgout, "%c", pd[pi * cs]);
                  fprintf(dbgout, "\"");
                }
              }
            }
          }
        }
        fprintf(dbgout, "\n");
        fp = (natural)savefp;
      }
    }
    fflush(dbgout);
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
    /* Bug 140: Handle alloc traps directly in Mach handler to avoid
       re-entrant exception issues.  The signal_handler path changes
       tcr->valence to FOREIGN, so any nested fault (e.g. W^X page
       toggle or heap extension) sees valence != LISP and aborts.
       By handling the common case here, we avoid setup_signal_frame
       entirely. */
    if (exception == EXC_BAD_INSTRUCTION) {
      opcode insn = *(opcode *)(natural)ts->__pc;
      if (IS_ALLOC_TRAP(insn)) {
        signed_natural disp = 0;
        opcode *pc = (opcode *)(natural)ts->__pc;
        /* Check pc[-3] and pc[-4] for the SUB instruction.
           Standard: sub, cmp, b.hi, hlt → sub at [-3].
           TCR-loaded allocbase: sub, ldr, cmp, b.hi, hlt → sub at [-4]. */
        int offsets[] = {-3, -4};
        int oi;
        for (oi = 0; oi < 2 && disp == 0; oi++) {
          opcode sub_insn = pc[offsets[oi]];
          if (IS_SUB_IMM_FROM_ALLOCPTR(sub_insn)) {
            natural imm12 = (sub_insn >> 10) & 0xFFF;
            disp = -((signed_natural)imm12);
          } else if (IS_SUB_REG_FROM_ALLOCPTR(sub_insn)) {
            unsigned rm = (sub_insn >> 16) & 0x1F;
            disp = -((signed_natural)ts->__x[rm]);
          }
        }

        if (disp) {
          natural cur_allocptr = ts->__x[allocptr];
          natural bytes_needed = (-disp) + node_size;

          /* update_bytes_allocated inline */
          {
            BytePtr last = (BytePtr)tcr->last_allocptr;
            BytePtr current = (BytePtr)(cur_allocptr - disp);
            if (last && cur_allocptr != (natural)VOID_ALLOCPTR) {
              tcr->bytes_allocated += (last - current);
            }
            tcr->last_allocptr = 0;
          }

          /* Try to allocate from active dynamic area without extending */
          {
            area *a = active_dynamic_area;
            natural log2_aq = tcr->log2_allocation_quantum;
            natural oldlimit = (natural)a->active;
            natural newlimit = (align_to_power_of_2(oldlimit, log2_aq) +
                                align_to_power_of_2(bytes_needed, log2_aq));

            if (newlimit <= (natural)a->high) {
              a->active = (BytePtr)newlimit;
              /* Zero new memory */
              if ((BytePtr)oldlimit < heap_dirty_limit) {
                if ((BytePtr)newlimit < heap_dirty_limit) {
                  memset((void *)oldlimit, 0, newlimit - oldlimit);
                } else {
                  memset((void *)oldlimit, 0, (size_t)heap_dirty_limit - oldlimit);
                }
              }
              if ((BytePtr)newlimit > heap_dirty_limit) {
                heap_dirty_limit = (BytePtr)newlimit;
              }
              /* Set output state: advance past HLT, update allocptr/allocbase */
              *out_ts = *ts;
              tcr->last_allocptr = (void *)newlimit;
              out_ts->__x[allocptr] = (LispObj)newlimit + disp;
              out_ts->__x[allocbase] = (LispObj)oldlimit;
              tcr->save_allocbase = (void *)oldlimit;
              out_ts->__pc = ts->__pc + 4;
              /* Bug 156: check frame after alloc */
              {
                natural fp156a = (natural)ts->__fp;
                if (fp156a > 0x100000000ULL && fp156a < 0x200000000ULL) {
                  LispObj sl = ((LispObj *)fp156a)[1];
                  LispObj sf = ((LispObj *)fp156a)[2];
                  if (sl == 0 && sf == 0) {
                    fprintf(dbgout, "BUG156-ALLOC: frame zeroed during alloc! fp=0x%lx pc=0x%lx disp=%ld\n",
                            (unsigned long)fp156a, (unsigned long)ts->__pc, (long)disp);
                    fflush(dbgout);
                  }
                }
              }
              kret = KERN_SUCCESS;
              goto done;
            }
            /* Heap full: fall through to signal handler for GC/extend */
          }
        }
        /* Could not handle directly */
      }

    }

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
