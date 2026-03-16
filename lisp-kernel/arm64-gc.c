/*
 * Copyright 1994-2009 Clozure Associates
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

/*
 * arm64-gc.c — Garbage collector support for ARM64 with TBI tagging.
 *
 * ARM64 TBI differences from ARM32:
 *   - Tags are in the top byte (bits 56-63), not low bits.
 *   - untag(o) = o & 0x00FFFFFFFFFFFFFF = base + node_size (8).
 *   - Header: subtag in high byte, element count in low 56 bits.
 *   - 8-byte header, 16-byte dnode (same dnode_size as ARM32).
 *   - No code vectors / PC locatives (entrypoint is in gvector slot 1).
 *   - No lisp_frame_marker on cstack; cstack/tstack areas are empty.
 *   - No subtag_pseudofunction.
 *   - Node registers: rnil (x6) through save7 (x23).
 *   - TCR is flat (no TCR_AUX).
 */

#include "lisp.h"
#include "lisp_globals.h"
#include "bits.h"
#include "gc.h"
#include "area.h"
#include "lisp-exceptions.h"
#include "threads.h"
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

/*
 * ARM64 TBI helper: given a tagged pointer to a cons or uvector,
 * return a pointer to the object's base (header) address.
 * untag(n) points to base + node_size, so subtract node_size.
 */
#define ARM64_BASE(n) ((LispObj *)ptr_from_lispobj(untag(n) - node_size))

/* area_dnode override for ARM64 is now in gc.h */

/* ================================================================
   Heap sanity checking
   ================================================================ */

void
check_node(LispObj n)
{
  int tag = fulltag_of(n), header_tag;
  area *a;
  LispObj header;

  /* Fixnums: tag 0x00 (positive) or 0xFF (negative) */
  if (tag == tag_positive_fixnum || tag == tag_negative_fixnum)
    return;

  /* Immediates: tag byte has bit 4 set (0x10-0x1F) */
  if (tag & imm_tag_mask)
    return;

  /* NIL */
  if (tag == tag_nil) {
    if (n != lisp_nil) {
      Bug(NULL, "Object tagged as nil, not nil : 0x" LISP, n);
    }
    return;
  }

  /* Headers should not appear as node values */
  if (nodeheader_tag_p(tag) || immheader_tag_p(tag)) {
    Bug(NULL, "Header not expected : 0x" LISP, n);
    return;
  }

  /* Cons or uvector ref — must point into a heap area */
  if (tag == tag_cons || is_node_fulltag(tag)) {
    a = heap_area_containing((BytePtr)ptr_from_lispobj(untag(n)));

    if (a == NULL) {
      a = active_dynamic_area;
      if ((untag(n) > (ptr_to_lispobj(a->active))) &&
          (untag(n) < (ptr_to_lispobj(a->high)))) {
        Bug(NULL, "Node points to heap free space: 0x" LISP, n);
      }
      return;
    }
  } else {
    return;
  }

  /* Node points to heap area, so check header/lack thereof. */
  header = header_of(n);
  header_tag = fulltag_of(header);
  if (tag == tag_cons) {
    if (nodeheader_tag_p(header_tag) || immheader_tag_p(header_tag)) {
      Bug(NULL, "Cons cell at 0x" LISP " has bogus header : 0x" LISP, n, header);
    }
    return;
  }

  if (!nodeheader_tag_p(header_tag) && !immheader_tag_p(header_tag)) {
    Bug(NULL, "Vector at 0x" LISP " has bogus header : 0x" LISP, n, header);
  }
}


void
check_range(LispObj *start, LispObj *end, Boolean header_allowed)
{
  LispObj node, *current = start, *prev = NULL;
  int tag, subtag;
  natural elements;

  while (current < end) {
    prev = current;
    node = *current++;
    tag = fulltag_of(node);
    if (immheader_tag_p(tag)) {
      if (!header_allowed) {
        Bug(NULL, "Header not expected at 0x" LISP "\n", (LispObj)prev);
      }
      current = (LispObj *)skip_over_ivector((natural)prev, node);
    } else if (nodeheader_tag_p(tag)) {
      if (!header_allowed) {
        Bug(NULL, "Header not expected at 0x" LISP "\n", (LispObj)prev);
      }
      subtag = header_subtag(node);
      /* ARM64 functions have entrypoint in slot 1 (a fixnum-tagged locative).
         No separate code vector to validate here. */
      elements = header_element_count(node) | 1;
      while (elements--) {
        check_node(*current++);
      }
    } else {
      check_node(node);
      check_node(*current++);
    }
  }

  if (current != end) {
    Bug(NULL, "Overran end of memory range: start = 0x" LISP ", end = 0x" LISP
        ", prev = 0x" LISP ", current = 0x" LISP,
        (LispObj)start, (LispObj)end, (LispObj)prev, (LispObj)current);
  }
}


void
check_xp(ExceptionInformation *xp)
{
  natural *regs = (natural *)xpGPRvector(xp);
  int r;

  /* Node registers: rnil (x6) through save7 (x23) */
  for (r = rnil; r <= save7; r++) {
    check_node(regs[r]);
  }
}


void
check_tcrs(TCR *first)
{
  xframe_list *xframes;
  ExceptionInformation *xp;
  TCR *tcr = first;
  LispObj *tlb_start, *tlb_end;

  do {
    xp = tcr->gc_context;
    if (xp) {
      check_xp(xp);
    }
    for (xframes = (xframe_list *)tcr->xframe;
         xframes;
         xframes = xframes->prev) {
      check_xp(xframes->curr);
    }
    tlb_start = tcr->tlb_pointer;
    if (tlb_start) {
      tlb_end = tlb_start + (tcr->tlb_limit / sizeof(LispObj));
      check_range(tlb_start, tlb_end, false);
    }
    tcr = tcr->next;
  } while (tcr != first);
}


void
check_all_areas(TCR *tcr)
{
  area *a = active_dynamic_area;
  area_code code = a->code;

  while (code != AREA_VOID) {
    switch (code) {
    case AREA_DYNAMIC:
    case AREA_WATCHED:
    case AREA_STATIC:
    case AREA_MANAGED_STATIC:
      check_range((LispObj *)a->low, (LispObj *)a->active, true);
      break;

    case AREA_VSTACK:
      {
        LispObj *low = (LispObj *)a->active;
        LispObj *high = (LispObj *)a->high;

        if (((natural)low) & node_size) {
          check_node(*low++);
        }
        check_range(low, high, false);
      }
      break;

    default:
      break;
    }
    a = a->succ;
    code = a->code;
  }
  check_tcrs(tcr);
}


/* ================================================================
   Ivector size calculation (ARM64: 8-byte header, 16-byte dnode)

   ARM64 ivector size in bytes (including 8-byte header):
     nodeheader / 32-bit ivector:  8 + (count << 2)
     64-bit ivector:               8 + (count << 3)
     8-bit ivector:                8 + count
     16-bit ivector:               8 + (count << 1)
     complex_double_float_vector:  8 + (count << 4)
     bit_vector:                   8 + ((count+7) >> 3)

   suffix_dnodes = ((total + 15) >> 4) - 1
   ================================================================ */

/*
 * Compute the total size in bytes of an ivector (including header)
 * and return the number of suffix dnodes (dnodes beyond the first).
 */
static natural
ivector_total_size_and_suffix(LispObj header, natural *suffix_dnodes_out)
{
  natural subtag = header_subtag(header);
  natural element_count = header_element_count(header);
  natural total_size_in_bytes;

  if (subtag <= max_32_bit_ivector_subtag) {
    total_size_in_bytes = 8 + (element_count << 2);
  } else if (subtag <= max_64_bit_ivector_subtag) {
    total_size_in_bytes = 8 + (element_count << 3);
  } else if (subtag <= max_8_bit_ivector_subtag) {
    total_size_in_bytes = 8 + element_count;
  } else if (subtag <= max_16_bit_ivector_subtag) {
    total_size_in_bytes = 8 + (element_count << 1);
  } else if (subtag == subtag_complex_double_float_vector) {
    total_size_in_bytes = 8 + (element_count << 4);
  } else if (subtag == subtag_bit_vector) {
    total_size_in_bytes = 8 + ((element_count + 7) >> 3);
  } else {
    /* Shouldn't happen, but treat as 64-bit */
    total_size_in_bytes = 8 + (element_count << 3);
  }

  if (suffix_dnodes_out) {
    *suffix_dnodes_out = ((total_size_in_bytes + (dnode_size - 1)) >> dnode_shift) - 1;
  }
  return total_size_in_bytes;
}

/*
 * Given the address of an ivector header and the header value,
 * return a pointer past the end of the ivector (dnode-aligned).
 */
LispObj *
skip_over_ivector(natural start, LispObj header)
{
  natural subtag = header_subtag(header);
  natural element_count = header_element_count(header);
  natural nbytes;

  if (subtag <= max_32_bit_ivector_subtag) {
    nbytes = element_count << 2;
  } else if (subtag <= max_64_bit_ivector_subtag) {
    nbytes = element_count << 3;
  } else if (subtag <= max_8_bit_ivector_subtag) {
    nbytes = element_count;
  } else if (subtag <= max_16_bit_ivector_subtag) {
    nbytes = element_count << 1;
  } else if (subtag == subtag_complex_double_float_vector) {
    nbytes = element_count << 4;
  } else if (subtag == subtag_bit_vector) {
    nbytes = (element_count + 7) >> 3;
  } else {
    nbytes = element_count << 3;
  }
  /* start + 8-byte header + nbytes, rounded up to dnode boundary */
  return ptr_from_lispobj(start + ((nbytes + 8 + (dnode_size - 1)) & ~(dnode_size - 1)));
}


/* ================================================================
   Marking
   ================================================================ */

void
mark_root(LispObj n)
{
  int tag_n = fulltag_of(n);
  natural dnode, bits, *bitsp, mask;

  if (!is_node_fulltag(tag_n)) {
    return;
  }

  dnode = gc_area_dnode(n);
  if (dnode >= GCndnodes_in_area) {
    return;
  }
  set_bits_vars(GCmarkbits, dnode, bitsp, bits, mask);
  if (bits & mask) {
    return;
  }
  *bitsp = (bits | mask);

  if (tag_n == tag_cons) {
    /* ARM64 cons: untag gives base+8; base[0]=car, base[1]=cdr
       but we use the car/cdr macros from macros.h */
    rmark(car(n));
    rmark(cdr(n));
    return;
  }

  /* Uvector */
  {
    LispObj *base = ARM64_BASE(n);
    natural
      header = *((natural *)base),
      subtag = header_subtag(header),
      element_count = header_element_count(header),
      suffix_dnodes;

    tag_n = fulltag_of(header);

    if (nodeheader_tag_p(tag_n)) {
      /* gvector — mark suffix dnodes then mark elements */
      suffix_dnodes = ((8 + (element_count << node_shift) + (dnode_size - 1)) >> dnode_shift) - 1;
    } else {
      /* ivector — compute size and mark suffix dnodes, then return */
      ivector_total_size_and_suffix(header, &suffix_dnodes);
    }

    if (suffix_dnodes) {
      set_n_bits(GCmarkbits, dnode + 1, suffix_dnodes);
    }

    if (!nodeheader_tag_p(tag_n)) {
      return;  /* ivector, nothing more to mark */
    }

    if (subtag == subtag_hash_vector) {
      LispObj flags = ((hash_table_vector_header *)base)->flags;
      if (flags & nhash_weak_mask) {
        ((hash_table_vector_header *)base)->cache_key = undefined;
        ((hash_table_vector_header *)base)->cache_value = lisp_nil;
        mark_weak_htabv(n);
        return;
      }
    }

    if (subtag == subtag_pool) {
      deref(n, 1) = lisp_nil;
    }

    if (subtag == subtag_weak) {
      natural weak_type = (natural)base[2];
      if (weak_type >> population_termination_bit) {
        element_count -= 2;
      } else {
        element_count -= 1;
      }
    }

    /* Mark elements in reverse order (high to low) */
    base += (1 + element_count);
    while (element_count--) {
      rmark(*--base);
    }

    if (subtag == subtag_weak) {
      /* Splice onto GCweakvll.
         GCweakvll stores base (header) addresses. */
      deref(n, 1) = GCweakvll;
      GCweakvll = untag(n) - node_size;
    }
  }
}


/*
  mark_ephemeral_root: marks the node if needed; returns true if the
  node is a hash table vector header or a cons/misc-tagged pointer
  to ephemeral space.
*/
Boolean
mark_ephemeral_root(LispObj n)
{
  int tag_n = fulltag_of(n);
  natural eph_dnode;

  if (nodeheader_tag_p(tag_n)) {
    return (header_subtag(n) == subtag_hash_vector);
  }

  if (is_node_fulltag(tag_n)) {
    eph_dnode = area_dnode(n, GCephemeral_low);
    if (eph_dnode < GCn_ephemeral_dnodes) {
      mark_root(n);
      return true;
    }
  }
  return false;
}


/*
  ARM64 has no separate code vectors or PC locatives.
  The entrypoint is stored in gvector slot 1 as a fixnum-tagged locative.
  We don't need mark_pc_root — all roots are marked via mark_root.
*/


/* ================================================================
   rmark — recursive/link-inversion marker for ARM64

   FSM state encoding (in the tag byte of the "prev" pointer):
     tag_positive_fixnum (0x00): walking vector elements -> ClimbVector
     tag_cons (0x03):            prev saved in cdr       -> ClimbCdr
     RMARK_PREV_CAR (tag_nil=0x02): prev saved in car   -> ClimbCar
     RMARK_PREV_ROOT (tag_unbound=0x12): initial root    -> return

   Tag manipulation:
     MarkCons:  this = untag(this) | ((LispObj)RMARK_PREV_CAR << tag_shift)
     MarkCdr:   this = untag(this) | ((LispObj)tag_cons << tag_shift)
     MarkVector entry:
       this = untag(this) - node_size + ((element_count+1) << node_shift)
       (= base + (ec+1)*8, with tag byte 0x00 = positive fixnum)
     MarkVectorDone:
       reconstruct ref tag from header subtag:
         ref_tag = (htag & ~0x80) | 0x40
       this = (this + node_size) | ((LispObj)ref_tag << tag_shift)
   ================================================================ */

#define RMARK_PREV_ROOT tag_unbound
#define RMARK_PREV_CAR  tag_nil

void
rmark(LispObj n)
{
  int tag_n = fulltag_of(n);
  bitvector markbits = GCmarkbits;
  natural dnode, bits, *bitsp, mask;

  if (!is_node_fulltag(tag_n)) {
    return;
  }

  dnode = gc_area_dnode(n);
  if (dnode >= GCndnodes_in_area) {
    return;
  }
  set_bits_vars(markbits, dnode, bitsp, bits, mask);
  if (bits & mask) {
    return;
  }
  *bitsp = (bits | mask);

  if (current_stack_pointer() > GCstack_limit) {
    /* Enough C stack — use simple recursion */
    if (tag_n == tag_cons) {
      rmark(deref(n, 1));
      rmark(deref(n, 0));
    } else {
      LispObj *base = ARM64_BASE(n);
      natural
        header = *((natural *)base),
        subtag = header_subtag(header),
        element_count = header_element_count(header),
        suffix_dnodes;

      tag_n = fulltag_of(header);

      if (nodeheader_tag_p(tag_n)) {
        suffix_dnodes = ((8 + (element_count << node_shift) + (dnode_size - 1)) >> dnode_shift) - 1;
      } else {
        ivector_total_size_and_suffix(header, &suffix_dnodes);
      }

      if (suffix_dnodes) {
        set_n_bits(GCmarkbits, dnode + 1, suffix_dnodes);
      }

      if (!nodeheader_tag_p(tag_n)) return;

      if (subtag == subtag_hash_vector) {
        LispObj flags = ((hash_table_vector_header *)base)->flags;
        if (flags & nhash_weak_mask) {
          ((hash_table_vector_header *)base)->cache_key = undefined;
          ((hash_table_vector_header *)base)->cache_value = lisp_nil;
          mark_weak_htabv(n);
          return;
        }
      }

      if (subtag == subtag_pool) {
        deref(n, 1) = lisp_nil;
      }

      if (subtag == subtag_weak) {
        natural weak_type = (natural)base[2];
        if (weak_type >> population_termination_bit)
          element_count -= 2;
        else
          element_count -= 1;
      }
      while (element_count) {
        rmark(deref(n, element_count));
        element_count--;
      }

      if (subtag == subtag_weak) {
        deref(n, 1) = GCweakvll;
        GCweakvll = untag(n) - node_size;
      }
    }
  } else {
    /* Low on C stack — use link-inversion FSM */
    LispObj prev = ((LispObj)RMARK_PREV_ROOT << tag_shift);
    LispObj this = n, next;

    if (tag_n == tag_cons) goto MarkCons;
    goto MarkVector;

  ClimbCdr:
    prev = deref(this, 0);
    deref(this, 0) = next;

  Climb:
    next = this;
    this = prev;
    tag_n = fulltag_of(prev);
    if (tag_n == tag_positive_fixnum)
      goto ClimbVector;
    if (tag_n == RMARK_PREV_ROOT)
      return;
    if (tag_n == tag_cons)
      goto ClimbCdr;
    if (tag_n == RMARK_PREV_CAR)
      goto ClimbCar;
    /* Should not reach here */
    return;

  DescendCons:
    prev = this;
    this = next;

  MarkCons:
    /* Mark the car first, then the cdr.
       "this" is a cons-tagged pointer.
       Encode "prev saved in car" by setting tag to RMARK_PREV_CAR */
    next = deref(this, 1);  /* car */
    this = untag(this) | ((LispObj)RMARK_PREV_CAR << tag_shift);
    tag_n = fulltag_of(next);
    if (!is_node_fulltag(tag_n)) goto MarkCdr;
    dnode = gc_area_dnode(next);
    if (dnode >= GCndnodes_in_area) goto MarkCdr;
    set_bits_vars(markbits, dnode, bitsp, bits, mask);
    if (bits & mask) goto MarkCdr;
    *bitsp = (bits | mask);
    deref(this, 1) = prev;
    if (tag_n == tag_cons) goto DescendCons;
    goto DescendVector;

  ClimbCar:
    prev = deref(this, 1);
    deref(this, 1) = next;

  MarkCdr:
    /* Now mark the cdr.
       Encode "prev saved in cdr" by setting tag to tag_cons */
    next = deref(this, 0);  /* cdr */
    this = untag(this) | ((LispObj)tag_cons << tag_shift);
    tag_n = fulltag_of(next);
    if (!is_node_fulltag(tag_n)) goto Climb;
    dnode = gc_area_dnode(next);
    if (dnode >= GCndnodes_in_area) goto Climb;
    set_bits_vars(markbits, dnode, bitsp, bits, mask);
    if (bits & mask) goto Climb;
    *bitsp = (bits | mask);
    deref(this, 0) = prev;
    if (tag_n == tag_cons) goto DescendCons;
    /* fall through */

  DescendVector:
    prev = this;
    this = next;

  MarkVector:
    {
      LispObj *base = ARM64_BASE(this);
      natural
        header = *((natural *)base),
        subtag = header_subtag(header),
        element_count = header_element_count(header),
        suffix_dnodes;

      tag_n = fulltag_of(header);

      if (nodeheader_tag_p(tag_n)) {
        suffix_dnodes = ((8 + (element_count << node_shift) + (dnode_size - 1)) >> dnode_shift) - 1;
      } else {
        ivector_total_size_and_suffix(header, &suffix_dnodes);
      }

      if (suffix_dnodes) {
        set_n_bits(GCmarkbits, dnode + 1, suffix_dnodes);
      }

      if (!nodeheader_tag_p(tag_n)) goto Climb;

      if (subtag == subtag_hash_vector) {
        LispObj flags = ((hash_table_vector_header *)base)->flags;
        if (flags & nhash_weak_mask) {
          ((hash_table_vector_header *)base)->cache_key = undefined;
          ((hash_table_vector_header *)base)->cache_value = lisp_nil;
          dws_mark_weak_htabv(this);
          element_count = hash_table_vector_header_count;
        }
      }

      if (subtag == subtag_pool) {
        deref(this, 1) = lisp_nil;
      }

      if (subtag == subtag_weak) {
        natural weak_type = (natural)base[2];
        if (weak_type >> population_termination_bit)
          element_count -= 2;
        else
          element_count -= 1;
      }

      /* Walk from high element to low.
         Encode as: this = base + (element_count+1)*node_size
         The tag byte will be 0x00 (tag_positive_fixnum) since
         the address is in the low 56 bits with a zero top byte. */
      this = (LispObj)(base) + ((element_count + 1) << node_shift);
      goto MarkVectorLoop;
    }

  ClimbVector:
    prev = *((LispObj *)ptr_from_lispobj(this));
    *((LispObj *)ptr_from_lispobj(this)) = next;

  MarkVectorLoop:
    this -= node_size;
    next = *((LispObj *)ptr_from_lispobj(this));
    tag_n = fulltag_of(next);
    if (nodeheader_tag_p(tag_n)) goto MarkVectorDone;
    if (!is_node_fulltag(tag_n)) goto MarkVectorLoop;
    dnode = gc_area_dnode(next);
    if (dnode >= GCndnodes_in_area) goto MarkVectorLoop;
    set_bits_vars(markbits, dnode, bitsp, bits, mask);
    if (bits & mask) goto MarkVectorLoop;
    *bitsp = (bits | mask);
    *(ptr_from_lispobj(this)) = prev;
    if (tag_n == tag_cons) goto DescendCons;
    goto DescendVector;

  MarkVectorDone:
    /* "next" is the vector header; "this" points at element 0 (= base + node_size).
       Reconstruct the tagged pointer: ref_tag = (header_subtag & ~0x80) | 0x40 */
    {
      natural htag = header_subtag(next);
      natural ref_tag = (htag & ~0x80) | 0x40;
      this = (this + node_size) | ((LispObj)ref_tag << tag_shift);

      if (htag == subtag_weak) {
        deref(this, 1) = GCweakvll;
        GCweakvll = untag(this) - node_size;
      }
    }
    goto Climb;
  }
}


/* ================================================================
   Refmap consistency checking
   ================================================================ */

void
check_refmap_consistency(LispObj *start, LispObj *end, bitvector refbits, bitvector refidx)
{
  LispObj x1, *base = start, *prev = start;
  int tag;
  natural ref_dnode, node_dnode;
  Boolean intergen_ref, lenient_next_dnode = false, lenient_this_dnode = false;

  while (start < end) {
    x1 = *start;
    tag = fulltag_of(x1);
    if (immheader_tag_p(tag)) {
      prev = start;
      start = skip_over_ivector(ptr_to_lispobj(start), x1);
    } else {
      if (nodeheader_tag_p(tag)) {
        prev = start;
      }
      intergen_ref = false;
      if (header_subtag(x1) == subtag_weak) {
        lenient_next_dnode = true;
      }
      if (is_node_fulltag(tag)) {
        node_dnode = gc_area_dnode(x1);
        if (node_dnode < GCndnodes_in_area) {
          intergen_ref = true;
        }
      }
      if (lenient_this_dnode) {
        lenient_this_dnode = false;
      } else {
        if (intergen_ref == false) {
          x1 = start[1];
          tag = fulltag_of(x1);
          if (is_node_fulltag(tag)) {
            node_dnode = gc_area_dnode(x1);
            if (node_dnode < GCndnodes_in_area) {
              intergen_ref = true;
            }
          }
        }
      }
      if (intergen_ref) {
        ref_dnode = area_dnode(start, base);
        if (!ref_bit(refbits, ref_dnode)) {
          Bug(NULL, "Missing memoization in doublenode at 0x" LISP "\n", (LispObj)start);
          set_bit(refbits, ref_dnode);
          if (refidx) {
            set_bit(refidx, ref_dnode >> 8);
          }
        } else {
          if (refidx) {
            if (!ref_bit(refidx, ref_dnode >> 8)) {
              Bug(NULL, "Memoization for doublenode at 0x" LISP " not indexed\n", (LispObj)start);
              set_bit(refidx, ref_dnode >> 8);
            }
          }
        }
      }
      start += 2;
      if (lenient_next_dnode) {
        lenient_this_dnode = true;
      }
      lenient_next_dnode = false;
    }
  }
}


/* ================================================================
   mark_simple_area_range — mark nodes in a contiguous heap range.
   "start" points at the beginning of the range (header addresses).
   ================================================================ */

void
mark_simple_area_range(LispObj *start, LispObj *end)
{
  LispObj x1, *base;
  int tag;

  while (start < end) {
    x1 = *start;
    tag = fulltag_of(x1);
    if (immheader_tag_p(tag)) {
      start = (LispObj *)ptr_from_lispobj(skip_over_ivector(ptr_to_lispobj(start), x1));
    } else if (!nodeheader_tag_p(tag)) {
      /* Cons pair or unheadered pair of nodes */
      ++start;
      mark_root(x1);
      mark_root(*start++);
    } else {
      int subtag = header_subtag(x1);
      natural element_count = header_element_count(x1);
      natural size = (element_count + 1 + 1) & ~1;

      if (subtag == subtag_hash_vector) {
        LispObj flags = ((hash_table_vector_header *)start)->flags;
        if (flags & nhash_weak_mask) {
          ((hash_table_vector_header *)start)->cache_key = undefined;
          ((hash_table_vector_header *)start)->cache_value = lisp_nil;
          /* mark_weak_htabv expects a tagged pointer on ARM32.
             On ARM64, start is the header address (base).
             We pass it as-is since mark_weak_htabv in gc-common.c
             will need ARM64 patching — for now, pass the base address. */
          mark_weak_htabv((LispObj)start);
          element_count = 0;
        }
      }
      if (subtag == subtag_pool) {
        start[1] = lisp_nil;
      }

      if (subtag == subtag_weak) {
        natural weak_type = (natural)start[2];
        if (weak_type >> population_termination_bit)
          element_count -= 2;
        else
          element_count -= 1;
        /* GCweakvll stores base (header) addresses */
        start[1] = GCweakvll;
        GCweakvll = ptr_to_lispobj(start);
      }

      base = start + element_count + 1;
      while (element_count--) {
        mark_root(*--base);
      }
      start += size;
    }
  }
}


/* ================================================================
   Stack area marking
   ================================================================ */

/* ARM64 temp stacks have no lisp data to mark */
void
mark_tstack_area(area *a)
{
}

/*
  vstacks are just treated as a "simple area range", possibly with
  an extra word at the top (where the area's active pointer points).
*/
void
mark_vstack_area(area *a)
{
  LispObj
    *start = (LispObj *)a->active,
    *end = (LispObj *)a->high;

  if (((natural)start) & (sizeof(natural))) {
    mark_root(*start);
    ++start;
  }
  mark_simple_area_range(start, end);
}

/*
  ARM64 has no lisp frame markers on the control stack.
  No lisp objects to mark.
*/
void
mark_cstack_area(area *a)
{
}


/* ================================================================
   Exception context marking
   ================================================================ */

void
mark_xp(ExceptionInformation *xp)
{
  natural *regs = (natural *)xpGPRvector(xp);
  int r;

  /* Node registers: rnil (x6) through save7 (x23) */
  for (r = rnil; r <= save7; r++) {
    mark_root(regs[r]);
  }
  /* ARM64: PC and LR are raw code addresses, not tagged lisp objects.
     No mark_pc_root needed. */
}


/* ================================================================
   Relocation table and forwarding

   A "pagelet" contains 64 doublewords on 64-bit platforms.
   The relocation table contains a word for each pagelet which
   defines the lowest address to which dnodes on that pagelet
   will be relocated.
   ================================================================ */

LispObj
calculate_relocation()
{
  LispObj *relocptr = GCrelocptr;
  LispObj current = GCareadynamiclow;
  bitvector markbits = GCdynamic_markbits;
  qnode *q = (qnode *)markbits;
  natural npagelets = ((GCndynamic_dnodes_in_area + (nbits_in_word - 1)) >> bitmap_shift);
  natural thesebits;
  LispObj first = 0;

  do {
    *relocptr++ = current;
    thesebits = *markbits++;
    if (thesebits == ALL_ONES) {
      current += nbits_in_word * dnode_size;
      q += (nbits_in_word / (sizeof(qnode) * 8));
    } else {
      if (!first) {
        first = current;
        while (thesebits & BIT0_MASK) {
          first += dnode_size;
          thesebits += thesebits;
        }
      }
      current += one_bits(*q++);
      current += one_bits(*q++);
      current += one_bits(*q++);
      current += one_bits(*q++);
    }
  } while (--npagelets);
  *relocptr++ = current;
  return first ? first : current;
}


/*
  dnode_forwarding_address — x86-64 "quicker, dirtier" algorithm.
  On ARM64 with TBI, the tag goes into the high byte:
    new = GCrelocptr[pagelet] | ((LispObj)tag_n << tag_shift)
*/
LispObj
dnode_forwarding_address(natural dnode, int tag_n)
{
  natural pagelet, nbits, marked;
  LispObj new;

  if (GCDebug) {
    if (!ref_bit(GCdynamic_markbits, dnode)) {
      Bug(NULL, "unmarked object being forwarded!\n");
    }
  }

  pagelet = dnode >> bitmap_shift;
  nbits = dnode & bitmap_shift_count_mask;
  new = GCrelocptr[pagelet] | ((LispObj)tag_n << tag_shift);
  if (nbits) {
    marked = (GCdynamic_markbits[dnode >> bitmap_shift]) >> (64 - nbits);
    while (marked) {
      new += one_bits((qnode)marked);
      marked >>= 16;
    }
  }
  return new;
}


LispObj
locative_forwarding_address(LispObj obj)
{
  int tag_n = fulltag_of(obj);
  natural dnode;

  /* Immediates, headers, nil, and fixnums should not be forwarded. */
  if (!is_node_fulltag(tag_n) && tag_n != tag_positive_fixnum) {
    return obj;
  }

  dnode = gc_dynamic_area_dnode(obj);

  if ((dnode >= GCndynamic_dnodes_in_area) ||
      (obj < GCfirstunmarked)) {
    return obj;
  }

  return dnode_forwarding_address(dnode, tag_n);
}


/* ================================================================
   forward_range — update node references in a heap range.

   ARM64 specifics:
   - Function entrypoint (slot 1) is a fixnum-tagged locative:
     use update_locref for it.
   - No subtag_pseudofunction.
   ================================================================ */

void
forward_range(LispObj *range_start, LispObj *range_end)
{
  LispObj *p = range_start, node, new;
  int tag_n, subtag;
  natural nwords;
  hash_table_vector_header *hashp;

  while (p < range_end) {
    node = *p;
    tag_n = fulltag_of(node);
    if (immheader_tag_p(tag_n)) {
      p = (LispObj *)skip_over_ivector((natural)p, node);
    } else if (nodeheader_tag_p(tag_n)) {
      nwords = header_element_count(node);
      nwords += (1 - (nwords & 1));
      if ((header_subtag(node) == subtag_hash_vector) &&
          ((((hash_table_vector_header *)p)->flags) & nhash_track_keys_mask)) {
        natural skip = (sizeof(hash_table_vector_header) / sizeof(LispObj)) - 1;
        hashp = (hash_table_vector_header *)p;
        p++;
        nwords -= skip;
        while (skip--) {
          update_noderef(p);
          p++;
        }
        /* nwords is odd: (floor nwords 2) key/value pairs + alignment word */
        nwords >>= 1;
        while (nwords--) {
          if (update_noderef(p) && hashp) {
            hashp->flags |= nhash_key_moved_mask;
            hashp = NULL;
          }
          p++;
          update_noderef(p);
          p++;
        }
        *p++ = 0;
      } else {
        p++;
        subtag = header_subtag(node);
        if (subtag == subtag_function) {
          /* Slot 1 = entrypoint (fixnum-tagged locative) */
          update_locref(p);
          p++;
          nwords--;
        }
        while (nwords--) {
          update_noderef(p);
          p++;
        }
      }
    } else {
      /* Cons pair */
      new = node_forwarding_address(node);
      if (new != node) {
        *p = new;
      }
      p++;
      update_noderef(p);
      p++;
    }
  }
}


void
forward_tstack_area(area *a)
{
  /* Empty on ARM64 */
}

void
forward_vstack_area(area *a)
{
  LispObj
    *p = (LispObj *)a->active,
    *q = (LispObj *)a->high;

  if (((natural)p) & sizeof(natural)) {
    update_noderef(p);
    p++;
  }
  forward_range(p, q);
}

void
forward_cstack_area(area *a)
{
  /* Empty on ARM64 — no lisp frame markers */
}


void
forward_xp(ExceptionInformation *xp)
{
  natural *regs = (natural *)xpGPRvector(xp);
  int r;

  /* Node registers: rnil (x6) through save7 (x23) */
  for (r = rnil; r <= save7; r++) {
    update_noderef((LispObj *)(&(regs[r])));
  }
  /* PC and LR are raw code addresses on ARM64, not forwarded */
}

void
forward_tcr_xframes(TCR *tcr)
{
  xframe_list *xframes;
  ExceptionInformation *xp;

  xp = tcr->gc_context;
  if (xp) {
    forward_xp(xp);
  }
  for (xframes = tcr->xframe; xframes; xframes = xframes->prev) {
    if (xframes->curr == xp) {
      Bug(NULL, "forward xframe twice ???");
    }
    forward_xp(xframes->curr);
  }
}


/* ================================================================
   compact_dynamic_heap — compact the dynamic heap from
   GCfirstunmarked through its end.
   Returns the LispObj address of the new freeptr.

   ARM64 specifics:
   - 8-byte header, 16-byte dnode.
   - Function entrypoint (slot 1) uses locative_forwarding_address.
   - No subtag_pseudofunction.
   - No code vectors to flush (ARM64 functions are gvectors
     with an entrypoint locative, not separate code vectors).
   ================================================================ */

LispObj
compact_dynamic_heap()
{
  LispObj *src = ptr_from_lispobj(GCfirstunmarked), *dest = src, node, new;
  natural
    elements,
    dnode = gc_area_dnode(GCfirstunmarked),
    node_dnodes = 0,
    imm_dnodes = 0,
    bitidx,
    *bitsp,
    bits,
    nextbit,
    diff;
  int tag, subtag;
  bitvector markbits = GCmarkbits;

  if (dnode < GCndnodes_in_area) {
    lisp_global(FWDNUM) += (1 << fixnum_shift);

    set_bitidx_vars(markbits, dnode, bitsp, bits, bitidx);
    while (dnode < GCndnodes_in_area) {
      if (bits == 0) {
        int remain = nbits_in_word - bitidx;
        dnode += remain;
        src += (remain + remain);
        bits = *++bitsp;
        bitidx = 0;
      } else {
        nextbit = count_leading_zeros(bits);
        if ((diff = (nextbit - bitidx)) != 0) {
          dnode += diff;
          bitidx = nextbit;
          src += (diff + diff);
        }

        if (GCDebug) {
          if (dest != ptr_from_lispobj(locative_forwarding_address(ptr_to_lispobj(src)))) {
            Bug(NULL, "Out of synch in heap compaction.  Forwarding from 0x" LISP " to 0x" LISP
                ",\n expected to go to 0x" LISP "\n",
                (LispObj)src, (LispObj)dest,
                locative_forwarding_address(ptr_to_lispobj(src)));
          }
        }

        node = *src++;
        tag = fulltag_of(node);
        if (nodeheader_tag_p(tag)) {
          elements = header_element_count(node);
          node_dnodes = (elements + 2) >> 1;
          dnode += node_dnodes;
          if ((header_subtag(node) == subtag_hash_vector) &&
              (((hash_table_vector_header *)(src - 1))->flags & nhash_track_keys_mask)) {
            hash_table_vector_header *hashp = (hash_table_vector_header *)dest;
            int skip = (sizeof(hash_table_vector_header) / sizeof(LispObj)) - 1;

            *dest++ = node;
            elements -= skip;
            while (skip--) {
              *dest++ = node_forwarding_address(*src++);
            }
            /* Even number of key/value pairs + alignment word */
            elements >>= 1;
            while (elements--) {
              if (hashp) {
                node = *src++;
                new = node_forwarding_address(node);
                if (new != node) {
                  hashp->flags |= nhash_key_moved_mask;
                  hashp = NULL;
                  *dest++ = new;
                } else {
                  *dest++ = node;
                }
              } else {
                *dest++ = node_forwarding_address(*src++);
              }
              *dest++ = node_forwarding_address(*src++);
            }
            *dest++ = 0;
            src++;
          } else {
            *dest++ = node;
            subtag = header_subtag(node);
            if (subtag == subtag_function) {
              /* Slot 1 = entrypoint locative */
              *dest++ = locative_forwarding_address(*src++);
            } else {
              *dest++ = node_forwarding_address(*src++);
            }
            while (--node_dnodes) {
              *dest++ = node_forwarding_address(*src++);
              *dest++ = node_forwarding_address(*src++);
            }
          }
          set_bitidx_vars(markbits, dnode, bitsp, bits, bitidx);
        } else if (immheader_tag_p(tag)) {
          *dest++ = node;
          *dest++ = *src++;
          elements = header_element_count(node);
          subtag = header_subtag(node);

          if (subtag <= max_32_bit_ivector_subtag) {
            imm_dnodes = (((elements << 2) + 8 + (dnode_size - 1)) >> dnode_shift);
          } else if (subtag <= max_64_bit_ivector_subtag) {
            imm_dnodes = (((elements << 3) + 8 + (dnode_size - 1)) >> dnode_shift);
          } else if (subtag <= max_8_bit_ivector_subtag) {
            imm_dnodes = ((elements + 8 + (dnode_size - 1)) >> dnode_shift);
          } else if (subtag <= max_16_bit_ivector_subtag) {
            imm_dnodes = (((elements << 1) + 8 + (dnode_size - 1)) >> dnode_shift);
          } else if (subtag == subtag_bit_vector) {
            imm_dnodes = ((((elements + 7) >> 3) + 8 + (dnode_size - 1)) >> dnode_shift);
          } else if (subtag == subtag_complex_double_float_vector) {
            imm_dnodes = (((elements << 4) + 8 + (dnode_size - 1)) >> dnode_shift);
          } else {
            imm_dnodes = (((elements << 3) + 8 + (dnode_size - 1)) >> dnode_shift);
          }
          dnode += imm_dnodes;
          /* Already copied header dnode (2 words); copy remaining */
          imm_dnodes--;  /* subtract the header dnode */
          while (imm_dnodes--) {
            *dest++ = *src++;
            *dest++ = *src++;
          }
          set_bitidx_vars(markbits, dnode, bitsp, bits, bitidx);
        } else {
          /* Cons pair */
          *dest++ = node_forwarding_address(node);
          *dest++ = node_forwarding_address(*src++);
          bits &= ~(BIT0_MASK >> bitidx);
          dnode++;
          bitidx++;
        }
      }
    }
  }
  return ptr_to_lispobj(dest);
}


/*
  Total the (physical) byte sizes of all ivectors in the indicated memory range.
*/
natural
unboxed_bytes_in_range(LispObj *start, LispObj *end)
{
  natural total = 0, elements, tag, subtag, bytes;
  LispObj header;

  while (start < end) {
    header = *start;
    tag = fulltag_of(header);

    if (nodeheader_tag_p(tag) || immheader_tag_p(tag)) {
      elements = header_element_count(header);
      if (nodeheader_tag_p(tag)) {
        start += ((elements + 2) & ~1);
      } else {
        subtag = header_subtag(header);

        if (subtag <= max_32_bit_ivector_subtag) {
          bytes = 8 + (elements << 2);
        } else if (subtag <= max_64_bit_ivector_subtag) {
          bytes = 8 + (elements << 3);
        } else if (subtag <= max_8_bit_ivector_subtag) {
          bytes = 8 + elements;
        } else if (subtag <= max_16_bit_ivector_subtag) {
          bytes = 8 + (elements << 1);
        } else if (subtag == subtag_complex_double_float_vector) {
          bytes = 8 + (elements << 4);
        } else if (subtag == subtag_bit_vector) {
          bytes = 8 + ((elements + 7) >> 3);
        } else {
          bytes = 8 + (elements << 3);
        }

        bytes = (bytes + dnode_size - 1) & ~(dnode_size - 1);
        total += bytes;
        start += (bytes >> node_shift);
      }
    } else {
      start += 2;
    }
  }
  return total;
}


/* ================================================================
   Purification — move ivectors to the readonly area.

   ARM64 TBI specifics:
   - untag(obj) = base + node_size, so base = untag(obj) - node_size.
   - Tagged pointer from base: ((LispObj)(base+1)) | ((LispObj)ref_tag << tag_shift)
   - No separate code vectors; function entrypoints are fixnum-tagged
     locatives in gvector slot 1.
   - No subtag_pseudofunction.
   ================================================================ */

/*
  purify_displaced_object: copy an ivector to the destination area.
  Returns the new tagged pointer with displacement 'disp'.
*/
LispObj
purify_displaced_object(LispObj obj, area *dest, natural disp)
{
  BytePtr
    free = dest->active,
    *old = (BytePtr *)ptr_from_lispobj(untag(obj) - node_size);
  LispObj
    header = header_of(obj),
    new;
  natural
    start = (natural)old,
    physbytes;

  physbytes = ((natural)(skip_over_ivector(start, header))) - start;
  dest->active += physbytes;

  new = ptr_to_lispobj(free) + disp;

  memcpy(free, (BytePtr)old, physbytes);
  /* Leave forwarding breadcrumbs at every dnode in the old space */
  while (physbytes) {
    *old++ = (BytePtr)forward_marker;
    *old++ = (BytePtr)free;
    free += dnode_size;
    physbytes -= dnode_size;
  }
  return new;
}

LispObj
purify_object(LispObj obj, area *dest)
{
  /* On ARM64, the "displacement" is the full tag:
     the tagged pointer's top byte encodes the tag. */
  return purify_displaced_object(obj, dest, fulltag_of(obj));
}


/*
  copy_ivector_reference: if *ref is a uvector-tagged pointer into
  [low, high), copy the ivector to dest and update *ref.
  On ARM64, we check for any gvector ref tag (is_node_fulltag but not cons).
*/
void
copy_ivector_reference(LispObj *ref, BytePtr low, BytePtr high, area *dest)
{
  LispObj obj = *ref, header;
  natural tag = fulltag_of(obj), header_tag;

  if (is_node_fulltag(tag) && (tag != tag_cons) &&
      (((BytePtr)ptr_from_lispobj(untag(obj))) > low) &&
      (((BytePtr)ptr_from_lispobj(untag(obj))) < high)) {
    header = deref(obj, 0);
    if (header == forward_marker) {
      /* Already copied.  Reconstruct tagged pointer from breadcrumb.
         deref(obj,1) is the new base address. */
      LispObj new_base = deref(obj, 1);
      *ref = (new_base + node_size) | ((LispObj)tag << tag_shift);
    } else {
      header_tag = fulltag_of(header);
      if (immheader_tag_p(header_tag)) {
        if (header_subtag(header) != subtag_macptr) {
          *ref = purify_object(obj, dest);
        }
      }
    }
  }
}


void
purify_range(LispObj *start, LispObj *end, BytePtr low, BytePtr high, area *to)
{
  LispObj header;
  unsigned tag, subtag;

  while (start < end) {
    header = *start;
    if (header == forward_marker) {
      start += 2;
    } else {
      tag = fulltag_of(header);
      if (immheader_tag_p(tag)) {
        start = (LispObj *)skip_over_ivector((natural)start, header);
      } else {
        if (!nodeheader_tag_p(tag)) {
          copy_ivector_reference(start, low, high, to);
        }
        start++;
        subtag = header_subtag(header);
        if (subtag == subtag_function) {
          /* Entrypoint in slot 1 is a fixnum-tagged locative.
             On ARM64 we treat it like a regular node for purification
             since there are no separate code vectors to purify. */
          copy_ivector_reference(start, low, high, to);
        } else {
          copy_ivector_reference(start, low, high, to);
        }
        start++;
      }
    }
  }
}


void
purify_vstack_area(area *a, BytePtr low, BytePtr high, area *to)
{
  LispObj
    *p = (LispObj *)a->active,
    *q = (LispObj *)a->high;

  if (((natural)p) & sizeof(natural)) {
    copy_ivector_reference(p, low, high, to);
    p++;
  }
  purify_range(p, q, low, high, to);
}


void
purify_cstack_area(area *a, BytePtr low, BytePtr high, area *to)
{
  /* Empty on ARM64 — no lisp frame markers on cstack */
}


void
purify_xp(ExceptionInformation *xp, BytePtr low, BytePtr high, area *to)
{
  natural *regs = (natural *)xpGPRvector(xp);
  int r;

  for (r = rnil; r <= save7; r++) {
    copy_ivector_reference((LispObj *)(&(regs[r])), low, high, to);
  }
  /* PC and LR are raw addresses on ARM64, not purified */
}


void
purify_tcr_tlb(TCR *tcr, BytePtr low, BytePtr high, area *to)
{
  natural n = tcr->tlb_limit;
  LispObj *start = tcr->tlb_pointer, *end = (LispObj *)((BytePtr)start + n);

  purify_range(start, end, low, high, to);
}

void
purify_tcr_xframes(TCR *tcr, BytePtr low, BytePtr high, area *to)
{
  xframe_list *xframes;
  ExceptionInformation *xp;

  xp = tcr->gc_context;
  if (xp) {
    purify_xp(xp, low, high, to);
  }

  for (xframes = tcr->xframe; xframes; xframes = xframes->prev) {
    purify_xp(xframes->curr, low, high, to);
  }
}

void
purify_gcable_ptrs(BytePtr low, BytePtr high, area *to)
{
  LispObj *prev = &(lisp_global(GCABLE_POINTERS)), next;

  while ((*prev) != (LispObj)NULL) {
    copy_ivector_reference(prev, low, high, to);
    next = *prev;
    prev = &(((xmacptr *)ptr_from_lispobj(untag(next) - node_size))->link);
  }
}


void
purify_areas(BytePtr low, BytePtr high, area *target)
{
  area *next_area;
  area_code code;

  for (next_area = active_dynamic_area; (code = next_area->code) != AREA_VOID; next_area = next_area->succ) {
    switch (code) {
    case AREA_VSTACK:
      purify_vstack_area(next_area, low, high, target);
      break;

    case AREA_CSTACK:
      purify_cstack_area(next_area, low, high, target);
      break;

    case AREA_STATIC:
    case AREA_DYNAMIC:
      purify_range((LispObj *)next_area->low, (LispObj *)next_area->active, low, high, target);
      break;

    default:
      break;
    }
  }
}


signed_natural
purify(TCR *tcr, signed_natural param)
{
  extern area *extend_readonly_area(unsigned);
  area
    *a = active_dynamic_area,
    *new_pure_area;
  TCR *other_tcr;
  natural max_pure_size;
  BytePtr new_pure_start;

  max_pure_size = unboxed_bytes_in_range(
    (LispObj *)(a->low + (static_dnodes_for_area(a) << dnode_shift)),
    (LispObj *)a->active);
  new_pure_area = extend_readonly_area(max_pure_size);
  if (new_pure_area) {
    new_pure_start = new_pure_area->active;
    lisp_global(IN_GC) = (1 << fixnumshift);

    purify_areas(a->low, a->active, new_pure_area);

    other_tcr = tcr;
    do {
      purify_tcr_xframes(other_tcr, a->low, a->active, new_pure_area);
      purify_tcr_tlb(other_tcr, a->low, a->active, new_pure_area);
      other_tcr = other_tcr->next;
    } while (other_tcr != tcr);

    purify_gcable_ptrs(a->low, a->active, new_pure_area);

    {
      natural puresize = (natural)(new_pure_area->active - new_pure_start);
      if (puresize != 0) {
        xMakeDataExecutable(new_pure_start, puresize);
      }
    }
    ProtectMemory(new_pure_area->low,
                  align_to_power_of_2(new_pure_area->active - new_pure_area->low,
                                      log2_page_size));
    lisp_global(IN_GC) = 0;
    just_purified_p = true;
    return 0;
  }
  return -1;
}


/* ================================================================
   Impurification — move readonly ivectors back to dynamic space.
   ================================================================ */

void
impurify_noderef(LispObj *p, LispObj low, LispObj high, int delta)
{
  LispObj q = *p;

  /* On ARM64, check for any node fulltag (cons or uvector ref) */
  if (is_node_fulltag(fulltag_of(q)) &&
      (untag(q) >= low) &&
      (untag(q) < high)) {
    /* Add delta to the untagged address, preserve tag */
    *p = (untag(q) + delta) | ((LispObj)fulltag_of(q) << tag_shift);
  }
}


void
impurify_range(LispObj *start, LispObj *end, LispObj low, LispObj high, int delta)
{
  LispObj header;
  unsigned tag, subtag;

  while (start < end) {
    header = *start;
    tag = fulltag_of(header);
    if (immheader_tag_p(tag)) {
      start = (LispObj *)skip_over_ivector((natural)start, header);
    } else {
      if (!nodeheader_tag_p(tag)) {
        impurify_noderef(start, low, high, delta);
      }
      start++;
      subtag = header_subtag(header);
      if (subtag == subtag_function) {
        /* Entrypoint is a fixnum-tagged locative — treat as noderef */
        impurify_noderef(start, low, high, delta);
      } else {
        impurify_noderef(start, low, high, delta);
      }
      start++;
    }
  }
}


void
impurify_xp(ExceptionInformation *xp, LispObj low, LispObj high, int delta)
{
  natural *regs = (natural *)xpGPRvector(xp);
  int r;

  for (r = rnil; r <= save7; r++) {
    impurify_noderef((LispObj *)(&(regs[r])), low, high, delta);
  }
  /* PC and LR are raw addresses on ARM64 */
}


void
impurify_cstack_area(area *a, LispObj low, LispObj high, int delta)
{
  /* Empty on ARM64 */
}


void
impurify_vstack_area(area *a, LispObj low, LispObj high, int delta)
{
  LispObj
    *p = (LispObj *)a->active,
    *q = (LispObj *)a->high;

  if (((natural)p) & sizeof(natural)) {
    impurify_noderef(p, low, high, delta);
    p++;
  }
  impurify_range(p, q, low, high, delta);
}


void
impurify_tcr_tlb(TCR *tcr, LispObj low, LispObj high, int delta)
{
  natural n = tcr->tlb_limit;
  LispObj *start = tcr->tlb_pointer, *end = (LispObj *)((BytePtr)start + n);

  impurify_range(start, end, low, high, delta);
}

void
impurify_tcr_xframes(TCR *tcr, LispObj low, LispObj high, int delta)
{
  xframe_list *xframes;
  ExceptionInformation *xp;

  xp = tcr->gc_context;
  if (xp) {
    impurify_xp(xp, low, high, delta);
  }

  for (xframes = tcr->xframe; xframes; xframes = xframes->prev) {
    impurify_xp(xframes->curr, low, high, delta);
  }
}


void
impurify_areas(LispObj low, LispObj high, int delta)
{
  area *next_area;
  area_code code;

  for (next_area = active_dynamic_area; (code = next_area->code) != AREA_VOID; next_area = next_area->succ) {
    switch (code) {
    case AREA_VSTACK:
      impurify_vstack_area(next_area, low, high, delta);
      break;

    case AREA_CSTACK:
      impurify_cstack_area(next_area, low, high, delta);
      break;

    case AREA_STATIC:
    case AREA_DYNAMIC:
      impurify_range((LispObj *)next_area->low, (LispObj *)next_area->active, low, high, delta);
      break;

    default:
      break;
    }
  }
}


void
impurify_gcable_ptrs(LispObj low, LispObj high, signed_natural delta)
{
  LispObj *prev = &(lisp_global(GCABLE_POINTERS)), next;

  while ((*prev) != (LispObj)NULL) {
    impurify_noderef(prev, low, high, delta);
    next = *prev;
    prev = &(((xmacptr *)ptr_from_lispobj(untag(next) - node_size))->link);
  }
}


signed_natural
impurify(TCR *tcr, signed_natural param)
{
  area *r = readonly_area;

  if (r) {
    area *a = active_dynamic_area;
    BytePtr ro_base = r->low, ro_limit = r->active, oldfree = a->active,
      oldhigh = a->high, newhigh;
    natural n = ro_limit - ro_base;
    signed_natural delta = oldfree - ro_base;
    TCR *other_tcr;

    if (n) {
      lisp_global(IN_GC) = 1;
      newhigh = (BytePtr)(align_to_power_of_2(oldfree + n,
                                               log2_heap_segment_size));
      if (newhigh > oldhigh) {
        grow_dynamic_area(newhigh - oldhigh);
      }
      a->active += n;
      memmove(oldfree, ro_base, n);
      UnCommitMemory(ro_base, n);
      a->ndnodes = area_dnode(a->active, a->low);
      pure_space_active = r->active = r->low;
      r->ndnodes = 0;

      impurify_areas(ptr_to_lispobj(ro_base), ptr_to_lispobj(ro_limit), delta);

      other_tcr = tcr;
      do {
        impurify_tcr_xframes(other_tcr, ptr_to_lispobj(ro_base), ptr_to_lispobj(ro_limit), delta);
        impurify_tcr_tlb(other_tcr, ptr_to_lispobj(ro_base), ptr_to_lispobj(ro_limit), delta);
        other_tcr = other_tcr->next;
      } while (other_tcr != tcr);

      impurify_gcable_ptrs(ptr_to_lispobj(ro_base), ptr_to_lispobj(ro_limit), delta);
      lisp_global(IN_GC) = 0;
    }
    return 0;
  }
  return -1;
}
