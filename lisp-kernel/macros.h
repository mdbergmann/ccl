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

/* Totally different content than 'macros.s' */



#ifndef __macros__
#define __macros__

#ifdef ARM64
/* ================================================================
 * ARM64 TBI Tagging Overrides
 * ================================================================
 * ARM64 uses Top Byte Ignore: type tags occupy bits 56-63 of a
 * 64-bit pointer.  The standard low-bit extraction macros used by
 * all other architectures are WRONG for ARM64 and must be overridden.
 *
 * Header layout (in memory):
 *   bits 56-63: subtag byte (object type)
 *   bits  0-55: element count
 *
 * Tagged pointer layout:
 *   bits 56-63: tag byte (encodes type)
 *   bits  0-55: effective address (= object base + node_size)
 * ================================================================ */

#define ptr_to_lispobj(p) ((LispObj)(p))
#define ptr_from_lispobj(o) ((LispObj*)(o))

/* Lisp-tagged registers: x6 (rnil) through x23 (save7) */
#define lisp_reg_p(reg) ((reg) >= rnil && (reg) <= save7)

/* Tag extraction: high byte */
#undef tag_of  /* arm64-constants.h may have defined this */
#define fulltag_of(o)  (((natural)(o)) >> 56)
#define tag_of(o)      fulltag_of(o)

/* Clear tag: mask to low 56 bits */
#define untag(o)       ((natural)(o) & 0x00FFFFFFFFFFFFFFLL)
#define node_aligned(o) untag(o)
#define indirect_node(o) (*(LispObj *)(node_aligned(o)))

/* Tagged pointers point to base + node_size (past header).
   deref(o,0) returns the header at the object base. */
#define deref(o,n) ((((LispObj*)(untag((LispObj)(o)) - node_size)))[(n)])
#define header_of(o) deref(o,0)

/* Headers: subtag in high byte, element count in low 56 bits */
#define header_subtag(h) ((natural)(h) >> 56)
#define header_element_count(h) ((h) & 0x00FFFFFFFFFFFFFFLL)
#define make_header(subtag,element_count) (((LispObj)(subtag) << 56) | (element_count))

/* fixnumshift = 0 on ARM64, so unbox/box are trivial casts */
#define unbox_fixnum(x) ((signed_natural)(x))
#define box_fixnum(x)   ((LispObj)(signed_natural)(x))

/* Cons access: untag gives base+node_size, subtract to get struct base */
#define car(x) (((cons *)ptr_from_lispobj(untag(x) - node_size))->car)
#define cdr(x) (((cons *)ptr_from_lispobj(untag(x) - node_size))->cdr)

/* "sym" is an untagged pointer to a symbol (= base + node_size) */
#define BOUNDP(sym)  ((((lispsymbol *)((char*)(sym) - node_size))->vcell) != undefined)
#define FBOUNDP(sym) ((((lispsymbol *)((char*)(sym) - node_size))->fcell) != nrs_UDF.vcell)

/* Node headers: bits 7 AND 5 set (gvector headers: 0xA0-0xBF) */
#define nodeheader_tag_p(tag) (((tag) & 0xA0) == 0xA0)
/* Imm headers: bit 7 set, bit 5 clear (ivector headers: 0x80-0x9F) */
#define immheader_tag_p(tag)  (((tag) & 0xA0) == 0x80)

#else /* !ARM64 — all other architectures */

#define ptr_to_lispobj(p) ((LispObj)(p))
#define ptr_from_lispobj(o) ((LispObj*)(o))
#define lisp_reg_p(reg)  ((reg) >= fn)

#define fulltag_of(o)  ((o) & fulltagmask)
#define tag_of(o) ((o) & tagmask)
#define untag(o) ((o) & ~fulltagmask)
#define node_aligned(o) ((o) & ~tagmask)
#define indirect_node(o) (*(LispObj *)(node_aligned(o)))

#define deref(o,n) ((((LispObj*) (untag((LispObj)o))))[(n)])
#define header_of(o) deref(o,0)

#define header_subtag(h) ((h) & subtagmask)
#define header_element_count(h) ((h) >> num_subtag_bits)
#define make_header(subtag,element_count) ((subtag)|((element_count)<<num_subtag_bits))

#define unbox_fixnum(x) ((signed_natural)(((signed_natural)(x))>>fixnum_shift))
#define box_fixnum(x) ((LispObj)((signed_natural)(x)<<fixnum_shift))

#define car(x) (((cons *)ptr_from_lispobj(untag(x)))->car)
#define cdr(x) (((cons *)ptr_from_lispobj(untag(x)))->cdr)

/* "sym" is an untagged pointer to a symbol */
#define BOUNDP(sym)  ((((lispsymbol *)(sym))->vcell) != undefined)

/* Likewise. */
#define FBOUNDP(sym) ((((lispsymbol *)(sym))->fcell) != nrs_UDF.vcell)

#ifdef PPC
#ifdef PPC64
#define nodeheader_tag_p(tag) (((tag) & lowtag_mask) == lowtag_nodeheader)
#define immheader_tag_p(tag) (((tag) & lowtag_mask) == lowtag_immheader)
#else
#define nodeheader_tag_p(tag) (tag == fulltag_nodeheader)
#define immheader_tag_p(tag) (tag == fulltag_immheader)
#endif
#endif

#ifdef X86
#ifdef X8664
#define NODEHEADER_MASK ((1<<(fulltag_nodeheader_0)) | \
			 (1<<(fulltag_nodeheader_1)))
#define nodeheader_tag_p(tag) ((1<<(tag)) &  NODEHEADER_MASK)

#define IMMHEADER_MASK ((1<<fulltag_immheader_0) | \
			(1UL<<fulltag_immheader_1) |			\
			(1UL<<fulltag_immheader_2))

#define immheader_tag_p(tag) ((1<<(tag)) & IMMHEADER_MASK)
#else
#define nodeheader_tag_p(tag) (tag == fulltag_nodeheader)
#define immheader_tag_p(tag) (tag == fulltag_immheader)
#endif
#endif

#ifdef ARM
#define nodeheader_tag_p(tag) (tag == fulltag_nodeheader)
#define immheader_tag_p(tag) (tag == fulltag_immheader)
#endif

#endif /* !ARM64 */

#ifdef VC
#define inline
#define __attribute__(x)
#endif

/* lfuns */
#define lfun_bits(f) (deref(f,header_element_count(header_of(f))))
#define named_function_p(f) (!(lfun_bits(f)&(1<<(29+fixnum_shift))))
#define named_function_name(f) (deref(f,-1+header_element_count(header_of(f))))

#define TCR_INTERRUPT_LEVEL(tcr) \
  (((signed_natural *)((tcr)->tlb_pointer))[INTERRUPT_LEVEL_BINDING_INDEX])

#ifdef WINDOWS
#define LSEEK(fd,offset,how) _lseeki64(fd,offset,how)
#else
#define LSEEK(fd,offset,how) lseek(fd,offset,how)
#endif

/* We can't easily and unconditionally use format strings like "0x%lx"
   to print lisp objects: the "l" might not match the word size, and
   neither would (necessarily) something like "0x%llx".  We can at
   least exploit the fact that on all current platforms, "ll" ("long long")
   is the size of a 64-bit lisp object and "l" ("long") is the size of
   a 32-bit lisp object. */

#if (WORD_SIZE == 64)
#define LISP "%llx"
#define ZLISP "%016llx"
#define DECIMAL "%lld"
#else
#define LISP "%lx"
#define ZLISP "%08x"
#define DECIMAL "%ld"
#endif

#ifdef WIN_32
#define TCR_AUX(tcr) tcr->aux
#else
#define TCR_AUX(tcr) tcr
#endif
#endif /* __macros__ */
