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

#ifndef __ARM64_CONSTANTS_H__
#define __ARM64_CONSTANTS_H__

#include "constants.h"

/* ================================================================
   Section 1: Register definitions
   Must match arm64-constants.s lines 16-51 and arm64-arch.lisp.
   ================================================================ */

#define imm0       0
#define imm1       1
#define imm2       2
#define imm3       3
#define imm4       4
#define imm5       5
#define nargs      5
#define rnil       6
#define rt         7
#define rclosure_call 8
#define temp3      9
#define fname      temp3
#define temp2      10
#define nfn        temp2
#define temp1      11
#define temp0      12
#define arg_x      13
#define arg_y      14
#define arg_z      15
#define save0      16
#define save1      17
#define save2      18
#define save3      19
#define save4      20
#define save5      21
#define save6      22
#define save7      23
#define loc_pc     24
#define vsp        25
#define allocptr   26
#define allocbase  27
#define rcontext   28
#define Rfp        29
#define Rlr        30

#define Rfn        nfn
#define nargregs   3

/* ================================================================
   Section 2: Fundamental constants
   From arm64-arch.lisp lines 483-515 and arm64-constants.s lines 55-68.
   ================================================================ */

#define nbits_in_word  64
#define nbits_in_byte  8
#define tag_shift      56

#define num_subtag_bits 8
#define fixnumshift    0
#define fixnum_shift   0

#define ntagbits       8
#define nlisptagbits   8
#define fulltagmask    0xFF
#define subtagmask     0xFF

#define ncharcodebits  8
#define charcode_shift 8

#define node_size      8
#define node_shift     3
#define word_shift     3

#define fixnumone      1
#define fixnum_one     1

/* ================================================================
   Section 3: TBI tag definitions
   From arm64-arch.lisp lines 539-599 and arm64-constants.s lines 75-130.

   ARM64 uses Top Byte Ignore: tags occupy bits 56-63 of a 64-bit
   pointer.  The tag byte space is partitioned as:
     0x00       non-negative fixnum (sign extension of bit 55)
     0x01       overflowed positive fixnum
     0x02       NIL
     0x03       cons
     0x10-0x1F  immediates (single-float, character, markers)
     0x40-0x5F  ivector references (bit 6 set, bit 5 clear)
     0x60-0x7F  gvector references (bit 6 set, bit 5 set)
     0x80-0x9F  ivector headers  (bit 7 set, bit 5 clear)
     0xA0-0xBF  gvector headers  (bit 7 set, bit 5 set)
     0xFE       overflowed negative fixnum
     0xFF       negative fixnum (sign extension of bit 55)
   ================================================================ */

/* Fixnum tags */
#define tag_positive_fixnum  0
#define tag_negative_fixnum  0xFF
#define tag_overflowed_positive_fixnum 1
#define tag_overflowed_negative_fixnum 0xFE

/* List tags */
#define tag_nil   2
#define tag_cons  3

/* Immediate tags — base = 0x10 */
#define imm_tag_mask  0x10
#define tag_single_float  (imm_tag_mask | 0)   /* 0x10 */
#define tag_character     (imm_tag_mask | 1)   /* 0x11 */
#define tag_unbound       (imm_tag_mask | 2)   /* 0x12 */
#define tag_slot_unbound  (imm_tag_mask | 3)   /* 0x13 */
#define tag_no_thread_local_binding (imm_tag_mask | 4)  /* 0x14 */
#define tag_illegal       (imm_tag_mask | 5)   /* 0x15 */
#define tag_stack_alloc   (imm_tag_mask | 6)   /* 0x16 */

/* Uvector tag infrastructure */
#define gvector_tag_bit   5
#define gvector_tag_mask  (1 << gvector_tag_bit)  /* 0x20 */
#define uvector_ref       0x40
#define uvector_header    0x80
#define uvector_mask      (uvector_header | uvector_ref)  /* 0xC0 */
#define cl_ivector_tag_bit 0
#define cl_ivector_mask   (1 << cl_ivector_tag_bit)  /* 0x01 */

/* ================================================================
   Section 4: TBI tag extraction macros
   ARM64-specific macros for extracting the tag byte from a 64-bit value.
   ================================================================ */

#define tag_of(o)          (((natural)(o)) >> tag_shift)
#define is_fixnum(o)       (tag_of(o) == 0 || tag_of(o) == 0xFF)
#define is_immediate(o)    (tag_of(o) & imm_tag_mask)
#define is_cons_tag(t)     ((t) == tag_cons)
#define is_nil_tag(t)      ((t) == tag_nil)
#define is_uvector_ref(t)  ((t) & uvector_ref)
#define is_gvector_ref(t)  (is_uvector_ref(t) && ((t) & gvector_tag_mask))

/* ================================================================
   Section 5: Uvector subtag enum
   From arm64-arch.lisp lines 620-738 and arm64-constants.s lines 131-193.
   The low byte of a uvector header encodes the subtag.
   ================================================================ */

#define define_uvector(name, val) \
  tag_##name = (uvector_ref|(val)), name##_header = (uvector_header|(val))

#define define_ivector(name,val) define_uvector(name,((val)<<1))
#define define_cl_ivector(name,val) define_uvector(name,(((val)<<1)|cl_ivector_mask))
#define define_gvector(name,val) define_uvector(name,((val)|gvector_tag_mask))

enum {
/* 32-bit ivectors */
define_ivector(bignum,0),
define_cl_ivector(s32_vector,0),
define_ivector(double_float,1),
define_cl_ivector(u32_vector,1),
define_ivector(complex_single_float,2),
define_cl_ivector(single_float_vector,2),
define_ivector(complex_double_float,3),
define_cl_ivector(simple_string,3),
define_ivector(xcode_vector,4),
min_32_bit_ivector_header = bignum_header,
max_32_bit_ivector_header = xcode_vector_header,

/* 64-bit ivectors */
define_ivector(macptr,5),
define_cl_ivector(s64_vector,5),
define_ivector(dead_macptr,6),
define_cl_ivector(u64_vector,6),
define_cl_ivector(fixnum_vector,7),
define_cl_ivector(double_float_vector,8),
define_cl_ivector(complex_single_float_vector,9),
min_64_bit_ivector_header = macptr_header,
max_64_bit_ivector_header = complex_single_float_vector_header,

/* 8-bit ivectors */
define_cl_ivector(s8_vector,10),
define_cl_ivector(u8_vector,11),
min_8_bit_ivector_header = s8_vector_header,
max_8_bit_ivector_header = u8_vector_header,

/* 16-bit ivectors */
define_cl_ivector(s16_vector,12),
define_cl_ivector(u16_vector,13),
min_16_bit_ivector_header = s16_vector_header,
max_16_bit_ivector_header = u16_vector_header,

/* Other CL ivectors */
define_cl_ivector(complex_double_float_vector,14),
define_cl_ivector(bit_vector,15),

/* Minimum CL ivector subtag (all CL ivectors have bit 0 set) */
min_cl_ivector_subtag = tag_s32_vector,

/* Gvectors — node-containing heap objects (bit 5 set) */
define_gvector(ratio,0),
define_gvector(complex,1),
define_gvector(function,2),
define_gvector(symbol,3),
define_gvector(catch_frame,4),
define_gvector(basic_stream,5),
define_gvector(lock,6),
define_gvector(hash_vector,7),
define_gvector(pool,8),
define_gvector(weak,9),
define_gvector(package,10),
define_gvector(slot_vector,11),
define_gvector(instance,12),
define_gvector(struct,13),
define_gvector(istruct,14),
define_gvector(value_cell,15),
define_gvector(xfunction,16),
define_gvector(arrayH,29),
define_gvector(vectorH,30),
define_gvector(simple_vector,31)
};

/* Subtag aliases for immediate types */
#define subtag_single_float  tag_single_float
#define subtag_character     tag_character
#define subtag_unbound       tag_unbound
#define subtag_slot_unbound  tag_slot_unbound
#define subtag_no_thread_local_binding tag_no_thread_local_binding
#define subtag_illegal       tag_illegal
#define subtag_stack_alloc_marker tag_stack_alloc

/* Subtag aliases for uvector headers.
   On ARM64, header_subtag() returns the high byte of the header word,
   which matches the *_header enum values.  These aliases allow shared
   code (gc-common.c, image.c, etc.) to use the subtag_* naming. */

/* Ivector (immutable) header subtags */
#define subtag_bignum                       bignum_header
#define subtag_double_float                 double_float_header
#define subtag_complex_single_float         complex_single_float_header
#define subtag_complex_double_float         complex_double_float_header
#define subtag_xcode_vector                 xcode_vector_header
#define subtag_code_vector                  xcode_vector_header  /* compat alias */
#define subtag_macptr                       macptr_header
#define subtag_dead_macptr                  dead_macptr_header
#define subtag_s32_vector                   s32_vector_header
#define subtag_u32_vector                   u32_vector_header
#define subtag_single_float_vector          single_float_vector_header
#define subtag_simple_base_string           simple_string_header /* ARM64 uses simple_string */
#define subtag_fixnum_vector                fixnum_vector_header
#define subtag_s64_vector                   s64_vector_header
#define subtag_u64_vector                   u64_vector_header
#define subtag_double_float_vector          double_float_vector_header
#define subtag_complex_single_float_vector  complex_single_float_vector_header
#define subtag_complex_double_float_vector  complex_double_float_vector_header
#define subtag_s8_vector                    s8_vector_header
#define subtag_u8_vector                    u8_vector_header
#define subtag_s16_vector                   s16_vector_header
#define subtag_u16_vector                   u16_vector_header
#define subtag_bit_vector                   bit_vector_header

/* Gvector (node) header subtags */
#define subtag_ratio           ratio_header
#define subtag_complex         complex_header
#define subtag_function        function_header
#define subtag_symbol          symbol_header
#define subtag_catch_frame     catch_frame_header  /* enum val, before #define shadow */
#define subtag_basic_stream    basic_stream_header
#define subtag_lock            lock_header
#define subtag_hash_vector     hash_vector_header
#define subtag_pool            pool_header
#define subtag_weak            weak_header
#define subtag_package         package_header
#define subtag_slot_vector     slot_vector_header
#define subtag_instance        instance_header
#define subtag_struct          struct_header
#define subtag_istruct         istruct_header
#define subtag_value_cell      value_cell_header
#define subtag_xfunction       xfunction_header
#define subtag_pseudofunction  xfunction_header    /* ARM64 has no pseudofunction */
#define subtag_arrayH          arrayH_header
#define subtag_vectorH         vectorH_header
#define subtag_simple_vector   simple_vector_header
#define subtag_forward_marker  tag_nil

/* Min/max subtag range aliases for ivector size dispatch */
#define min_32_bit_ivector_subtag  min_32_bit_ivector_header
#define max_32_bit_ivector_subtag  max_32_bit_ivector_header
#define min_64_bit_ivector_subtag  min_64_bit_ivector_header
#define max_64_bit_ivector_subtag  max_64_bit_ivector_header
#define min_8_bit_ivector_subtag   min_8_bit_ivector_header
#define max_8_bit_ivector_subtag   max_8_bit_ivector_header
#define min_16_bit_ivector_subtag  min_16_bit_ivector_header
#define max_16_bit_ivector_subtag  max_16_bit_ivector_header
#define min_cl_ivector_subtag      s32_vector_header

/* ================================================================
   Section 5b: Compatibility defines
   ================================================================ */

/* tagmask: same as fulltagmask on ARM64 (8-bit tags) */
#define tagmask fulltagmask

/* fulltag_nil: alias for tag_nil, used by some shared code */
#define fulltag_nil   tag_nil
#define fulltag_cons  tag_cons

/* fulltag_misc: on ARM64, gvector refs serve as the "misc" tag.
   Use the lowest gvector ref tag (0x60) as the canonical value. */
#define fulltag_misc  uvector_ref

/* Rsp: sentinel register number for hardware SP.
   SP is NOT in x0-x30; access via xpSP() in exception contexts. */
#define Rsp  31

/* fixnumshift: alias for fixnum_shift (some code uses this name) */
#ifndef fixnumshift
#define fixnumshift  fixnum_shift
#endif

/* fixnummask: mask for the tag byte — if (val & fixnummask) == 0, it's a non-negative fixnum */
#define fixnummask  ((natural)fulltagmask << tag_shift)

/* dnode alignment */
#define dnode_align_bits 4

/* ================================================================
   Section 6: Marker values
   Full 64-bit marker values — tag byte shifted into bits 56-63.
   From arm64-arch.lisp lines 572-579.
   ================================================================ */

#define unbound_marker        ((LispObj)tag_unbound << tag_shift)
#define slot_unbound_marker   ((LispObj)tag_slot_unbound << tag_shift)
#define slot_unbound          slot_unbound_marker
#define no_thread_local_binding_marker ((LispObj)tag_no_thread_local_binding << tag_shift)
#define illegal_marker        ((LispObj)tag_illegal << tag_shift)
#define stack_alloc_marker    ((LispObj)tag_stack_alloc << tag_shift)
#define undefined             unbound_marker
#define unbound               unbound_marker

/* ================================================================
   Section 7: Offset and bias constants
   From arm64-arch.lisp lines 785-810 and arm64-constants.s lines 195-213.

   In TBI, the bias is uniformly -node_size for all heap objects.
   The tagged pointer's low 56 bits point node_size past the object
   base, so header is at offset -node_size and data starts at 0.
   ================================================================ */

#define misc_bias      node_size            /* = 8, matches Lisp misc-bias */
#define cons_bias      misc_bias
#define function_bias  misc_bias

#define misc_header_offset  (-node_size)        /* = -8 */
#define misc_subtag_offset  (misc_header_offset + (node_size - 1))  /* high byte of header, little-endian */
#define misc_data_offset    0                   /* first data element */
#define misc_dfloat_offset  0                   /* double-floats are 8-byte aligned */

#define max_64_bit_constant_index  0x400
#define max_32_bit_constant_index  0x400
#define max_16_bit_constant_index  0x400
#define max_8_bit_constant_index   0x400
#define max_1_bit_constant_index   0

/* ================================================================
   Section 8: NIL and T values
   From arm64-arch.lisp lines 835-861.

   NIL is at a fixed low-memory address.  The rnil register (x6)
   holds canonical-nil-value: tag_nil in the top byte, effective
   address (nil_base + node_size) in the low 56 bits.
   T is the first nil-relative symbol, one dnode past nil-base.
   ================================================================ */

#define nil_base_address  0x300011000LL
#define nil_value  (((LispObj)tag_nil << tag_shift) | (nil_base_address + node_size))
/* lisp_nil is a C global variable, not a macro — see pmcl-kernel.c */
#define t_offset   dnode_size                   /* = 16 */
#define t_value    (nil_value + t_offset)

#define STATIC_BASE_ADDRESS 0x300010000LL

/* ================================================================
   Section 9: Type structures
   From arm64-arch.lisp lines 864-1018 and arm64-constants.s lines 217-312.

   cons, lispsymbol, ratio, macptr, special_binding, package,
   hash_table_vector_header are already in constants.h (shared).
   ================================================================ */

/* Double-float: header + 2x32-bit elements (8-byte IEEE 754 value).
   Little-endian: low word first. */
typedef struct double_float {
  LispObj header;
  unsigned int value_low;
  unsigned int value_high;
} double_float;

/* Lisp stack frame — 0-based, no marker word (unlike ARM32).
   32 bytes: savevsp, savelr, savefn (nfn=fn on ARM64), savefp (x29). */
typedef struct lisp_frame {
  LispObj savevsp;
  LispObj savelr;
  LispObj savefn;
  LispObj savefp;
} lisp_frame;

/* Catch frame — a gvector allocated on the temp stack.
   14 node-sized fields (matching arm64-arch.lisp catch-frame). */
typedef struct catch_frame {
  LispObj header;
  LispObj catch_tag;            /* #<unbound> -> unwind-protect */
  LispObj _save0;
  LispObj _save1;
  LispObj _save2;
  LispObj _save3;
  LispObj _save4;
  LispObj _save5;
  LispObj _save6;
  LispObj _save7;
  LispObj link;                 /* backpointer to previous catch frame */
  LispObj mvflag;               /* 0 if single-value, fixnum 1 otherwise */
  LispObj db_link;              /* head of special-binding chain */
  LispObj xframe;               /* exception frame chain */
  LispObj last_lisp_frame;      /* from TCR */
} catch_frame;

#define catch_frame_element_count ((sizeof(catch_frame)/sizeof(LispObj))-1)
#define catch_frame_header make_header(subtag_catch_frame,catch_frame_element_count)

/* Exception frame list — same as all architectures. */
typedef struct xframe_list {
  ExceptionInformation *curr;
  struct xframe_list *prev;
} xframe_list;

#define fixnum_bitmask(n)  (1LL<<((n)+fixnumshift))

/* ================================================================
   Section 10: TCR (Thread Context Record)
   Must exactly match arm64-constants.s lines 371-416 and
   arm64-arch.lisp lines 1062-1103.
   43 node-sized slots (0x000-0x150), then padding to 0x180,
   then 256-entry subprims dispatch table (sptab) at 0x180.
   ================================================================ */

#define TCR_BIAS 0

typedef struct tcr {
  struct tcr *prev;                     /* 0x000 */
  struct tcr *next;                     /* 0x008 */
  LispObj single_float_convert;         /* 0x010 float boxing/unboxing */
  struct {                              /* 0x018 */
    unsigned int lisp_fpscr;
    unsigned int lisp_fpscr_low;
  };
  special_binding *db_link;             /* 0x020 special binding chain head */
  LispObj catch_top;                    /* 0x028 top catch frame */
  LispObj *save_vsp;                    /* 0x030 VSP when in foreign code */
  LispObj *save_tsp;                    /* 0x038 TSP when in foreign code */
  struct area *cs_area;                 /* 0x040 cstack area pointer */
  struct area *vs_area;                 /* 0x048 vstack area pointer */
  struct area *ts_area;                 /* 0x050 tstack area pointer */
  LispObj cs_limit;                     /* 0x058 cstack overflow limit */
  unsigned long long bytes_allocated;    /* 0x060 */
  natural log2_allocation_quantum;      /* 0x068 */
  signed_natural interrupt_pending;     /* 0x070 */
  xframe_list *xframe;                  /* 0x078 exception-frame linked list */
  int *errno_loc;                       /* 0x080 per-thread errno location */
  LispObj ffi_exception;                /* 0x088 fpscr bits from ff-call */
  LispObj osid;                         /* 0x090 OS thread id */
  signed_natural valence;               /* 0x098 odd when in foreign code */
  signed_natural foreign_exception_status; /* 0x0A0 */
  void *native_thread_info;             /* 0x0A8 platform-dependent */
  void *native_thread_id;               /* 0x0B0 mach_thread_t, pid_t, etc. */
  void *last_allocptr;                  /* 0x0B8 */
  void *save_allocptr;                  /* 0x0C0 */
  void *save_allocbase;                 /* 0x0C8 */
  void *reset_completion;               /* 0x0D0 */
  void *activate;                       /* 0x0D8 */
  signed_natural suspend_count;         /* 0x0E0 */
  ExceptionInformation *suspend_context;/* 0x0E8 */
  ExceptionInformation *pending_exception_context; /* 0x0F0 */
  void *suspend;                        /* 0x0F8 suspension semaphore */
  void *resume;                         /* 0x100 resumption semaphore */
  struct {                              /* 0x108 */
    unsigned int flags_pad;
    unsigned int flags;
  };
  ExceptionInformation *gc_context;     /* 0x110 */
  void *termination_semaphore;          /* 0x118 */
  signed_natural unwinding;             /* 0x120 */
  natural tlb_limit;                    /* 0x128 */
  LispObj *tlb_pointer;                 /* 0x130 */
  natural shutdown_count;               /* 0x138 */
  void *safe_ref_address;               /* 0x140 */
  LispObj last_lisp_frame;              /* 0x148 when in foreign code */
  void *io_datum;                       /* 0x150 exception port datum (Darwin) */
  LispObj nfp;                          /* 0x158 native frame pointer for unboxed temps */
  LispObj spare[4];                     /* 0x160-0x17F reserved/padding */
  LispObj sptab[256];                   /* 0x180 subprims dispatch table */
} TCR;

/* ================================================================
   Section 11: Heap/memory constants
   ================================================================ */

#define heap_segment_size      0x00020000L
#define log2_heap_segment_size 17L

/* ================================================================
   Section 12: NZCV condition flag masks
   From arm64-constants.s lines 439-442.
   ================================================================ */

#define PSR_N_MASK  (1<<31)
#define PSR_Z_MASK  (1<<30)
#define PSR_C_MASK  (1<<29)
#define PSR_V_MASK  (1<<28)

/* ================================================================
   Section 13: FPCR/FPSR exception bits
   From arm64-arch.lisp lines 1709-1721.
   AArch64 splits the ARM32 FPSCR into FPSR (status) and FPCR (control).
   ================================================================ */

/* FPSR cumulative exception flags (bits 0-4) */
#define FPSR_IOC_BIT  0              /* invalid operation */
#define FPSR_DZC_BIT  1              /* division by zero */
#define FPSR_OFC_BIT  2              /* overflow */
#define FPSR_UFC_BIT  3              /* underflow */
#define FPSR_IXC_BIT  4              /* inexact */

/* FPCR exception enable bits (bits 8-12) */
#define FPCR_IOE_BIT  8              /* invalid operation enable */
#define FPCR_DZE_BIT  9              /* division by zero enable */
#define FPCR_OFE_BIT  10             /* overflow enable */
#define FPCR_UFE_BIT  11             /* underflow enable */
#define FPCR_IXE_BIT  12             /* inexact enable */

/* ================================================================
   Section 14: UUO (HLT) encoding constants
   From arm64-arch.lisp lines 1736-1772.
   ARM64 uses HLT instructions for traps.  The 16-bit immediate is:
     bits 2:0  — format code (3 bits)
     bits 7:3  — register operand (5 bits)
     bits 15:8 — type info or second register (8 bits)
   ================================================================ */

/* HLT format codes (low 3 bits) */
#define hlt_code_nullary                0
#define hlt_code_unary_reg_not_lisptag  1
#define hlt_code_unary_reg_not_fulltag  2
#define hlt_code_unary_reg_not_subtag   3
#define hlt_code_unary_reg_not_xtype    4
#define hlt_code_unary_misc             5
#define hlt_code_binary                 6

/* Extraction macros for HLT immediate fields */
#define HLT_FORMAT(imm)  ((imm) & 0x7)
#define HLT_REG(imm)     (((imm) >> 3) & 0x1F)
#define HLT_INFO(imm)    (((imm) >> 8) & 0xFF)

/* Misc UUO sub-codes (info field for hlt_code_unary_misc) */
#define uuo_misc_not_callable   0
#define uuo_misc_no_throw_tag   1
#define uuo_misc_tlb_too_small  2
#define uuo_misc_unbound        3

/* Binary UUO sub-codes (high 3 bits for hlt_code_binary) */
#define uuo_binary_vector_bounds 0

/* xtypes: 8-bit type codes for type error reporting */
#define xtype_integer       4
#define xtype_s64           8
#define xtype_u64           12
#define xtype_s32           16
#define xtype_u32           20
#define xtype_s16           24
#define xtype_u16           28
#define xtype_s8            32
#define xtype_u8            36
#define xtype_bit           40
#define xtype_rational      44
#define xtype_real          48
#define xtype_number        52
#define xtype_char_code     56
#define xtype_array3d       244
#define xtype_array2d       248
#define xtype_unsigned_byte_24 252

/* ================================================================
   Section 15: ABI version
   From arm64-arch.lisp line 1801.
   ================================================================ */

#define ABI_VERSION_MIN     1046
#define ABI_VERSION_CURRENT 1046
#define ABI_VERSION_MAX     1046

#include "lisp-errors.h"

#endif /* __ARM64_CONSTANTS_H__ */
