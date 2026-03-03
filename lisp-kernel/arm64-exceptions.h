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

#ifndef __ARM64_EXCEPTIONS_H__
#define __ARM64_EXCEPTIONS_H__

/* AArch64 instructions are fixed 32-bit. */
typedef u_int32_t opcode, *pc;

/* ================================================================
   HLT-based UUO detection.

   AArch64 HLT encoding: 0xD4400000 | (imm16 << 5)
   The low 3 bits of the 16-bit immediate define the format;
   see arm64-uuo.s and arm64-constants.h for format codes.
   ================================================================ */

#define HLT_INSTRUCTION_MASK  0xFFE0001F
#define HLT_INSTRUCTION_VALUE 0xD4400000

#define IS_HLT(i) (((i) & HLT_INSTRUCTION_MASK) == HLT_INSTRUCTION_VALUE)
#define HLT_IMM16(i) (((i) >> 5) & 0xFFFF)

/* Classify an HLT by its format code (low 3 bits of imm16). */
#define HLT_UUO_FORMAT(i) (HLT_IMM16(i) & 0x7)
#define HLT_UUO_REG(i)    ((HLT_IMM16(i) >> 3) & 0x1F)
#define HLT_UUO_INFO(i)   ((HLT_IMM16(i) >> 8) & 0xFF)

/* Allocation trap: hlt_code_nullary with info=0. */
#define IS_ALLOC_TRAP(i) (IS_HLT(i) && HLT_IMM16(i) == hlt_code_nullary)

/* GC trap: hlt_code_nullary with info=1. */
#define IS_GC_TRAP(i)    (IS_HLT(i) && HLT_IMM16(i) == (hlt_code_nullary | (1 << 3)))

/* Debug trap: hlt_code_nullary with info=2. */
#define IS_DEBUG_TRAP(i) (IS_HLT(i) && HLT_IMM16(i) == (hlt_code_nullary | (2 << 3)))

/* Deferred interrupt: hlt_code_nullary with info=3. */
#define IS_DEFERRED_INTERRUPT(i) (IS_HLT(i) && HLT_IMM16(i) == (hlt_code_nullary | (3 << 3)))

/* Deferred suspend: hlt_code_nullary with info=4. */
#define IS_DEFERRED_SUSPEND(i)   (IS_HLT(i) && HLT_IMM16(i) == (hlt_code_nullary | (4 << 3)))

/* ================================================================
   Allocation sequence detection.

   The ARM64 allocation sequence is:
     sub allocptr, allocptr, #size    ; or sub allocptr, allocptr, Xn
     ldr temp, [rcontext, #save_allocbase]
     cmp allocptr, temp
     b.hs alloc_ok
     hlt #(alloc_trap)                ; triggers GC
   alloc_ok:
     str header, [allocptr, #-node_size]  ; set header
     ; ... fill fields ...
     orr result, allocptr, #tag       ; tag the pointer
   ================================================================ */

/* SUB Xd, Xn, #imm12 — checks for allocptr (x26) as destination and source */
#define IS_SUB_IMM_FROM_ALLOCPTR(i) \
  (((i) & 0xFF00001F) == (0xD1000000 | allocptr) && \
   (((i) >> 5) & 0x1F) == allocptr)

/* SUB Xd, Xn, Xm — allocptr = allocptr - Xm */
#define IS_SUB_REG_FROM_ALLOCPTR(i) \
  (((i) & 0xFFE0001F) == (0xCB000000 | allocptr) && \
   (((i) >> 5) & 0x1F) == allocptr)

#define IS_SUB_FROM_ALLOCPTR(i) \
  (IS_SUB_IMM_FROM_ALLOCPTR(i) || IS_SUB_REG_FROM_ALLOCPTR(i))

/* LDR Xt, [rcontext, #offset] — load allocbase from TCR */
#define IS_LOAD_ALLOCBASE_FROM_TCR(i) \
  (((i) & 0xFFC003E0) == (0xF9400000 | (rcontext << 5)))

/* CMP allocptr, Xm — compare allocptr to allocbase */
#define IS_COMPARE_ALLOCPTR(i) \
  (((i) & 0xFFE0FFE0) == (0xEB00001F | (allocptr << 5)))

typedef enum {
  ID_unrecognized_alloc_instruction,
  ID_sub_allocptr_instruction,
  ID_load_allocbase_instruction,
  ID_compare_allocptr_instruction,
  ID_branch_around_alloc_trap_instruction,
  ID_alloc_trap_instruction,
  ID_set_header_instruction,
  ID_finish_allocation
} alloc_instruction_id;

/* ================================================================
   Function declarations.
   ================================================================ */

Boolean
handle_uuo(ExceptionInformation *, siginfo_t *, opcode);

int
callback_for_trap(LispObj, ExceptionInformation *, natural, natural, int*);

natural
register_codevector_contains_pc(natural, pc);

int
callback_to_lisp(LispObj, ExceptionInformation *, natural, natural, int*);

OSStatus
handle_trap(ExceptionInformation *, opcode, pc, siginfo_t *);

OSStatus
handle_error(ExceptionInformation *, unsigned, unsigned, int*);

Boolean
extend_tcr_tlb(TCR *, ExceptionInformation *, unsigned);

void
pc_luser_xp(ExceptionInformation *, TCR *, signed_natural *);

void
normalize_tcr(ExceptionInformation *, TCR *, Boolean);

void
install_signal_handler(int, void*, unsigned);

void enable_fp_exceptions(void);

/* AArch64 code vectors start with a header word (element count),
   not executable code.  The first instruction follows the header. */
#define codevec_hdr_p(value) ((value) == 0)

#ifdef DARWIN
#undef USE_SIGALTSTACK
#else
#define USE_SIGALTSTACK 1
#endif

#ifdef USE_SIGALTSTACK
void
invoke_handler_on_main_stack(int, siginfo_t*, ExceptionInformation *, void *, void*);
void setup_sigaltstack(area *);
#define ALTSTACK(handler) altstack_ ## handler
#else
#define ALTSTACK(handler) handler
#endif

#endif /* __ARM64_EXCEPTIONS_H__ */
