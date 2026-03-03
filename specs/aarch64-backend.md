# AArch64 Native Backend Specification

## Overview

This document specifies the work required to add a complete AArch64 (ARM64)
native backend to Clozure Common Lisp. The backend targets both Linux/AArch64
and macOS/Apple Silicon (Darwin/AArch64).

## Current State

Partial scaffolding exists from an earlier incomplete effort, with
`arm64-arch.lisp` now fully implemented on branch `arm64-arch-foundation`:

| File | Lines | Status |
|------|-------|--------|
| `compiler/ARM64/arm64-arch.lisp` | 1,803 | **COMPLETE** — all constants, layouts, macros |
| `lisp-kernel/arm64-spentry.s` | 3,825 | ~70% of ARM32 equivalent |
| `lisp-kernel/arm64-macros.s` | 608 | Partial |
| `lisp-kernel/arm64-constants.s` | 442 | Partial |
| `lisp-kernel/arm64-constants.h` | 82 | Minimal stub |
| `lisp-kernel/arm64-exceptions.h` | 15 | Empty stub |
| `lisp-kernel/arm64-uuo.s` | 67 | Minimal stub |
| `compiler/ARM64/arm64-asm.lisp` | 1,170 | Assembler partially started |
| `lisp-kernel/linuxarm64/Makefile` | exists | References missing `platform-linuxarm64.h` |

**Missing entirely:** arm64-exceptions.c, arm64-gc.c, platform headers,
compiler code generator, vinsn definitions, level-0 Lisp files, FFI, backtrace,
disassembler.

## Reference Implementations

- **ARM (32-bit) backend** -- primary structural template (same load/store
  architecture, similar register conventions)
- **x86-64 backend** -- reference for 64-bit-specific patterns (tagging scheme,
  large address space, 64-bit fixnum width)

## Architecture Decisions

### Tagging Scheme

**Decision (implemented):** Use Top Byte Ignore (TBI) tagging, placing type
tags in the high byte (bits 56-63) of 64-bit values.  This is a departure from
the x86-64 low-bit tagging scheme, leveraging AArch64 hardware TBI support:

- `nbits_in_word` = 64
- `tag_shift` = 56 (tags in bits 56-63)
- `fixnumshift` = 0 (fixnums are unshifted native integers)
- `ntagbits` = 8, `nlisptagbits` = 8
- `node_size` = 8

Tag byte layout:
- `#x00` / `#xFF` — fixnums (positive / negative, sign-extension of bit 55)
- `#x02` — NIL, `#x03` — cons
- `#x10`-`#x1F` — immediates (single-float, character, markers)
- `#x40`-`#x5F` — ivector references
- `#x60`-`#x7F` — gvector references
- `#x80`-`#xBF` — uvector headers (in low byte of header word)

Each uvector type gets a unique pointer tag AND header subtag, unlike
ARM32/x86-64 where all misc objects share one pointer tag.  The
`arm64-constants.s` definitions use this scheme; `arm64-arch.lisp` is
the authoritative Lisp-side mirror.

### Register Mapping

AArch64 provides 31 general-purpose registers (x0-x30), SP, and 32 SIMD/FP
registers (v0-v31).

**Finalized mapping** (implemented in `arm64-constants.s` and `arm64-arch.lisp`):

| Lisp Role | AArch64 Register | Notes |
|-----------|------------------|-------|
| `imm0`-`imm5` | x0-x5 | Unboxed immediates |
| `nargs` | x5 | Argument count (aliases imm5) |
| `rnil` | x6 | NIL register (holds canonical-nil-value) |
| `rt` | x7 | Return-type / temp |
| `temp3` / `fname` | x9 | Temporary 3 / function name |
| `temp2` / `nfn` | x10 | Temporary 2 / new function |
| `temp1` | x11 | Temporary 1 |
| `temp0` | x12 | Temporary 0 |
| `arg_x` | x13 | Third argument |
| `arg_y` | x14 | Second argument |
| `arg_z` | x15 | First argument |
| `save0`-`save7` | x16-x23 | Callee-saved Lisp registers |
| `loc_pc` | x24 | Locative PC |
| `vsp` | x25 | Value stack pointer |
| `allocptr` | x26 | Allocation pointer |
| `allocbase` | x27 | Allocation limit |
| `rcontext` | x28 | TCR pointer |
| `lr` | x30 | Link register (hardware) |
| `sp` | SP | C stack pointer (hardware) |

FP/SIMD registers: d0-d31 (double), s0-s31 (single), with `vzero` = d31/q31.

## Components

### 1. Kernel C Runtime

#### 1.1 `lisp-kernel/arm64-exceptions.c` (~2,500 lines)

Exception and trap handling for AArch64. Responsibilities:

- Decode AArch64 instructions at trap sites to determine trap type
- Recognize allocation sequences (SUB from allocptr, compare with allocbase,
  conditional branch pattern)
- Handle UUO (Undefined/Unimplemented Operation) traps -- CCL uses illegal
  instructions as traps for type errors, unbound variables, etc.
- GC trap handling: recognize GC-safe-point patterns, adjust PC to allow
  GC to proceed
- Signal handler setup (SIGSEGV, SIGBUS, SIGTRAP, SIGILL)
- Pseudosignal support for deferred interrupts
- Debug trap support

Reference: `arm-exceptions.c` (2,070 lines). AArch64 will be larger due to
more complex instruction encoding patterns.

Key AArch64-specific concerns:
- AArch64 uses BRK instructions for traps (vs ARM32 UDF)
- Instruction encoding is fixed 32-bit but with different format classes
- PC-relative addressing (ADR/ADRP) needs special handling for GC relocation

#### 1.2 `lisp-kernel/arm64-gc.c` (~2,100 lines)

Architecture-specific garbage collection support:

- `mark_root()` -- mark a single root, handling AArch64 tagged pointers
- `forward_tcr()` -- update TCR fields after compaction
- `mark_xp()` -- mark roots in an exception context (all Lisp-tagged GPRs)
- `forward_xp()` -- forward pointers in exception context
- `check_refmap_consistency()` -- verify write barrier integrity
- `pc_luser_xp()` -- adjust PC if interrupted mid-allocation-sequence
  (critical for GC safety: must recognize partial allocation and back up
  or complete it)
- Code vector scanning -- walk AArch64 code vectors to find embedded
  literal references

Reference: `arm-gc.c` (2,119 lines).

#### 1.3 `lisp-kernel/arm64_print.c` (~300 lines)

Debug printing support for AArch64 Lisp objects:

- `sprint_gpr()` -- print a GPR value as a Lisp object
- `print_lisp_context()` -- dump all Lisp registers from a signal context

Reference: `arm_print.c`.

#### 1.4 Platform Headers

##### `lisp-kernel/platform-linuxarm64.h` (~80 lines)

```c
#define WORD_SIZE 64
#define PLATFORM_OS PLATFORM_OS_LINUX
#define PLATFORM_CPU PLATFORM_CPU_ARM64
#define PLATFORM_WORD_SIZE PLATFORM_WORD_SIZE_64

typedef ucontext_t ExceptionInformation;

// Register accessors for Linux AArch64 ucontext
#define xpGPR(x, gprno) ((x)->uc_mcontext.regs[gprno])
#define xpPC(x)          ((x)->uc_mcontext.pc)
#define xpLR(x)          ((x)->uc_mcontext.regs[30])
#define xpPSTATE(x)      ((x)->uc_mcontext.pstate)
```

##### `lisp-kernel/platform-darwinarm64.h` (~80 lines)

```c
#define WORD_SIZE 64
#define PLATFORM_OS PLATFORM_OS_DARWIN
#define PLATFORM_CPU PLATFORM_CPU_ARM64
#define PLATFORM_WORD_SIZE PLATFORM_WORD_SIZE_64

// Darwin uses Mach exceptions on AArch64
// Register accessors for Darwin arm_thread_state64_t
#define xpGPR(x, gprno) ((x)->uc_mcontext->__ss.__x[gprno])
#define xpPC(x)          ((x)->uc_mcontext->__ss.__pc)
#define xpLR(x)          ((x)->uc_mcontext->__ss.__lr)
#define xpSP(x)          ((x)->uc_mcontext->__ss.__sp)
```

#### 1.5 `lisp-kernel/arm64-constants.h` (expand from 82 to ~400 lines)

Needs to be fleshed out with:

- Full TCR field offsets for AArch64
- Register number constants matching the register mapping
- UUO format definitions for AArch64 (BRK-based traps)
- Allocation trap instruction patterns
- Node/immediate tag definitions (may reference shared 64-bit constants)

### 2. Kernel Assembly

#### 2.1 `lisp-kernel/arm64-spentry.s` (complete, ~5,000+ lines total)

Subprimitive entries -- the low-level runtime routines called by compiled
Lisp code. Currently 3,825 lines; needs completion of:

- Arithmetic with overflow detection (fixnum add/sub/mul with bignum fallback)
- Cons and general allocation sequences
- Type checking primitives (typep, consp, fixnump, etc.)
- Special variable binding/unbinding (bind, unbind, unbind_n)
- Catch/throw/unwind-protect
- funcall, apply, spread_lexpr
- Multiple value handling (values, mv-call)
- Array access (aref/aset for all element types)
- Hash table probing
- Foreign function call glue (Lisp-to-C and C-to-Lisp transitions)
- Stack overflow checking
- GC-related traps and safe points

Reference: `arm-spentry.s` (5,077 lines), `x86-spentry64.s`.

#### 2.2 `lisp-kernel/arm64-asmutils.s` (~300 lines)

Assembly utility routines:

- Context save/restore for signal handling
- C-to-Lisp and Lisp-to-C call frame setup
- Stack switching between C stack and Lisp value/temp stacks
- Atomic operations (compare-and-swap for thread safety)
- `enable_fp_exceptions` / `disable_fp_exceptions`
- Cache flush after code generation (critical on AArch64: `dc cvau` + `ic ivau`
  instruction cache coherence is not automatic like x86)

#### 2.3 `lisp-kernel/arm64-uuo.s` (expand from 67 to ~120 lines)

UUO (trap) instruction definitions:

- BRK-based trap encodings for type errors, unbound variable, etc.
- Format: encode trap type and operand register into BRK immediate field
- Must match the decoding logic in `arm64-exceptions.c`

### 3. Compiler Backend (Lisp)

#### 3.1 `compiler/ARM64/arm64-arch.lisp` — **COMPLETE** (1,803 lines)

The foundational architecture description.  Fully implemented on branch
`arm64-arch-foundation` (see `specs/arm64-arch-progress.md` for detailed
section-by-section breakdown).  Contains:

- Register names, numbers, and classes (GPRs x0-x30 with Lisp aliases,
  DFPRs d0-d31, SFPRs s0-s31)
- TBI tag bit layout (tag-shift=56, fixnumshift=0, 8-bit tag byte)
- Uvector subtags (ivector/cl-ivector/gvector, 40+ types)
- Memory layout constants (uniform TBI bias: all pointers = base + node-size)
- NIL/T values, nil-base-address=#x13000
- Object layouts (cons, ratio, double-float, complex types, macptr, function,
  symbol, catch-frame, lock, vectorH, arrayH, value-cell, lisp-frame, binding)
- TCR layout (41 fields, 328 bytes, matching arm64-constants.s)
- Kernel globals (49 entries), nil-relative symbols (33 entries)
- Subprimitives table (130 entries, AAPCS64 naming)
- Kernel imports (65 entries)
- Target uvector subtags alist, array-type-name-from-ctype, misc-byte-count
- Target arch descriptor (*arm64-target-arch*)
- Area/protected-area storage layouts
- 22 arch macros (defarm64archmacro) for cross-cutting operations
- AArch64 condition codes, FPCR/FPSR exception bits
- HLT-based UUO encoding constants (7 format codes, xtype values)
- Fake stack frame layout, FASL version #x68, ABI version 1046

Reference: `compiler/ARM/arm-arch.lisp` (1,461 lines).

#### 3.2 `compiler/ARM64/arm64-vinsns.lisp` (~5,000 lines)

Virtual instruction (vinsn) definitions. Each vinsn is a named pattern that
emits one or more AArch64 instructions. Categories:

- **Register moves:** copy between registers, load constants
- **Memory access:** load/store with various addressing modes, displaced access
- **Arithmetic:** add, sub, mul, div (fixnum and unboxed)
- **Logic:** and, or, xor, shifts
- **Comparison and branching:** compare, conditional branch, tbz/tbnz
  (AArch64 test-bit-and-branch)
- **Type tests:** fixnump, consp, characterp, subtag checks
- **Allocation:** cons, make-list, allocate general object
- **Calling:** funcall, apply, jump, return
- **Binding:** bind/unbind special variables
- **Stack:** push/pop on vsp and tsp
- **Floating point:** load/store, arithmetic, conversion, comparison
- **Tagging/untagging:** box/unbox fixnum, character, etc.

AArch64-specific vinsn considerations:
- Logical immediates use a special bitmask encoding (not arbitrary values)
- MOV wide immediates may need MOVZ+MOVK sequences for large constants
- Conditional select (CSEL) can replace some branch sequences
- No direct flags-setting for some operations (need explicit CMP/TST)

Reference: `compiler/ARM/arm-vinsns.lisp` (4,429 lines).

#### 3.3 `compiler/ARM64/arm642.lisp` (~10,000 lines)

The main code generator. Translates compiler IR (acode) into vinsn sequences.
This is the heart of the backend. Major sections:

- Expression compilation (variables, constants, function calls)
- Special form compilation (if, let, block, tagbody, catch, etc.)
- Argument passing and multiple value returns
- Register allocation and spilling
- Stack frame layout and management
- Foreign function calls (callback and callout)
- Inline arithmetic with overflow handling
- Inline type tests
- Optimize common patterns (e.g., (if (typep x ...) ...))

Reference: `compiler/ARM/arm2.lisp` (9,971 lines).

#### 3.4 `compiler/ARM64/arm64-backend.lisp` (~650 lines)

Backend registration and configuration:

- Define the `arm64-backend` CLOS class
- Register sets and allocation order
- Calling convention parameters (how many args in registers, etc.)
- Stack frame layout constants
- Pointer to the vinsn templates
- FPR handling
- Target-specific compiler policy

Reference: `compiler/ARM/arm-backend.lisp` (641 lines).

#### 3.5 `compiler/ARM64/arm64-lap.lisp` (~350 lines)

LAP (Lisp Assembly Program) support for hand-written assembly:

- Macros for defining LAP functions in Lisp source
- Instruction forms that map to assembler calls
- Label and branch support
- Integration with the Lisp object system (function headers, etc.)

Reference: `compiler/ARM/arm-lap.lisp` (339 lines).

#### 3.6 `compiler/ARM64/arm64-lapmacros.lisp` (~400 lines)

Convenience macros for LAP:

- Common sequences (push, pop, load-constant, funcall)
- Stack frame setup/teardown
- Special variable access
- Type checking sequences

Reference: `compiler/ARM/arm-lapmacros.lisp` (401 lines).

#### 3.7 `compiler/ARM64/arm64-disassemble.lisp` (~800 lines)

AArch64 disassembler for `(disassemble)`:

- Decode all instruction classes: data processing, branches, loads/stores,
  SIMD/FP
- Display with symbolic register names (using Lisp register aliases)
- Show branch targets as labels
- Annotate subprimitive calls

AArch64's encoding is more regular than ARM32 but has more instruction classes,
so this will be somewhat larger than ARM's 575 lines.

#### 3.8 `compiler/ARM64/arm64-asm.lisp` (complete, currently 1,170 lines)

The instruction-level assembler. Partially started. Needs:

- Complete instruction encoding for all AArch64 instruction forms
- Fixup/relocation support for forward branches
- Literal pool management (AArch64 loads literals via PC-relative LDR)
- Alignment and padding

### 4. Level-0 Low-Level Lisp

A new directory `level-0/ARM64/` with architecture-specific implementations
of core operations. These files contain Lisp code using LAP for
performance-critical paths.

#### Files needed (modeled on `level-0/ARM/`):

| File | Purpose | Reference Lines |
|------|---------|-----------------|
| `arm64-def.lisp` | Basic definitions, defun support | ~200 |
| `arm64-misc.lisp` | Miscellaneous primitives (eq, car, cdr, rplaca, etc.) | ~400 |
| `arm64-utils.lisp` | Utility functions, stack operations | ~300 |
| `arm64-numbers.lisp` | Fixnum/integer arithmetic | ~500 |
| `arm64-bignum.lisp` | Bignum arithmetic (multiply, divide, GCD) | ~600 |
| `arm64-float.lisp` | Floating-point operations, conversions | ~400 |
| `arm64-array.lisp` | Array element access, vector operations | ~300 |
| `arm64-hash.lisp` | Hash table probing, hashing functions | ~200 |
| `arm64-symbol.lisp` | Symbol value access, plist operations | ~200 |
| `arm64-pred.lisp` | Type predicates | ~200 |
| `arm64-clos.lisp` | GF dispatch, method combination | ~300 |
| `arm64-io.lisp` | Low-level I/O primitives | ~200 |

Estimated total: ~3,800 lines.

### 5. Library Support

#### 5.1 `lib/arm64-backtrace.lisp` (~500 lines)

Stack walking for backtraces and the debugger:

- Walk AArch64 stack frames (following frame pointer chain)
- Decode return addresses to find calling functions
- Handle mixed Lisp/foreign frames
- Recover local variable values from stack/registers

Reference: `lib/arm-backtrace.lisp`.

#### 5.2 `lib/arm64env.lisp` (~200 lines)

Environment setup:

- Feature flags for `*features*` (`:arm64-target`, `:64-bit-target`, etc.)
- Default optimization settings
- AArch64-specific configuration

Reference: `lib/armenv.lisp`.

#### 5.3 `lib/ffi-linuxarm64.lisp` (~600 lines)

FFI for Linux AArch64 (AAPCS64):

- Classify arguments: integer registers (x0-x7), FP registers (v0-v7),
  stack
- Handle struct passing (by value for small structs, by reference for large)
- HFA (Homogeneous Floating-point Aggregate) detection and passing
- Variadic function support (AArch64 varargs use stack, not registers,
  for anonymous args on some ABIs)
- Callback support (Lisp functions callable from C)

#### 5.4 `lib/ffi-darwinarm64.lisp` (~600 lines)

FFI for macOS/Apple Silicon:

- Apple's ABI variant (differs from AAPCS64 in some details)
- Variadic function handling (Apple requires all varargs on stack)
- Objective-C runtime interop (objc_msgSend)
- Framework loading

### 6. Build System

#### 6.1 `lisp-kernel/linuxarm64/Makefile` (update existing)

- Fix reference to missing `platform-linuxarm64.h`
- Ensure all new .c and .s files are listed
- Verify linker script

#### 6.2 `lisp-kernel/darwinarm64/Makefile` (new, ~80 lines)

- Darwin-specific compiler flags
- Mach-O linking (vs ELF on Linux)
- Code signing requirements for Apple Silicon
- `pthread_jit_write_protect_np` support flags

#### 6.3 `lisp-kernel/darwinarm64/` directory

- Platform-specific signal/exception handling wrappers
- Mach exception port setup

#### 6.4 Linker Scripts

- `lisp-kernel/linuxarm64/armlinux64.x` (if not already present)
- Defines memory layout for the Lisp kernel binary

### 7. Bootstrap and Cross-Compilation

#### 7.1 Cross-compilation from x86-64

The initial build must be cross-compiled:

1. Load the arm64 backend definition into an x86-64 CCL
2. Cross-compile all Lisp sources targeting arm64
3. Write out an arm64 heap image
4. Combine with the arm64 kernel binary (built by C/assembly compilation)
5. Boot and test

This requires adding arm64 as a recognized target in the cross-compilation
infrastructure.

#### 7.2 Self-hosting

The ultimate goal is that the arm64 CCL can compile itself:

1. Cross-compile produces a working arm64 CCL
2. Arm64 CCL recompiles all its own sources
3. Resulting image matches (or is functionally equivalent to) the cross-compiled
   version

## Platform-Specific Concerns

### Apple Silicon (Darwin/AArch64)

- **W^X enforcement:** macOS requires JIT memory to be either writable or
  executable, not both simultaneously. Use `pthread_jit_write_protect_np()`
  to toggle. The allocation and code-patching paths must call this.
- **16KB pages:** macOS on Apple Silicon uses 16KB pages (vs 4KB on Linux).
  Affects memory mapping granularity.
- **Mach exceptions:** Darwin uses Mach exception ports rather than Unix
  signals for some trap types. Existing `darwinx8664` code shows the pattern.
- **Code signing:** Even JIT code must be signed on macOS. Use
  `MAP_JIT` flag with `mmap()`.
- **Pointer authentication (PAC):** Apple Silicon supports PAC. LR values
  in stack frames may be signed. Must strip PAC bits when walking stacks
  (`ptrauth_strip()`).

### Linux/AArch64

- **4KB or 64KB pages:** Page size varies by kernel configuration.
  Should detect at runtime.
- **MTE (Memory Tagging Extension):** Future consideration. Tag bits in
  pointers could conflict with Lisp tag bits. Ensure MTE is disabled for
  Lisp heap memory or accommodate it.
- **BTI (Branch Target Identification):** If enabled, indirect branch
  targets must have BTI instructions. Generated code may need BTI landing
  pads.

## Instruction Cache Coherence

Unlike x86, AArch64 does **not** have coherent instruction caches. After
writing generated code to memory, the backend must execute:

```asm
    dc cvau, <addr>     ; Clean data cache to point of unification
    dsb ish              ; Data synchronization barrier
    ic ivau, <addr>     ; Invalidate instruction cache
    dsb ish              ; Ensure completion
    isb                  ; Instruction synchronization barrier
```

This must happen:
- After compiling any function
- After patching code (GC relocation, self-modifying code)
- After loading a heap image

## Estimated Size Summary

| Component | Estimated Lines | Difficulty | Status |
|-----------|----------------|------------|--------|
| Kernel C (exceptions, GC, platform headers, print) | ~5,000 | Very High | Not started |
| Kernel assembly (complete spentry, asmutils, UUO) | ~2,000 | High | Partial (~4,500 existing) |
| Compiler backend (arch, vinsns, codegen, backend, LAP, disasm, asm) | ~19,000 | Very High | arch.lisp done (1,803) |
| Level-0 Lisp (12 files) | ~3,800 | Medium | Not started |
| Library (FFI, backtrace, env) | ~1,900 | Medium-High | Not started |
| Build system (Makefiles, linker scripts) | ~300 | Medium | Partial |
| **Total new/modified code** | **~32,000** | | **~6% complete** |

## Suggested Implementation Order

### Phase 1: Foundation
1. ~~Finalize register mapping (Section: Register Mapping)~~ **DONE**
2. ~~Complete `arm64-arch.lisp` -- all constants and definitions~~ **DONE** (1,803 lines)
3. Complete `arm64-constants.h` -- C-side mirror of arch constants
4. Write `platform-linuxarm64.h` (and/or `platform-darwinarm64.h`)

### Phase 2: Kernel Runtime
5. Implement `arm64-exceptions.c` -- trap handling
6. Implement `arm64-gc.c` -- GC support
7. Implement `arm64_print.c` -- debug printing
8. Complete `arm64-spentry.s` -- all subprimitives
9. Write `arm64-asmutils.s` -- assembly utilities

### Phase 3: Assembler and Compiler
10. Complete `arm64-asm.lisp` -- instruction assembler
11. Implement `arm64-vinsns.lisp` -- vinsn definitions
12. Implement `arm64-backend.lisp` -- backend registration
13. Implement `arm642.lisp` -- main code generator
14. Implement `arm64-lap.lisp` and `arm64-lapmacros.lisp`

### Phase 4: Lisp Runtime
15. Implement all `level-0/ARM64/` files
16. Implement `lib/arm64-backtrace.lisp`
17. Implement `lib/arm64env.lisp`
18. Implement FFI files

### Phase 5: Integration and Bootstrap
19. Update build system (Makefiles)
20. Cross-compile from x86-64
21. Boot, debug, iterate
22. Implement `arm64-disassemble.lisp`
23. Achieve self-hosting

### Phase 6: Polish
24. Optimization passes (instruction scheduling, peephole)
25. Full test suite pass
26. Documentation
