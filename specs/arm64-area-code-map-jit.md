# AREA_CODE with MAP_JIT for CCL ARM64

## Overview

Implement a separate code area (`AREA_CODE`) for the ARM64 port on macOS Apple Silicon. Code vectors are allocated in a MAP_JIT region; data (function objects, cons cells, etc.) stays in regular `AREA_DYNAMIC`. This cleanly solves the W^X enforcement problem: code pages are executable, data pages are writable, and neither needs runtime toggling during normal execution.

### Why Not vm_remap?

The maintainer has directed that `MAP_JIT` + `pthread_jit_write_protect_np` is the correct approach on Darwin. A separate AREA_CODE with MAP_JIT is architecturally cleaner than dual-mapping the entire dynamic area.

### Why Not Toggle W^X on the Whole Dynamic Area?

CCL's dynamic area has code AND data mixed on the same pages. When compiled Lisp code (in MAP_JIT) tries to write to a heap object (also in MAP_JIT), we need RX to execute the store instruction but RW to write to the target address. Both are in the same MAP_JIT region — you can't have both states simultaneously. This creates an infinite fault loop.

With a separate AREA_CODE, the problem disappears: stores target AREA_DYNAMIC (always RW), code executes from AREA_CODE (always RX during normal operation).

## Current ARM64 State (What Already Works)

The ARM64 port already has the right foundation:

- **Function layout:** slot 0 = entrypoint (untagged code address), slot 1 = code-vector (tagged pointer), slot 2+ = constants/immediates
- **FN-relative constant access:** The `ref-constant` vinsn loads via `[nfn, #offset]` where nfn points to the function gvector in the data heap — not PC-relative
- **FN saved in lisp-frame:** Already done (32-byte lisp frame: savevsp, savelr, savefn, savefp)
- **xcode-vector type exists:** `subtag-xcode-vector` is defined (32-bit element ivector)

The main change: xcode-vectors get allocated in AREA_CODE (MAP_JIT) instead of AREA_DYNAMIC.

---

## Phase 1: Code Area Infrastructure (Kernel C)

**Goal:** Allocate a separate MAP_JIT code heap at boot. Verify boot proceeds normally with no code allocated there yet.

### Changes

**`lisp-kernel/area.h`**
- `AREA_CODE` already defined as `(10<<fixnumshift)`
- Add `extern area *code_area;` global

**`lisp-kernel/memory.c`**
- `MapMemoryForCode()` already exists (MAP_JIT allocation)
- Add helper to allocate a code area of a given size

**`lisp-kernel/pmcl-kernel.c`**
- After image load, before entering Lisp:
  ```c
  code_area_start = MapMemoryForCode(CODE_AREA_INITIAL_SIZE);  // 128MB
  code_area = new_area(code_area_start, code_area_start + CODE_AREA_INITIAL_SIZE, AREA_CODE);
  code_area->active = code_area_start;
  add_area_holding_area_lock(code_area);
  ```

**`lisp-kernel/memprotect.h`**
- Add inline helpers:
  ```c
  static inline void code_heap_make_writable(void) {
      pthread_jit_write_protect_np(false);
  }
  static inline void code_heap_make_executable(void) {
      pthread_jit_write_protect_np(true);
  }
  ```

**`lisp-kernel/lisp_globals.h`**
- Add lisp globals: `CODE_HEAP_START`, `CODE_HEAP_ACTIVE`, `CODE_HEAP_LIMIT` so Lisp code can see the code area boundaries

### Testing
Boot the image. Verify the code area is allocated via debug output. Everything else works exactly as before.

---

## Phase 2: Code Vector Allocator (Kernel C + Assembly)

**Goal:** Add a bump allocator for xcode-vectors in AREA_CODE.

### Design Decision: C-Call Allocator

Code vectors are only allocated during compilation and FASL loading — not in inner loops. A C-call allocator avoids consuming extra callee-saved registers and is simpler than a register-pair bump allocator.

### Changes

**`lisp-kernel/code-alloc.c`** (new file, or in `arm64-exceptions.c`)
```c
LispObj alloc_code_vector(natural element_count) {
    natural nbytes = 8 + (element_count << 2);  // header + 32-bit elements
    natural aligned = (nbytes + dnode_size - 1) & ~(dnode_size - 1);

    code_heap_make_writable();

    BytePtr result = code_area->active;
    if (result + aligned > (BytePtr)code_area->high) {
        // TODO: grow code area or trigger GC
        Bug(NULL, "Code area exhausted");
    }

    LispObj header = make_header(subtag_xcode_vector, element_count);
    *((LispObj *)result) = header;
    code_area->active = result + aligned;

    code_heap_make_executable();

    return ptr_to_lispobj(result) | fulltag_misc;
}
```

**`lisp-kernel/arm64-spentry.s`**
- Add `SPalloc_code_vector`: takes element count in `imm0`, calls `alloc_code_vector`, returns tagged pointer in `arg_z`

**`level-0/ARM64/arm64-def.lisp`**
- Add LAP function `%alloc-code-vector` that invokes the subprimitive

### W^X Protocol
1. `code_heap_make_writable()` — before writing header + code data
2. Write instruction bytes
3. `sys_icache_invalidate()` on the written range
4. `code_heap_make_executable()` — toggle back to RX

### Testing
Allocate a code vector, verify its address is in the code area range, verify header is correct.

---

## Phase 3: FASL Loading + Compilation Use Code Allocator (Lisp)

**Goal:** Route xcode-vector allocation through the new code area allocator.

### Changes

**`level-0/nfasload.lisp`** (around line 753)
- Change `(allocate-typed-vector :code-vector element-count)` to `(%alloc-code-vector element-count)`
- Wrap code data writes with W^X toggles:
  ```lisp
  (code-heap-make-writable)
  (%fasl-read-n-bytes s vector 0 size-in-bytes)
  (%make-code-executable vector)  ; toggles to executable + flushes icache
  ```

**`compiler/ARM64/arm64-lap.lisp`** (around line 114)
- Change `(%alloc-misc code-vector-size ...)` to `(%alloc-code-vector code-vector-size)`

**`level-0/ARM64/arm64-def.lisp`**
- `%make-code-executable`: already flushes icache; add `code_heap_make_executable()` call
- `%fix-fn-entrypoint`: no change needed (already strips TBI tag for entrypoint)

### Testing
Load a FASL file. Verify code vector lands in AREA_CODE. Verify the function executes correctly.

---

## Phase 4: Image Save/Load (Kernel C)

**Goal:** Persist the code area in the heap image and restore it on load.

### Changes

**`lisp-kernel/image.h`**
- Change `NUM_IMAGE_SECTIONS` from 5 to 6
- Add code area base address to image header for relocation

**`lisp-kernel/image.c`**
- **Load:** Allocate MAP_JIT region, copy code data while writable, toggle to executable
- **Save:** Write AREA_CODE data as 6th section
- **Relocate:** Compute `code_bias = new_code_base - saved_code_base`. Walk all function objects in AREA_DYNAMIC, AREA_STATIC, AREA_READONLY and adjust:
  - Slot 0 (entrypoint): untagged pointer into code area, add `code_bias`
  - Slot 1 (code-vector): tagged pointer into code area, add `code_bias` (preserving TBI tag)

### Key Subtlety
MAP_JIT cannot use MAP_FIXED, so the code area address changes between save and load. Both the untagged entrypoint (slot 0) and tagged code-vector (slot 1) must be relocated.

### Testing
Save image, load it, verify boot. Check function entrypoints point into the new code area.

---

## Phase 5: GC Changes (Kernel C)

**Goal:** Make GC correctly handle the split code/data layout.

### Key Simplification: Non-Compacting Code Area

Code vectors in AREA_CODE never move during GC. This means:
- Function entrypoints (slot 0) are stable — no forwarding needed
- Code-vector pointers (slot 1) are stable — no forwarding needed
- No W^X toggling during GC compaction
- Return addresses on the stack remain valid

### Changes

**`lisp-kernel/arm64-gc.c`**

*Marking phase* (`mark_root`, `rmark`):
- When a reference points into AREA_CODE (address range check), mark it in AREA_CODE's markbits but do not recurse (xcode-vectors are ivectors with no node references)
  ```c
  if (ptr_in_code_area(n)) {
      natural code_dnode = area_dnode(n, code_area->low);
      set_bit(code_area->markbits, code_dnode);
      return;
  }
  ```

*Forwarding phase* (`forward_range`):
- For `subtag_function` objects: slot 0 and slot 1 point into AREA_CODE — skip forwarding (code doesn't move). Forward remaining slots normally.

*Compaction phase* (`compact_dynamic_heap`):
- Same: copy slot 0 and slot 1 as-is for function objects.

*Code area sweep* (new function):
- After dynamic area compaction, sweep AREA_CODE markbits. Zero dead code vectors (requires writable toggle). Reset markbits.

**`lisp-kernel/gc-common.c`**
- `gc()`: allocate code area markbits, zero before marking, call code area sweep after compaction

*`locative_forwarding_address`*:
- If locative points into AREA_CODE, return it unchanged.

### W^X During GC
- Reading code area data: no toggle needed (pages are readable when executable)
- Sweeping dead code vectors: `code_heap_make_writable()`, zero them, `code_heap_make_executable()`

### Testing
Run GC. Verify no crashes. Verify dead code vectors reclaimed, live ones untouched.

---

## Phase 6: Exception Handling Cleanup

**Goal:** Remove the W^X trampoline logic from the dynamic area.

With separate areas:
- AREA_DYNAMIC is never executable — execute faults are genuine bugs
- AREA_CODE is never writable during normal execution — write faults are genuine bugs

### Changes

**`lisp-kernel/arm64-exceptions.c`**
- Remove `dynamic_area_is_map_jit` flag
- Remove W^X trampoline redirect logic from Mach exception handler

**`lisp-kernel/arm64-spentry.s`**
- Remove `wp_true_trampoline` and `wp_false_trampoline`

**`lisp-kernel/pmcl-kernel.c`**
- Remove two-phase dynamic area relocation to MAP_JIT
- AREA_DYNAMIC no longer needs MAP_JIT

### Testing
Boot and run. Verify no spurious faults.

---

## Phase 7: Purification

**Goal:** Handle purify/impurify with the separate code area.

Code vectors stay in AREA_CODE (already executable). Purify does not move them — they are already in a dedicated region separate from data. Purify only copies data ivectors from AREA_DYNAMIC to AREA_READONLY.

### Changes
- Skip xcode-vectors during purify's ivector walk of AREA_DYNAMIC (they won't be there anymore)
- No changes needed for code area itself

### Testing
Call `(purify)` and `(impurify)`. Verify correct behavior.

---

## Phase 8: Cross-Compiler Updates

**Goal:** Generate correct ARM64 images with the code area from the cross-compiler.

### Changes

**`compiler/ARM64/arm64-lap.lisp`**
- Cross-compiling path: function layout unchanged (slot 0=entrypoint, slot 1=code-vector, slot 2+=constants), minimal changes needed

**`level-0/nfasload.lisp`**
- ARM64 FASL loader detects `subtag-xcode-vector` and routes to code area allocator automatically

**Cross-compile image builder**
- Needs to generate a 6-section image with AREA_CODE containing all xcode-vectors

### Testing
Cross-compile from x86-64 host, generate ARM64 image, boot it.

---

## Dependency Graph

```
Phase 1 (infrastructure)
   |
   v
Phase 2 (code allocator)
   |
   v
Phase 3 (FASL + compiler) -----> Phase 4 (image save/load)
   |                                  |
   v                                  v
Phase 5 (GC)                     Phase 7 (purification)
   |
   v
Phase 6 (exception cleanup)
   |
   v
Phase 8 (cross-compiler)
```

Phases 1-3 are the critical path. Phase 4 can proceed once Phase 3 is stable. Phase 5 is needed for any non-trivial Lisp session. Phase 6 is cleanup. Phase 8 is needed for full bootstrapping.

---

## Key Design Decisions

### 1. Non-Compacting Code Area
Code vectors never move during GC. This is the single most important simplification:
- No W^X toggling during GC compaction
- Function entrypoints stable across GC
- Return addresses on stack remain valid
- Downside: fragmentation over time (acceptable — code vectors are few and long-lived)

### 2. C-Call Code Allocator (Not Register-Pair)
Code vectors are allocated infrequently (compilation + FASL load). A C-call allocator avoids consuming two callee-saved registers and is simpler. If performance matters later, a register-pair bump allocator can be added.

### 3. Code Area Size
Start with 128MB initial allocation. If exhausted, allocate another MAP_JIT region and chain it. MAP_JIT cannot use MAP_FIXED, so multiple regions may be at unrelated addresses.

### 4. Image Format: 6 Sections
Add code area as 6th image section. Code area data is raw bytes (xcode-vector headers + instruction words). On load: allocate MAP_JIT, copy while writable, toggle to executable. Relocate function entrypoints by `code_bias`.

### 5. FN Register Semantics Unchanged
`nfn`/`fn` continues to point to the function gvector in AREA_DYNAMIC. Constants accessed via `[nfn, #offset]`. Entrypoint loaded from function slot 0. No vinsn changes needed for constant access.
