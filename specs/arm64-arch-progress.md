# arm64-arch.lisp Implementation Progress

Branch: `arm64-arch-foundation`

## Completed Sections

1. **Package and Requires** — `542cb733` — Package declaration, license, require/provide
2. **Register Definitions** — `b088c759` — GPRs x0-x30, lisp aliases (imm0-5, nargs, rnil, rt, temp0-3, fname, nfn, arg_x/y/z, save0-7, vsp, allocptr, rcontext, lr), DFPRs d0-d31 (vzero=d31), SFPRs s0-s31
3. **Kernel Globals** — `37f18b39` — *arm64-kernel-globals* (49 entries, matching lisp_globals.s)
4. **NIL-Relative Symbols** — `2d9e903c` — *arm64-nil-relative-symbols* (33 entries, matching lisp_globals.s NRS)
5. **Subprimitives Table** — `974f1c1b` — *arm64-subprims* (130 entries, shift=3/8-byte, base=tcr.sptab=384, EABI->AAPCS64)
6. **Storage Layout Macros** — `542cb733` — define-storage-layout (8-byte step), define-lisp-object, define-fixedsized-object

7. **Fundamental Constants** — `8dcb6d94` — nbits-in-word=64, tag-shift=56 (TBI), fixnumshift=0, node-size=8, dnode-size=16, fixnumone=1, target fixnum range (56-bit signed)
8. **Tag Definitions** — `6a36b847` — TBI high-byte tags: fixnum (0x00/0xFF), list (nil=2, cons=3), immediates (imm-tag-mask=#x10, single-float/character/markers), subtag aliases, full marker values, uvector infrastructure (ref=#x40, header=#x80, gvector=#x20), define-uvector/ivector/cl-ivector/gvector macros

9. **Uvector Subtags** — `b2cd209f` — All ivector/cl-ivector/gvector subtags (bignum through simple-vector), element-size boundary constants, max constant indices, arrayH<vectorH<simple-vector assertion

10. **Memory Layout Constants** — `8d4632f7` — Bias constants (misc-bias=cons-bias=function-bias=node-size=8), offset constants (misc-header-offset=-8, misc-subtag-offset=-8, misc-data-offset=0, misc-dfloat-offset=0, misc-complex-dfloat-offset=8); uniform TBI pointer bias: tagged_ptr_low56 = object_base + node-size

11. **NIL and T Values** — `1983833e` — nil-base-address=#x13000, canonical-nil-value=(tag-nil<<56|#x13008), nil-value alias, t-offset=dnode-size=16; memory layout: dnode at nil-base holds CDR/CAR(NIL)=NIL, T symbol at nil-base+16, nilsym-offset deferred to section 12

12. **Object Layout Definitions** — `5b650831` — cons (cdr/car), ratio, double-float (manual 32-bit element constants), complex, complex-single-float, complex-double-float (with pad), macptr, xmacptr, function (entrypoint only), symbol (7 fields, symbol.size=64), nilsym-offset=80, catch-frame (14 fields: catch-tag, save0-7, link, mvflag, db-link, xframe, last-lisp-frame), lock, vectorH, arrayH (with cell indices), value-cell, lisp-frame (0-based), binding (0-based), define-header macro + common headers. Note: arm64-constants.s has _structf sign bug (misc_bias=-8 vs expected positive); Lisp definitions are authoritative.

13. **TCR Layout** — tcr-bias=0, define-storage-layout tcr (41 fields, 328 bytes): prev, next, single-float-convert, lisp-fpscr, db-link, catch-top, save-vsp, save-tsp, cs-area, vs-area, ts-area, cs-limit, total-bytes-allocated, log2-allocation-quantum, interrupt-pending, xframe, errno-loc, ffi-exception, osid, valence, foreign-exception-status, native-thread-info, native-thread-id, last-allocptr, save-allocptr, save-allocbase, reset-completion, activate, suspend-count, suspend-context, pending-exception-context, suspend, resume, flags, gc-context, termination-semaphore, unwinding, tlb-limit, tlb-pointer, shutdown-count, safe-ref-address. Sub-word constants for split _word pairs: tcr.single-float-convert.value, tcr.lisp-fpscr-low, tcr.flags-value. interrupt-level-binding-index=1. lockptr (7 fields) and rwlock (8 fields) layouts.

## Remaining Sections
14. Kernel Imports
15. Target Uvector Subtags Alist
16. Array Type Helper
17. Misc Byte Count Helper
18. Target Arch Descriptor
19. Arch Macros
20. Condition Codes and FPSCR
21. UUO Encoding
22. Stack Frame Layout, FASL Version, Provide
