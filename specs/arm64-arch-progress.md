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

14. **Kernel Imports** — %kernel-global function and macro (offset = -(pos+2)×node-size, relative to rnil effective address), kernel-import defenum (65 entries, step=node-size=8, fd-setsize-bytes through lisp-realpath, matching x86-64), nrs-offset macro (byte offset from NIL symbol to requested symbol, formula: (1-pos)×symbol.size).

15. **Target Uvector Subtags Alist** — *arm64-target-uvector-subtags* (42 entries): maps keyword type names to subtag values. Follows x86-64 pattern: includes s64/u64 vector types, no code-vector/pseudofunction. Entries: bignum, ratio, single-float, double-float, complex types, symbol, function, xcode-vector, macptr, catch-frame, struct, istruct, pool, population, hash-vector, package, value-cell, instance, lock, basic-stream, slot-vector, simple-string, bit-vector, s8/u8/s16/u16/s32/u32/s64/u64 vectors, fixnum-vector, single/double-float vectors, simple-vector, complex-single/double-float vectors, vectorH, arrayH, min-cl-ivector-subtag.

16. **Array Type Helper** — arm64-array-type-name-from-ctype: maps compile-time array ctypes to keyword element-type names. Follows x86-64 pattern with 64-bit integer ranges (s32 before fixnum before u64/s64). Handles class-ctype (character→:simple-string), numeric-ctype (integer ranges, float formats, complex), named-ctype (T→:simple-vector).

17. **Misc Byte Count Helper** — arm64-misc-byte-count: computes data byte count from subtag+element-count. TBI dispatch: gvectors via bit-5 test (×8), ivectors by subtag range (32-bit×4, 64-bit×8, 8-bit×1, 16-bit×2, complex-df×16, bit-vector÷8).

18. **Target Arch Descriptor** — *arm64-target-arch* via arch::make-target-arch. Key TBI-specific settings: ntagbits=8, nlisptagbits=8, fulltagmask=#xFF, fulltag-misc=uvector-ref(#x40). Tags use TBI top-byte values: fixnum-tag=0, cons-tag=3, null-tag=2, symbol-tag=tag-symbol(#x63), function-tag=tag-function(#x62). single-float-tag-is-subtag=nil (immediate in TBI). 64-bit platform: node-size=8, word-shift=3, includes s64/u64/fixnum in 64-bit-ivector-types. arm64-fpr-mask: 1 bit per register (AArch64 v-regs handle all widths). Wires .SPbuiltin-plus for primitive→subprims dispatch.

19. **Area and Protected-Area Layouts** — define-storage-layout area (21 fields: pred, succ, low, high, active, softlimit, hardlimit, code, markbits, ndnodes, older, younger, h, softprot, hardprot, owner, refbits, threshold, gc-count, static-dnodes, static-used). define-storage-layout protected-area (6 fields: next, start, end, nprot, protsize, why). Missing from section 12; needed by area-code/area-succ arch macros.

20. **Arch Macros** — defarm64archmacro wrapper. 22 macros: %make-sfloat (error—immediate in TBI), %make-dfloat, %numerator/%denominator (ratio cells), %realpart/%imagpart (dispatch on complex-single/double-float subtags), %get-single-float-from-double-ptr, codevec-header-p (error—no code-vector type), immediate-p-macro (TBI: tag=0x00/0xFF or imm-tag-mask test), hashed-by-identity (TBI: fixnum/imm/symbol/instance), %get-kernel-global/%get-kernel-global-ptr (fixnum-ref from nil-base+node-size+offset, no shift needed with fixnumshift=0), %target-kernel-global, lfun-vector/lfun-vector-lfun (identity), area-code/area-succ, nth-immediate/set-nth-immediate (+1 for entrypoint), symptr->symvector/symvector->symptr (identity), function-to-function-vector/function-vector-to-function (identity), with-ffcall-results (128 bytes: 8 GPRs + 8 FPRs for AAPCS64). arg-check-trap-pc-limit=8 (CMP+HLT).

21. **Condition Codes and FPSCR** — arm64-cond-eq through arm64-cond-al (15 values via defenum), arm64-cond-cs/cc synonyms for hs/lo. FPSR cumulative flags: ioc=0, dzc=1, ofc=2, ufc=3, ixc=4. FPCR enables: ioe=8, dze=9, ofe=10, ufe=11, ixe=12. Same bit positions as ARM32 FPSCR (AArch64 splits into FPCR+FPSR but bit layout is compatible).

22. **UUO Encoding** — HLT-based trap format (16-bit immediate, low 3 bits = format code). 7 format codes: hlt-code-nullary=0, hlt-code-unary-reg-not-lisptag=1, hlt-code-unary-reg-not-fulltag=2, hlt-code-unary-reg-not-subtag=3, hlt-code-unary-reg-not-xtype=4, hlt-code-unary-misc=5, hlt-code-binary=6. Misc sub-codes: not-callable=0, no-throw-tag=1, tlb-too-small=2, unbound=3. Binary sub-code: vector-bounds=0. 16 xtype constants (same values as ARM32): unsigned-byte-24=252, array2d=248, array3d=244, integer=4, s64/u64/s32/u32/s16/u16/s8/u8=8-36, bit=40, rational=44, real=48, number=52, char-code=56.

23. **Stack Frame Layout, FASL Version, Provide** — fake-stack-frame (8 fields: header, type, sp, next-sp, fn, lr, vsp, xp). fasl-version=#x68, fasl-max/min-version=#x68, *image-abi-version*=1046. (provide "ARM64-ARCH"). Note: real-tags-mask/numeric-tags-mask intentionally omitted (TBI subtag values exceed bitmask range and these constants are unused).

## Status: COMPLETE

All sections of arm64-arch.lisp have been implemented.
