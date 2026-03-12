;;; -*- Mode: Lisp; Package: CCL; -*-
;;;
;;; Copyright 2025 Clozure Associates
;;;
;;; Licensed under the Apache License, Version 2.0 (the "License");
;;; you may not use this file except in compliance with the License.
;;; You may obtain a copy of the License at
;;;
;;;     http://www.apache.org/licenses/LICENSE-2.0
;;;
;;; Unless required by applicable law or agreed to in writing, software
;;; distributed under the License is distributed on an "AS IS" BASIS,
;;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;; See the License for the specific language governing permissions and
;;; limitations under the License.


(in-package "CCL")

(defarm64lapfunction %address-of ((arg arg_z))
  ;; %address-of a fixnum is a fixnum, just for spite.
  ;; %address-of anything else is the address of that thing as an integer.
  ;; ARM64: fixnumshift=0, so fixnum value = raw integer.
  ;; For non-fixnums, imm0 gets the tagged pointer value (including tag byte).
  (test-fixnum arg)
  (mov imm0 arg_z)
  (b.ne @not-fixnum)
  (ret)
  @not-fixnum
  (spjump .SPmakeu64))

;;; "areas" are fixnum-tagged and, for the most part, so are their
;;; contents.

;;; The nilreg-relative global all-areas is a doubly-linked-list header
;;; that describes nothing.  Its successor describes the current/active
;;; dynamic heap.  Return a fixnum which "points to" that area, after
;;; ensuring that the "active" pointers associated with the current thread's
;;; stacks are correct.

(defarm64lapfunction %normalize-areas ()
  (let ((address imm0))
    ;; Update active pointer for vsp area.
    (ldr address (:@ rcontext (:$ arm64::tcr.vs-area)))
    (str vsp (:@ address (:$ arm64::area.active)))
    ;; Update active pointer for SP area
    (ldr arg_z (:@ rcontext (:$ arm64::tcr.cs-area)))
    (str sp (:@ arg_z (:$ arm64::area.active)))
    (ref-global arg_z all-areas)
    (ldr arg_z (:@ arg_z (:$ arm64::area.succ)))
    (ret)))

(defarm64lapfunction %active-dynamic-area ()
  (ref-global arg_z all-areas)
  (ldr arg_z (:@ arg_z (:$ arm64::area.succ)))
  (ret))


(defarm64lapfunction %object-in-stack-area-p ((object arg_y) (area arg_z))
  (ldr imm0 (:@ area (:$ arm64::area.active)))
  (ldr imm1 (:@ area (:$ arm64::area.high)))
  (mov arg_z rnil)
  (cmp object imm0)
  (b.lo @done)
  (cmp object imm1)
  (b.hs @done)
  (add arg_z rnil (:$ arm64::t-offset))
  @done
  (ret))

(defarm64lapfunction %object-in-heap-area-p ((object arg_y) (area arg_z))
  (ldr imm0 (:@ area (:$ arm64::area.low)))
  (ldr imm1 (:@ area (:$ arm64::area.active)))
  (mov arg_z rnil)
  (cmp object imm0)
  (b.lo @done)
  (cmp object imm1)
  (b.hs @done)
  (add arg_z rnil (:$ arm64::t-offset))
  @done
  (ret))


;;; Walk a static area, calling function f on each object.
;;;
;;; NOTE: On ARM64 with TBI tagging, distinguishing cons cells from misc
;;; objects is done by checking if the first word at an address looks like
;;; a uvector header (bit 7 of low byte set, top byte = 0 for reasonable
;;; element counts).  This can false-positive for cons cells whose CDR is
;;; a small positive fixnum with value in [128, 191].  In practice this
;;; doesn't occur in static areas containing compiler-generated data.

(defarm64lapfunction walk-static-area ((a arg_y) (f arg_z))
  (let ((fun temp0)
        (obj temp1)
        (limit temp2)
        (header imm0)
        (tag imm1)
        (subtag imm2))
    (build-lisp-frame)
    (mov fun f)
    (ldr limit (:@ a (:$ arm64::area.active)))
    (ldr obj (:@ a (:$ arm64::area.low)))
    (b @test)
    @loop
    (ldr header (:@ obj (:$ 0)))
    ;; Check if this looks like a uvector header:
    ;; Headers have subtag (low byte) >= #x80 and top byte = 0.
    ;; Tagged Lisp values (cons CDR) have non-zero top byte (except positive fixnums).
    (lsr tag header (:$ 56))                ; get top byte
    (cbnz tag @cons-cell)                   ; non-zero top byte → tagged value → cons
    (tst header (:$ #x80))                  ; check bit 7 of low byte
    (b.ne @misc)                            ; bit 7 set → uvector header
    @cons-cell
    ;; Tag as cons: effective addr = obj + cons-bias (8), tag byte = tag-cons (0x03)
    (add arg_z obj (:$ arm64::cons-bias))
    (movk arg_z (:$ #x0300) (:lsl 48))     ; set tag byte to tag-cons
    (set-nargs 1)
    (vpush1 fun)
    (vpush1 obj)
    (vpush1 limit)
    (mov nfn fun)
    (spcall .SPfuncall)
    (vpop1 limit)
    (vpop1 obj)
    (vpop1 fun)
    (add obj obj (:$ arm64::cons.size))
    (b @test)
    @misc
    ;; Tag as misc: effective addr = obj + misc-bias (8), tag byte = uvector-ref
    (add arg_z obj (:$ arm64::misc-bias))
    ;; Determine the tag byte from the subtag: use generic tagging.
    ;; ivector subtags: tag = uvector-ref (0x40)
    ;; gvector subtags (bit 5 set): tag = uvector-ref | gvector bit
    ;; Actually, ALL uvector references use uvector-ref (0x40) as the tag byte.
    (movk arg_z (:$ #x4000) (:lsl 48))     ; set tag byte to uvector-ref (0x40)
    (vpush1 fun)
    (vpush1 obj)
    (vpush1 limit)
    (set-nargs 1)
    (mov nfn fun)
    (spcall .SPfuncall)
    (vpop1 limit)
    (vpop1 obj)
    (vpop1 fun)
    ;; Compute size of this misc object and advance obj.
    ;; Reload header (may have moved, but we saved obj).
    (ldr header (:@ obj (:$ 0)))
    (lsr subtag header (:$ arm64::subtag-shift))     ; extract subtag
    (ubfx header header (:$ 0) (:$ arm64::subtag-shift))  ; element count
    ;; Determine byte size from subtag range.
    ;; Default: assume gvector (node-size per element) → bytes = count << 3
    (tst subtag (:$ arm64::gvector-tag-mask))  ; bit 5 set = gvector
    (b.eq @ivector-size)
    ;; Gvector: bytes = element_count * 8
    (lsl header header (:$ arm64::word-shift))
    (b @bump)
    @ivector-size
    ;; Ivector: determine element size from subtag range
    (cmp subtag (:$ arm64::max-32-bit-ivector-subtag))
    (b.hi @not-32bit)
    ;; 32-bit elements: bytes = count * 4
    (lsl header header (:$ 2))
    (b @bump)
    @not-32bit
    (cmp subtag (:$ arm64::max-64-bit-ivector-subtag))
    (b.hi @not-64bit)
    ;; 64-bit elements: bytes = count * 8
    (lsl header header (:$ 3))
    (b @bump)
    @not-64bit
    (cmp subtag (:$ arm64::max-8-bit-ivector-subtag))
    (b.hi @not-8bit)
    ;; 8-bit elements: bytes = count (no shift)
    (b @bump)
    @not-8bit
    (cmp subtag (:$ arm64::max-16-bit-ivector-subtag))
    (b.hi @not-16bit)
    ;; 16-bit elements: bytes = count * 2
    (lsl header header (:$ 1))
    (b @bump)
    @not-16bit
    (cmp subtag (:$ arm64::subtag-complex-double-float-vector))
    (b.ne @check-bitvector)
    ;; 128-bit elements: bytes = count * 16
    (lsl header header (:$ 4))
    (b @bump)
    @check-bitvector
    ;; bit-vector: bytes = ceil(count / 8)
    (add header header (:$ 7))
    (lsr header header (:$ 3))
    @bump
    ;; total = header_word (8) + data_bytes, rounded up to dnode (16)
    (add header header (:$ (+ arm64::node-size 15)))
    (and header header (:$ -16))            ; align to 16 bytes (dnode)
    (add obj obj header)
    @test
    (cmp obj limit)
    (b.lo @loop)
    (return-lisp-frame)))



;;; This walks the active "dynamic" area.  Objects might be moving around
;;; while we're doing this, so we have to be a lot more careful than we
;;; are when walking a static area.
;;; Allocate a "sentinel" cons, and terminate when we run into it.
;;; See walk-static-area NOTE about header/fixnum ambiguity on ARM64.

(defarm64lapfunction %walk-dynamic-area ((a arg_y) (f arg_z))
  (let ((fun temp1)
        (obj temp0)
        (sentinel temp2)
        (header imm0)
        (tag imm1)
        (subtag imm2))
    (ref-global imm1 tenured-area)
    (build-lisp-frame)
    ;; Allocate a sentinel cons cell.
    ;; Clear allocbase so the alloc trap fires if needed.
    (mov imm0 (:$ -8))
    (str imm0 (:@ rcontext (:$ arm64::tcr.save-allocbase)))
    (cmp imm1 (:$ 0))
    (mov fun f)
    (b.eq @no-tenured)
    (mov a imm1)
    @no-tenured
    (sub allocptr allocptr (:$ (- arm64::cons.size arm64::node-size)))
    (ldr imm1 (:@ rcontext (:$ arm64::tcr.save-allocbase)))
    (cmp allocptr imm1)
    (b.hi @no-trap)
    (uuo-alloc-trap)
    @no-trap
    (mov sentinel allocptr)
    ;; Clear allocptr low bits and high byte (TBI tag protection)
    (and allocptr allocptr (:$ #x00FFFFFFFFFFFFFFF0))
    (ldr obj (:@ a (:$ arm64::area.low)))
    (b @test)
    @loop
    (ldr header (:@ obj (:$ 0)))
    ;; Distinguish header from cons CDR (same logic as walk-static-area)
    (lsr tag header (:$ 56))
    (cbnz tag @dyn-cons)
    (tst header (:$ #x80))
    (b.ne @dyn-misc)
    @dyn-cons
    ;; Tag as cons
    (add arg_z obj (:$ arm64::cons-bias))
    (movk arg_z (:$ #x0300) (:lsl 48))
    (cmp arg_z sentinel)
    (b.hs @done)
    (set-nargs 1)
    (vpush1 arg_z)
    (vpush1 fun)
    (vpush1 sentinel)
    (mov nfn fun)
    (spcall .SPfuncall)
    (vpop1 sentinel)
    (vpop1 fun)
    (vpop1 obj)
    ;; Untag cons and advance
    (lsl obj obj (:$ 8))
    (lsr obj obj (:$ 8))                    ; clear tag byte
    (sub obj obj (:$ arm64::cons-bias))     ; back to raw address
    (add obj obj (:$ arm64::cons.size))
    (b @test)
    @dyn-misc
    ;; Tag as misc
    (add arg_z obj (:$ arm64::misc-bias))
    (movk arg_z (:$ #x4000) (:lsl 48))
    (vpush1 arg_z)
    (vpush1 fun)
    (vpush1 sentinel)
    (set-nargs 1)
    (mov nfn fun)
    (spcall .SPfuncall)
    (vpop1 sentinel)
    (vpop1 fun)
    (vpop1 obj)
    ;; Untag misc
    (lsl obj obj (:$ 8))
    (lsr obj obj (:$ 8))
    (sub obj obj (:$ arm64::misc-bias))
    ;; Compute size and advance (same as walk-static-area)
    (ldr header (:@ obj (:$ 0)))
    (lsr subtag header (:$ arm64::subtag-shift))
    (ubfx header header (:$ 0) (:$ arm64::subtag-shift))
    (tst subtag (:$ arm64::gvector-tag-mask))
    (b.eq @div-size)
    (lsl header header (:$ arm64::word-shift))
    (b @dbump)
    @div-size
    (cmp subtag (:$ arm64::max-32-bit-ivector-subtag))
    (b.hi @dnot32)
    (lsl header header (:$ 2))
    (b @dbump)
    @dnot32
    (cmp subtag (:$ arm64::max-64-bit-ivector-subtag))
    (b.hi @dnot64)
    (lsl header header (:$ 3))
    (b @dbump)
    @dnot64
    (cmp subtag (:$ arm64::max-8-bit-ivector-subtag))
    (b.hi @dnot8)
    (b @dbump)
    @dnot8
    (cmp subtag (:$ arm64::max-16-bit-ivector-subtag))
    (b.hi @dnot16)
    (lsl header header (:$ 1))
    (b @dbump)
    @dnot16
    (cmp subtag (:$ arm64::subtag-complex-double-float-vector))
    (b.ne @dcheck-bv)
    (lsl header header (:$ 4))
    (b @dbump)
    @dcheck-bv
    (add header header (:$ 7))
    (lsr header header (:$ 3))
    @dbump
    (add header header (:$ (+ arm64::node-size 15)))
    (and header header (:$ -16))
    (add obj obj header)
    @test
    (cmp obj sentinel)
    (b.lo @loop)
    @done
    (return-lisp-frame)))



(defun walk-dynamic-area (area func)
  (with-other-threads-suspended
      (%walk-dynamic-area area func)))



(defarm64lapfunction %class-of-instance ((i arg_z))
  (svref arg_z instance.class-wrapper i)
  (svref arg_z %wrapper-class arg_z)
  (ret))

(defarm64lapfunction class-of ((x arg_z))
  (check-nargs 1)
  (extract-fulltag imm0 x)
  ;; On ARM64 TBI: fulltag is the top byte. For misc objects, fulltag = uvector-ref (0x40+).
  ;; For non-misc, fulltag IS the typecode.
  (cmp imm0 (:$ arm64::uvector-ref))
  (b.hs @misc)                             ; fulltag >= 0x40 = misc reference
  ;; Not misc: use the tag byte directly as typecode
  (b @done)
  @misc
  ;; Misc object: extract subtag from header
  (extract-subtag imm0 x)
  @done
  ;; Scale typecode to index: typecode * 8 (word-shift) for 64-bit slot access
  (lsl imm0 imm0 (:$ arm64::word-shift))
  (ldr temp1 (:@ nfn '*class-table*))
  (add imm0 imm0 (:$ arm64::misc-data-offset))
  (ldr temp1 (:@ temp1 (:$ arm64::symbol.vcell)))
  (ldr temp0 (:@ temp1 imm0))              ; get entry from table
  (cmp temp0 rnil)
  (b.eq @bad)
  ;; functionp?
  (extract-typecode imm1 temp0)
  (cmp imm1 (:$ arm64::subtag-function))
  (b.ne @ret)                              ; not function - return entry
  ;; else jump to the fn
  (set-nargs 1)
  (mov nfn temp0)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr)
  @bad
  (set-nargs 1)
  (ldr fname (:@ nfn 'no-class-error))
  (ldr nfn (:@ fname (:$ arm64::symbol.fcell)))
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr)
  @ret
  (mov arg_z temp0)                        ; return frob from table
  (ret))

(defarm64lapfunction full-gccount ()
  (ref-global arg_z tenured-area)
  (cmp arg_z (:$ 0))
  (b.ne @from-area)
  (ref-global arg_z gc-count)
  (ret)
  @from-area
  (ldr arg_z (:@ arg_z (:$ arm64::area.gc-count)))
  (ret))


(defarm64lapfunction gc ()
  (check-nargs 0)
  (mov imm0 (:$ arch::gc-trap-function-gc))
  (uuo-gc-trap)
  (mov arg_z rnil)
  (ret))


;;; Make a list.  This can be faster than doing so by doing CONS
;;; repeatedly, since the latter strategy might trigger the GC several
;;; times if N is large.
(defarm64lapfunction %allocate-list ((initial-element arg_y) (nconses arg_z))
  (check-nargs 2)
  (build-lisp-frame)
  (mov fn nfn)
  (uuo-kernel-service (:$ arch::error-allocate-list))
  (vpush1 arg_z)
  (vpush1 arg_y)
  (set-nargs 2)
  (spjump .SPnvalret))



(defarm64lapfunction egc ((arg arg_z))
  "Enable the EGC if arg is non-nil, disables the EGC otherwise. Return
the previous enabled status. Although this function is thread-safe (in
the sense that calls to it are serialized), it doesn't make a whole lot
of sense to be turning the EGC on and off from multiple threads ..."
  (check-nargs 1)
  (sub imm1 arg rnil)
  (mov imm0 (:$ arch::gc-trap-function-egc-control))
  (uuo-gc-trap)
  (ret))



(defarm64lapfunction %configure-egc ((e0size arg_x)
                                     (e1size arg_y)
                                     (e2size arg_z))
  (check-nargs 3)
  (mov imm0 (:$ arch::gc-trap-function-configure-egc))
  (uuo-gc-trap)
  (ret))

(defarm64lapfunction purify ()
  (mov imm0 (:$ arch::gc-trap-function-purify))
  (uuo-gc-trap)
  (mov arg_z rnil)
  (ret))


(defarm64lapfunction impurify ()
  (mov imm0 (:$ arch::gc-trap-function-impurify))
  (uuo-gc-trap)
  (mov arg_z rnil)
  (ret))

(defarm64lapfunction lisp-heap-gc-threshold ()
  "Return the value of the kernel variable that specifies the amount
of free space to leave in the heap after full GC."
  (check-nargs 0)
  (mov imm0 (:$ arch::gc-trap-function-get-lisp-heap-threshold))
  (uuo-gc-trap)
  (spjump .SPmakeu64))

(defarm64lapfunction set-lisp-heap-gc-threshold ((new arg_z))
  "Set the value of the kernel variable that specifies the amount of free
space to leave in the heap after full GC to new-value, which should be a
non-negative fixnum. Returns the value of that kernel variable (which may
be somewhat larger than what was specified)."
  (check-nargs 1)
  (build-lisp-frame)
  (spcall .SPgetu64)
  (mov imm1 imm0)
  (mov imm0 (:$ arch::gc-trap-function-set-lisp-heap-threshold))
  (uuo-gc-trap)
  (return-lisp-frame)
  (spjump .SPmakeu64))


(defarm64lapfunction use-lisp-heap-gc-threshold ()
  "Try to grow or shrink lisp's heap space, so that the free space is
(approximately) equal to the current heap threshold. Return NIL"
  (check-nargs 0)
  (mov imm0 (:$ arch::gc-trap-function-use-lisp-heap-threshold))
  (uuo-gc-trap)
  (mov arg_z rnil)
  (ret))



(defarm64lapfunction allow-heap-allocation ((arg arg_z))
  "If ARG is false, signal an ALLOCATION-DISABLED condition on attempts
at heap allocation."
  (:arglist (arg))
  (check-nargs 1)
  (cmp arg_z rnil)
  (mov imm0 (:$ arch::gc-trap-function-allocation-control))
  (mov imm1 (:$ 0))                        ;disallow
  (b.eq @do-trap)
  (mov imm1 (:$ 1))                        ;allow if arg non-null
  @do-trap
  (uuo-gc-trap)
  (ret))



(defarm64lapfunction heap-allocation-allowed-p ()
  "Return T if heap allocation is allowed, NIL otherwise."
  (check-nargs 0)
  (mov imm0 (:$ arch::gc-trap-function-allocation-control))
  (mov imm1 (:$ 2))                        ;query
  (uuo-gc-trap)
  (ret))

(defun %watch (uvector)
  (declare (ignore uvector))
  (error "watching objects not supported on ARM64 yet"))

(defun %unwatch (watched new)
  (declare (ignore watched new))
  (error "watching objects not supported on ARM64 yet"))



(defarm64lapfunction %ensure-static-conses ()
  (check-nargs 0)
  (mov imm0 (:$ arch::gc-trap-function-ensure-static-conses))
  (uuo-gc-trap)
  (mov arg_z rnil)
  (ret))

(defarm64lapfunction set-gc-notification-threshold ((threshold arg_z))
  "Set the value of the kernel variable that can be used to trigger
GC notifications."
  (check-nargs 1)
  (build-lisp-frame)
  (spcall .SPgetu64)
  (mov imm1 imm0)
  (mov imm0 (:$ arch::gc-trap-function-set-gc-notification-threshold))
  (uuo-gc-trap)
  (return-lisp-frame)
  (spjump .SPmakeu64))

(defarm64lapfunction get-gc-notification-threshold ()
  "Get the value of the kernel variable that can be used to trigger
GC notifications."
  (check-nargs 0)
  (mov imm0 (:$ arch::gc-trap-function-get-gc-notification-threshold))
  (uuo-gc-trap)
  (spjump .SPmakeu64))


(defparameter *kernel-import-table* nil)

(defun %kernel-import (offset)
  (declare (fixnum offset)
           (optimize (speed 3) (safety 0)))
  (let* ((table (or *kernel-import-table*
                    (setq *kernel-import-table* (make-array target::num-kernel-imports))))
         ;; ARM64: node-size = 8, so divide by 8 (word-shift=3) for index
         (idx (ash offset (- arm64::word-shift)))
         (p (svref table idx)))
    (declare (simple-vector table) (fixnum idx))
    (if (typep p 'macptr) ; not dead-macptr from earlier session
      p
      (setf (svref table idx) (%kernel-import-internal offset)))))

;;; offset is a fixnum, one of the arm64::kernel-import-xxx constants.
;;; Returns that kernel import as a MACPTR.
;;; ARM64: fixnumshift=0, so offset IS the byte offset.
(defarm64lapfunction %kernel-import-internal ((offset arg_z))
  (ref-global imm0 kernel-imports)
  ;; ARM64: fixnumshift=0, so offset = byte offset directly.
  ;; Load the pointer from the kernel imports table.
  (ldr imm0 (:@ imm0 offset))
  ;; Allocate a macptr object.
  (lri imm1 arm64::macptr-header)
  (sub allocptr allocptr (:$ (- arm64::macptr.size arm64::node-size)))
  (ldr arg_z (:@ rcontext (:$ arm64::tcr.save-allocbase)))
  (cmp allocptr arg_z)
  (b.hi @no-trap)
  (uuo-alloc-trap)
  @no-trap
  ;; Store header at allocptr - node-size
  (stur imm1 (:@ allocptr (:$ (- arm64::node-size))))
  ;; Tag the result: effective addr = allocptr, tag = uvector-ref (0x40)
  (mov arg_z allocptr)
  (movk arg_z (:$ #x4000) (:lsl 48))
  ;; Clear allocptr low bits and high byte (TBI tag protection)
  (and allocptr allocptr (:$ #x00FFFFFFFFFFFFFFF0))
  ;; Store the import address in the macptr
  (str imm0 (:@ arg_z (:$ arm64::macptr.address)))
  (ret))

(defarm64lapfunction %get-unboxed-ptr ((macptr arg_z))
  (macptr-ptr imm0 arg_z)
  (ldr arg_z (:@ imm0 (:$ 0)))
  (ret))


(defarm64lapfunction %revive-macptr ((p arg_z))
  ;; Change subtag-dead-macptr to subtag-macptr in the header.
  ;; Load header, clear low byte, set new subtag.
  (ldur imm0 (:@ p (:$ arm64::misc-header-offset)))
  (and imm0 imm0 (:$ #xffffffffffffff00))  ; clear low byte
  (orr imm0 imm0 (:$ arm64::subtag-macptr))
  (stur imm0 (:@ p (:$ arm64::misc-header-offset)))
  (ret))

(defarm64lapfunction %macptr-type ((p arg_z))
  (check-nargs 1)
  (trap-unless-xtype= p arm64::subtag-macptr)
  (svref imm0 arm64::macptr.type-cell p)
  (box-fixnum arg_z imm0)
  (ret))

(defarm64lapfunction %macptr-domain ((p arg_z))
  (check-nargs 1)
  (trap-unless-xtype= p arm64::subtag-macptr)
  (svref imm0 arm64::macptr.domain-cell p)
  (box-fixnum arg_z imm0)
  (ret))

(defarm64lapfunction %set-macptr-type ((p arg_y) (new arg_z))
  (check-nargs 2)
  (unbox-fixnum imm1 new)
  (trap-unless-xtype= p arm64::subtag-macptr)
  (svset imm1 arm64::macptr.type-cell p)
  (ret))

(defarm64lapfunction %set-macptr-domain ((p arg_y) (new arg_z))
  (check-nargs 2)
  (unbox-fixnum imm1 new)
  (trap-unless-xtype= p arm64::subtag-macptr)
  (svset imm1 arm64::macptr.domain-cell p)
  (ret))

(defarm64lapfunction true ()
  (:arglist (&rest ignore))
  ;; ARM64: nargs counts in bytes (node-size=8), so 3 args = 24
  (cmp nargs (:$ 24))
  (mov arg_z rnil)
  (add arg_z arg_z (:$ arm64::t-offset))
  (b.ls @done)
  (sub imm0 nargs (:$ 24))
  (add vsp vsp imm0)
  @done
  (ret))

(defarm64lapfunction false ()
  (:arglist (&rest ignore))
  (cmp nargs (:$ 24))
  (mov arg_z rnil)
  (b.ls @done)
  (sub imm0 nargs (:$ 24))
  (add vsp vsp imm0)
  @done
  (ret))

(defarm64lapfunction constant-ref ()
  (:arglist (&rest ignore))
  (cmp nargs (:$ 24))
  (ldr arg_z (:@ nfn 'constant))
  (b.ls @done)
  (sub imm0 nargs (:$ 24))
  (add vsp vsp imm0)
  @done
  (ret))

;;; end
