;;; -*- Mode: Lisp; Package: CCL -*-
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

;;; level-0;ARM64;arm64-misc.lisp


(in-package "CCL")


;;; Copy N bytes from pointer src, starting at byte offset src-offset,
;;; to ivector dest, starting at offset dest-offset.
;;; Depending on alignment, it might make sense to move more than
;;; a byte at a time.
;;; Does no arg checking of any kind.  Really.

(defun %copy-ptr-to-ivector (src src-byte-offset dest dest-byte-offset nbytes)
  (declare (fixnum src-byte-offset dest-byte-offset nbytes)
           (optimize (speed 3) (safety 0)))
  (let* ((ptr-align (logand 7 (%ptr-to-int src))))
    (declare (type (mod 8) ptr-align))
    (if (and (>= nbytes 64)
             (= 0 (logand nbytes 7))
             (= 0 (logand dest-byte-offset 7))
             (= 0 (logand (the fixnum (+ ptr-align src-byte-offset)) 7)))
      (%copy-ptr-to-ivector-64bit src src-byte-offset dest dest-byte-offset nbytes)
      (%copy-ptr-to-ivector-8bit src src-byte-offset dest dest-byte-offset nbytes))
    dest))

(defarm64lapfunction %copy-ptr-to-ivector-8bit ((src (* 1 arm64::node-size))
                                                 (src-byte-offset 0)
                                                 (dest arg_x)
                                                 (dest-byte-offset arg_y)
                                                 (nbytes arg_z))
  (let ((src-reg imm0)
        (src-byteptr temp2)
        (src-node-reg temp0)
        (dest-byteptr imm2)
        (val imm1)
        (node-temp temp1))
    (cmp nbytes (:$ 0))
    (ldr src-node-reg (:@ vsp (:$ src)))
    (macptr-ptr src-reg src-node-reg)
    (ldr src-byteptr (:@ vsp (:$ src-byte-offset)))
    (add src-reg src-reg src-byteptr)          ; fixnumshift=0, no unboxing needed
    (mov dest-byteptr dest-byte-offset)        ; unbox-fixnum is identity
    (b @test)
    @loop
    (subs nbytes nbytes (:$ 1))
    (ldrb val (:@+ src-reg (:$ 1)))
    (strb val (:@ dest dest-byteptr))
    (add dest-byteptr dest-byteptr (:$ 1))
    @test
    (b.ne @loop)
    (mov arg_z dest)
    (add vsp vsp (:$ (* 2 arm64::node-size)))
    (ret)))

;;; Everything's aligned OK and NBYTES is a multiple of 8.
;;; Simple 8-byte-at-a-time loop (no VFP/computed branch like ARM32).
(defarm64lapfunction %copy-ptr-to-ivector-64bit ((src (* 1 arm64::node-size))
                                                  (src-byte-offset 0)
                                                  (dest arg_x)
                                                  (dest-byte-offset arg_y)
                                                  (nbytes arg_z))
  (let ((src-reg imm0)
        (src-node-reg temp0)
        (dest-ptr imm2)
        (val imm1))
    (ldr src-node-reg (:@ vsp (:$ src)))
    (ldr val (:@ vsp (:$ src-byte-offset)))
    (macptr-ptr src-reg src-node-reg)
    (add src-reg src-reg val)
    (add dest-ptr dest dest-byte-offset)       ; TBI: tagged pointer works as address
    @loop
    (ldr val (:@+ src-reg (:$ 8)))
    (str val (:@+ dest-ptr (:$ 8)))
    (subs nbytes nbytes (:$ 8))
    (b.ne @loop)
    (mov arg_z dest)
    (add vsp vsp (:$ (* 2 arm64::node-size)))
    (ret)))


(defun %copy-ivector-to-ptr (src src-byte-offset dest dest-byte-offset nbytes)
  (declare (fixnum src-byte-offset dest-byte-offset nbytes)
           (optimize (speed 3) (safety 0)))
  (let* ((ptr-align (logand (the (unsigned-byte 64) (%ptr-to-int dest)) 7)))
    (declare (type (mod 8) ptr-align))
    (if (or (< nbytes 64)
            (not (= 0 (logand nbytes 7)))
            (not (= 0 (logand src-byte-offset 7)))
            (not (= 0 (logand (the fixnum (+ ptr-align dest-byte-offset)) 7))))
      (%copy-ivector-to-ptr-8bit src src-byte-offset dest dest-byte-offset nbytes)
      (%copy-ivector-to-ptr-64bit src src-byte-offset dest dest-byte-offset nbytes))
    dest))

(defarm64lapfunction %copy-ivector-to-ptr-8bit ((src (* 1 arm64::node-size))
                                                 (src-byte-offset 0)
                                                 (dest arg_x)
                                                 (dest-byte-offset arg_y)
                                                 (nbytes arg_z))
  (ldr temp0 (:@ vsp (:$ src)))
  (cmp nbytes (:$ 0))
  (ldr imm0 (:@ vsp (:$ src-byte-offset)))
  ;; fixnumshift=0, no unboxing needed; misc-data-offset=0
  (macptr-ptr imm1 dest)
  (add imm1 imm1 dest-byte-offset)
  (b @test)
  @loop
  (subs nbytes nbytes (:$ 1))
  (ldrb imm2 (:@ temp0 imm0))
  (add imm0 imm0 (:$ 1))
  (strb imm2 (:@+ imm1 (:$ 1)))
  @test
  (b.ne @loop)
  (mov arg_z dest)
  (add vsp vsp (:$ (* 2 arm64::node-size)))
  (ret))

;;; Everything's aligned OK and NBYTES is a multiple of 8.
(defarm64lapfunction %copy-ivector-to-ptr-64bit ((src (* 1 arm64::node-size))
                                                  (src-byte-offset 0)
                                                  (dest arg_x)
                                                  (dest-byte-offset arg_y)
                                                  (nbytes arg_z))
  (let ((src-ptr imm0)
        (dest-reg imm1)
        (val imm2))
    (ldr temp0 (:@ vsp (:$ src)))
    (ldr src-ptr (:@ vsp (:$ src-byte-offset)))
    (add src-ptr temp0 src-ptr)                ; ivector + byte offset (TBI OK)
    (macptr-ptr dest-reg dest)
    (add dest-reg dest-reg dest-byte-offset)
    @loop
    (ldr val (:@+ src-ptr (:$ 8)))
    (str val (:@+ dest-reg (:$ 8)))
    (subs nbytes nbytes (:$ 8))
    (b.ne @loop)
    (mov arg_z dest)
    (add vsp vsp (:$ (* 2 arm64::node-size)))
    (ret)))


(defun %copy-ivector-to-ivector (src src-byte-offset dest dest-byte-offset nbytes)
  (declare (fixnum src-byte-offset dest-byte-offset nbytes))
  (if (or (not (eq src dest))
          (< dest-byte-offset src-byte-offset)
          (>= dest-byte-offset (the fixnum (+ src-byte-offset nbytes))))
    (%copy-ivector-to-ivector-postincrement src src-byte-offset dest dest-byte-offset nbytes)
    (if (and (eq src dest)
             (eql src-byte-offset dest-byte-offset))
      dest
      (%copy-ivector-to-ivector-predecrement src
                                             (the fixnum (+ src-byte-offset nbytes))
                                             dest
                                             (the fixnum (+ dest-byte-offset nbytes))
                                             nbytes)))
  dest)

(defun %copy-ivector-to-ivector-postincrement (src src-byte-offset dest dest-byte-offset nbytes)
  (declare (fixnum src-byte-offset dest-byte-offset nbytes))
  (cond ((or (< nbytes 16)
             (not (= (logand src-byte-offset 7)
                     (logand dest-byte-offset 7))))
         (%copy-ivector-to-ivector-postincrement-8bit src src-byte-offset dest dest-byte-offset nbytes))
        (t
         (let* ((prefix-size (- 8 (logand src-byte-offset 7))))
           (declare (fixnum prefix-size))
           (unless (= 8 prefix-size)
             (%copy-ivector-to-ivector-postincrement-8bit src src-byte-offset dest dest-byte-offset prefix-size)
             (incf src-byte-offset prefix-size)
             (incf dest-byte-offset prefix-size)
             (decf nbytes prefix-size)))
         (let* ((tail-size (logand nbytes 7))
                (fullword-size (- nbytes tail-size)))
           (declare (fixnum tail-size fullword-size))
           (unless (zerop fullword-size)
             (%copy-ivector-to-ivector-postincrement-64bit src src-byte-offset dest dest-byte-offset fullword-size))
           (unless (zerop tail-size)
             (%copy-ivector-to-ivector-postincrement-8bit src (the fixnum (+ src-byte-offset fullword-size)) dest (the fixnum (+ dest-byte-offset fullword-size)) tail-size))))))

(defun %copy-ivector-to-ivector-predecrement (src src-byte-offset dest dest-byte-offset nbytes)
  (declare (fixnum src-byte-offset dest-byte-offset nbytes))
  (cond ((or (< nbytes 16)
             (not (= (logand src-byte-offset 7)
                     (logand dest-byte-offset 7))))
         (%copy-ivector-to-ivector-predecrement-8bit src src-byte-offset dest dest-byte-offset nbytes))
    (t
      (let* ((suffix-size (logand src-byte-offset 7)))
        (declare (fixnum suffix-size))
        (unless (zerop suffix-size)
          (%copy-ivector-to-ivector-predecrement-8bit src src-byte-offset dest dest-byte-offset suffix-size)
          (decf src-byte-offset suffix-size)
          (decf dest-byte-offset suffix-size)
          (decf nbytes suffix-size)))
      (let* ((head-size (logand nbytes 7))
             (fullword-size (- nbytes head-size)))
        (declare (fixnum head-size fullword-size))
        (unless (zerop fullword-size)
          (%copy-ivector-to-ivector-predecrement-64bit src src-byte-offset dest dest-byte-offset fullword-size))
        (unless (zerop head-size)
          (%copy-ivector-to-ivector-predecrement-8bit src (the fixnum (- src-byte-offset fullword-size)) dest (the fixnum (- dest-byte-offset fullword-size)) head-size))))
))

(defarm64lapfunction %copy-ivector-to-ivector-postincrement-8bit ((src (* 1 arm64::node-size))
                                                                   (src-byte-offset 0)
                                                                   (dest arg_x)
                                                                   (dest-byte-offset arg_y)
                                                                   (nbytes arg_z))
  (let ((rsrc temp0)
        (scaled-src-idx imm1)
        (scaled-dest-idx imm2)
        (val imm0))
    (cmp nbytes (:$ 0))
    (vpop1 scaled-src-idx)
    ;; fixnumshift=0: index is already raw; misc-data-offset=0
    (mov scaled-dest-idx dest-byte-offset)
    (vpop1 rsrc)
    (b @test)
    @loop
    (subs nbytes nbytes (:$ 1))
    (ldrb val (:@ rsrc scaled-src-idx))
    (add scaled-src-idx scaled-src-idx (:$ 1))
    (strb val (:@ dest scaled-dest-idx))
    (add scaled-dest-idx scaled-dest-idx (:$ 1))
    @test
    (b.ne @loop)
    (mov arg_z dest)
    (ret)))

;;; 8-byte aligned copy, nbytes is a multiple of 8.
(defarm64lapfunction %copy-ivector-to-ivector-postincrement-64bit ((src (* 1 arm64::node-size))
                                                                    (src-byte-offset 0)
                                                                    (dest arg_x)
                                                                    (dest-byte-offset arg_y)
                                                                    (nbytes arg_z))
  (let ((rsrc temp0)
        (scaled-src-idx imm1)
        (scaled-dest-idx imm2)
        (val imm0))
    (vpop1 scaled-src-idx)
    (mov scaled-dest-idx dest-byte-offset)
    (vpop1 rsrc)
    @loop
    (ldr val (:@ rsrc scaled-src-idx))
    (add scaled-src-idx scaled-src-idx (:$ 8))
    (str val (:@ dest scaled-dest-idx))
    (add scaled-dest-idx scaled-dest-idx (:$ 8))
    (subs nbytes nbytes (:$ 8))
    (b.ne @loop)
    (mov arg_z dest)
    (ret)))

(defarm64lapfunction %copy-ivector-to-ivector-predecrement-8bit ((src (* 1 arm64::node-size))
                                                                  (src-byte-offset 0)
                                                                  (dest arg_x)
                                                                  (dest-byte-offset arg_y)
                                                                  (nbytes arg_z))
  (let ((rsrc temp0)
        (scaled-src-idx imm1)
        (scaled-dest-idx imm2)
        (val imm0))
    (cmp nbytes (:$ 0))
    (vpop1 scaled-src-idx)
    (mov scaled-dest-idx dest-byte-offset)
    (vpop1 rsrc)
    (b @test)
    @loop
    (sub scaled-src-idx scaled-src-idx (:$ 1))
    (sub scaled-dest-idx scaled-dest-idx (:$ 1))
    (subs nbytes nbytes (:$ 1))
    (ldrb val (:@ rsrc scaled-src-idx))
    (strb val (:@ dest scaled-dest-idx))
    @test
    (b.ne @loop)
    (mov arg_z dest)
    (ret)))

;;; 8-byte aligned predecrement copy, nbytes is a multiple of 8.
(defarm64lapfunction %copy-ivector-to-ivector-predecrement-64bit ((src (* 1 arm64::node-size))
                                                                   (src-byte-offset 0)
                                                                   (dest arg_x)
                                                                   (dest-byte-offset arg_y)
                                                                   (nbytes arg_z))
  (let ((rsrc temp0)
        (scaled-src-idx imm1)
        (scaled-dest-idx imm2)
        (val imm0))
    (vpop1 scaled-src-idx)
    (mov scaled-dest-idx dest-byte-offset)
    (vpop1 rsrc)
    @loop
    (sub scaled-src-idx scaled-src-idx (:$ 8))
    (sub scaled-dest-idx scaled-dest-idx (:$ 8))
    (ldr val (:@ rsrc scaled-src-idx))
    (str val (:@ dest scaled-dest-idx))
    (subs nbytes nbytes (:$ 8))
    (b.ne @loop)
    (mov arg_z dest)
    (ret)))

;;; Unless we're sure that DEST is newly-created, we have to do this
;;; in a way that honors the write barrier.
(defun %copy-gvector-to-gvector (src src-element dest dest-element nelements)
  (declare (fixnum src-element dest-element nelements)
           (optimize (speed 3) (safety 0)))
  (if (or (not (eq src dest))
          (< dest-element src-element)
          (>= dest-element (the fixnum (+ src-element nelements))))
    (do* ()
         ((<= nelements 0) dest)
      (setf (%svref dest dest-element)
            (%svref src src-element))
      (incf dest-element)
      (incf src-element)
      (decf nelements))
    (do* ((src-element (+ src-element nelements))
          (dest-element (+ dest-element nelements)))
         ((<= nelements 0) dest)
      (declare (fixnum src-element dest-element))
      (decf src-element)
      (decf dest-element)
      (setf (%svref dest dest-element)
            (%svref src src-element))
      (decf nelements))))



(defarm64lapfunction %heap-bytes-allocated ()
  ;; ARM64: total-bytes-allocated is a single 64-bit field.
  (ldr imm2 (:@ rcontext (:$ arm64::tcr.last-allocptr)))
  (ldr imm0 (:@ rcontext (:$ arm64::tcr.total-bytes-allocated)))
  (cbz imm2 @go)
  ;; Check if allocptr is the "void" sentinel (-8)
  (cmn allocptr (:$ 8))
  (b.eq @go)
  (sub imm2 imm2 allocptr)
  (add imm0 imm0 imm2)
  @go
  (spjump .SPmakeu64))




(defarm64lapfunction values ()
  (:arglist (&rest values))
  (vpush-argregs)
  (add temp0 nargs vsp)
  (spjump .SPvalues))

;; It would be nice if (%setf-macptr macptr (ash (the fixnum value)
;; ash::fixnumshift)) would do this inline.
(defarm64lapfunction %setf-macptr-to-object ((macptr arg_y) (object arg_z))
  (check-nargs 2)
  (trap-unless-xtype= arg_y arm64::subtag-macptr)
  (str arg_z (:@ arg_y (:$ arm64::macptr.address)))
  (ret))

(defarm64lapfunction %fixnum-from-macptr ((macptr arg_z))
  (check-nargs 1)
  (trap-unless-xtype= arg_z arm64::subtag-macptr)
  (ldr imm0 (:@ arg_z (:$ arm64::macptr.address)))
  (trap-unless-fixnum imm0)
  (mov arg_z imm0)
  (ret))

;;; On ARM64, a "longlong" is a single 64-bit value (one register).
(defarm64lapfunction %%get-unsigned-longlong ((ptr arg_y) (offset arg_z))
  (trap-unless-xtype= ptr arm64::subtag-macptr)
  (macptr-ptr imm1 ptr)
  (add imm1 imm1 offset)              ; fixnumshift=0, offset is raw
  (ldr imm0 (:@ imm1 (:$ 0)))
  (spjump .SPmakeu64))



(defarm64lapfunction %%get-signed-longlong ((ptr arg_y) (offset arg_z))
  (trap-unless-xtype= ptr arm64::subtag-macptr)
  (macptr-ptr imm1 ptr)
  (add imm1 imm1 offset)
  (ldr imm0 (:@ imm1 (:$ 0)))
  (spjump .SPmakes64))



(defarm64lapfunction %%set-unsigned-longlong ((ptr arg_x)
                                              (offset arg_y)
                                              (val arg_z))
  (build-lisp-frame)
  (trap-unless-xtype= ptr arm64::subtag-macptr)
  (spcall .SPgetu64)
  (macptr-ptr imm2 ptr)
  (add imm2 imm2 offset)
  (str imm0 (:@ imm2 (:$ 0)))
  (return-lisp-frame))



(defarm64lapfunction %%set-signed-longlong ((ptr arg_x)
                                            (offset arg_y)
                                            (val arg_z))
  (build-lisp-frame)
  (trap-unless-xtype= ptr arm64::subtag-macptr)
  (spcall .SPgets64)
  (macptr-ptr imm2 ptr)
  (add imm2 imm2 offset)
  (str imm0 (:@ imm2 (:$ 0)))
  (return-lisp-frame))



(defarm64lapfunction interrupt-level ()
  (ldr arg_z (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (ldr arg_z (:@ arg_z (:$ arm64::interrupt-level-binding-index)))
  (ret))




(defarm64lapfunction set-interrupt-level ((new arg_z))
  (ldr imm1 (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (trap-unless-fixnum new)
  (str new (:@ imm1 (:$ arm64::interrupt-level-binding-index)))
  (ret))



(defarm64lapfunction %current-tcr ()
  (mov arg_z rcontext)
  (ret))

(defarm64lapfunction %tcr-toplevel-function ((tcr arg_z))
  (check-nargs 1)
  (ldr temp0 (:@ tcr (:$ arm64::tcr.vs-area)))
  (ldr imm1 (:@ temp0 (:$ arm64::area.high)))
  (cmp tcr rcontext)
  (b.eq @current)
  (ldr imm0 (:@ temp0 (:$ arm64::area.active)))
  (b @compare)
  @current
  (mov imm0 vsp)
  @compare
  (cmp imm1 imm0)
  (b.ne @has-function)
  (mov arg_z rnil)
  (ret)
  @has-function
  (ldur arg_z (:@ imm1 (:$ (- arm64::node-size))))
  (ret))

(defarm64lapfunction %set-tcr-toplevel-function ((tcr arg_y) (fun arg_z))
  (check-nargs 2)
  (ldr temp0 (:@ tcr (:$ arm64::tcr.vs-area)))
  (ldr imm1 (:@ temp0 (:$ arm64::area.high)))
  (cmp tcr rcontext)
  (b.eq @current)
  (ldr imm0 (:@ temp0 (:$ arm64::area.active)))
  (b @compare)
  @current
  (mov imm0 vsp)
  @compare
  (cmp imm1 imm0)
  (mov imm0 (:$ 0))
  ;; Push a slot at high: imm1 = high - node-size, store 0 there
  (sub imm1 imm1 (:$ arm64::node-size))
  (str imm0 (:@ imm1 (:$ 0)))
  (b.ne @not-empty)
  ;; Was empty: update active and save-vsp
  (str imm1 (:@ temp0 (:$ arm64::area.active)))
  (str imm1 (:@ tcr (:$ arm64::tcr.save-vsp)))
  @not-empty
  (str fun (:@ imm1 (:$ 0)))
  (ret))

;;; This needs to be done out-of-line, to handle EGC memoization.
(defarm64lapfunction %store-node-conditional ((offset 0) (object arg_x) (old arg_y) (new arg_z))
  (spjump .SPstore-node-conditional))

#+notyet                                ; needs a subprim on ARM64
(defarm64lapfunction %store-immediate-conditional ((offset 0) (object arg_x) (old arg_y) (new arg_z))
  (vpop temp0)
  (unbox-fixnum imm0 temp0)
  (let ((current temp1))
    @again
    (ldxr current (:@ object imm0))
    (cmp current old)
    (b.ne @lose)
    (stxr imm1 new (:@ object imm0))
    (cbnz imm1 @again)
    (add arg_z rnil (:$ arm64::t-offset))
    (ret)
    @lose
    (clrex)
    (mov arg_z rnil)
    (ret)))

(defarm64lapfunction set-%gcable-macptrs% ((ptr arg_z))
  (load-global-address imm1 arm64::gcable-pointers)
  @again
  (ldxr arg_y (:@ imm1))
  (str arg_y (:@ ptr (:$ arm64::xmacptr.link)))
  (stxr imm0 ptr (:@ imm1))
  (cbnz imm0 @again)
  (ret))

;;; Atomically increment or decrement the gc-inhibit-count kernel-global
;;; (It's decremented if it's currently negative, incremented otherwise.)
(defarm64lapfunction %lock-gc-lock ()
  (load-global-address imm1 arm64::gc-inhibit-count)
  @again
  (ldxr arg_y (:@ imm1))
  (cmp arg_y (:$ 0))
  (b.lt @negative)
  (add arg_z arg_y (:$ 1))
  (b @store)
  @negative
  (sub arg_z arg_y (:$ 1))
  @store
  (stxr imm0 arg_z (:@ imm1))
  (cbnz imm0 @again)
  (ret))

;;; Atomically decrement or increment the gc-inhibit-count kernel-global
;;; (It's incremented if it's currently negative, decremented otherwise.)
;;; If it's incremented from -1 to 0, try to GC (maybe just a little.)
(defarm64lapfunction %unlock-gc-lock ()
  (load-global-address imm1 arm64::gc-inhibit-count)
  @again
  (mov arg_x (:$ 0))
  (ldxr arg_y (:@ imm1))
  (cmn arg_y (:$ 1))                    ; compare with -1
  (b.gt @decrement)                     ; if > -1 (i.e., >= 0): decrement
  (b.ne @increment)                     ; if < -1: increment
  ;; arg_y == -1: set GC trigger flag
  (mov arg_x arg_y)
  @increment
  (add arg_z arg_y (:$ 1))
  (b @store)
  @decrement
  (sub arg_z arg_y (:$ 1))
  @store
  (stxr imm0 arg_z (:@ imm1))
  (cbnz imm0 @again)
  (cbz arg_x @done)
  ;; Trigger immediate GC
  (mov imm0 (:$ arch::gc-trap-function-immediate-gc))
  (uuo-gc-trap)
  @done
  (ret))



(defarm64lapfunction %atomic-incf-node ((by arg_x) (node arg_y) (disp arg_z))
  (spjump .SPatomic-incf-node))

(defarm64lapfunction %atomic-incf-ptr ((ptr arg_z))
  (macptr-ptr imm1 ptr)
  @again
  (ldxr imm0 (:@ imm1))
  (add imm0 imm0 (:$ 1))
  (stxr imm2 imm0 (:@ imm1))
  (cbnz imm2 @again)
  (box-fixnum arg_z imm0)
  (ret))


(defarm64lapfunction %atomic-incf-ptr-by ((ptr arg_y) (by arg_z))
  (macptr-ptr imm1 ptr)
  @again
  (ldxr imm0 (:@ imm1))
  (add imm0 imm0 by)                    ; fixnumshift=0, by is raw
  (stxr imm2 imm0 (:@ imm1))
  (cbnz imm2 @again)
  (box-fixnum arg_z imm0)
  (ret))

(defarm64lapfunction %atomic-decf-ptr ((ptr arg_z))
  (macptr-ptr imm1 ptr)
  @again
  (ldxr imm0 (:@ imm1))
  (sub imm0 imm0 (:$ 1))
  (stxr imm2 imm0 (:@ imm1))
  (cbnz imm2 @again)
  (box-fixnum arg_z imm0)
  (ret))

(defarm64lapfunction %atomic-decf-ptr-if-positive ((ptr arg_z))
  (macptr-ptr imm1 ptr)
  @again
  (ldxr imm0 (:@ imm1))
  (cmp imm0 (:$ 0))
  (b.eq @done)
  (sub imm0 imm0 (:$ 1))
  (stxr imm2 imm0 (:@ imm1))
  (cbnz imm2 @again)
  (box-fixnum arg_z imm0)
  (ret)
  @done
  (clrex)
  (box-fixnum arg_z imm0)
  (ret))


(defarm64lapfunction %atomic-swap-ptr ((ptr arg_y) (newval arg_z))
  (macptr-ptr imm1 ptr)
  (mov imm3 newval)                      ; fixnumshift=0, value is raw
  @again
  (ldxr imm0 (:@ imm1))
  (stxr imm2 imm3 (:@ imm1))
  (cbnz imm2 @again)
  (box-fixnum arg_z imm0)
  (ret))

;;; Try to store the fixnum NEWVAL at PTR, if and only if the old value
;;; was equal to OLDVAL.  Return the old value.
(defarm64lapfunction %ptr-store-conditional ((ptr arg_x) (expected-oldval arg_y) (newval arg_z))
  (macptr-ptr imm0 ptr)
  (mov imm3 newval)                      ; fixnumshift=0, value is raw
  @again
  (ldxr imm1 (:@ imm0))
  (cmp imm1 expected-oldval)             ; compare raw value with fixnum
  (b.ne @done)
  (stxr imm2 imm3 (:@ imm0))
  (cbnz imm2 @again)
  (box-fixnum arg_z imm1)
  (ret)
  @done
  (clrex)
  (box-fixnum arg_z imm1)
  (ret))

(defarm64lapfunction %ptr-store-fixnum-conditional ((ptr arg_x) (expected-oldval arg_y) (newval arg_z))
  (let ((address imm2)
        (actual-oldval imm1))
    (macptr-ptr address ptr)
    @again
    (ldxr actual-oldval (:@ address))
    (cmp actual-oldval expected-oldval)
    (b.ne @done)
    (stxr imm0 newval (:@ address))
    (cbnz imm0 @again)
    (mov arg_z actual-oldval)
    (ret)
    @done
    (clrex)
    (mov arg_z actual-oldval)
    (ret)))




(defarm64lapfunction %macptr->dead-macptr ((macptr arg_z))
  (check-nargs 1)
  (mov imm0 (:$ arm64::subtag-dead-macptr))
  ;; Subtag is the low byte of the header at misc-header-offset (-8)
  (sturb imm0 (:@ macptr (:$ arm64::misc-subtag-offset)))
  (ret))

#+notyet                                ;for different reasons
(defarm64lapfunction %%apply-in-frame ((catch-count imm0) (srv temp0) (tsp-count imm0) (db-link imm0)
                                       (parent arg_x) (function arg_y) (arglist arg_z))
  (check-nargs 7)
  ;; Too complex to port now; deferred.
  (uuo-debug-trap)
  (ret))




(defarm64lapfunction %%save-application ((flags arg_y) (fd arg_z))
  (mov imm0 flags)                       ; fixnumshift=0, already raw
  (orr imm0 imm0 (:$ arch::gc-trap-function-save-application))
  (mov imm1 fd)
  (uuo-gc-trap)
  (ret))



(defarm64lapfunction %misc-address-fixnum ((misc-object arg_z))
  (check-nargs 1)
  ;; On ARM64, misc-data-offset=0, and the tagged pointer IS the data address.
  ;; Clear the tag byte (bits 56-63) to get a clean fixnum address.
  (lsl arg_z arg_z (:$ 8))
  (lsr arg_z arg_z (:$ 8))
  (ret))


(defarm64lapfunction fudge-heap-pointer ((ptr arg_x) (subtype arg_y) (len arg_z))
  (check-nargs 3)
  (macptr-ptr imm1 ptr)                  ; raw address
  (add imm0 imm1 (:$ 9))                ; 2 for delta halfword + 7 for alignment
  (bic imm0 imm0 (:$ 7))                ; align to 8 bytes
  (sub imm1 imm0 imm1)                  ; delta = aligned - raw
  (sturh imm1 (:@ imm0 (:$ -2)))        ; save delta halfword
  ;; Construct header: (len << num-subtag-bits) | subtag
  ;; fixnumshift=0: subtype and len are already raw
  (mov imm1 subtype)
  (orr imm1 imm1 (:lsl len (:$ arm64::num-subtag-bits)))
  (str imm1 (:@ imm0 (:$ 0)))           ; store header
  ;; Tagged pointer = aligned + misc-bias (8), with reference tag in bits 56-63
  (add arg_z imm0 (:$ arm64::misc-bias))
  ;; Compute reference tag: subtag ^ 0xC0 (clear header bit 7, set ref bit 6)
  (eor imm1 subtype (:$ #xC0))
  (orr arg_z arg_z (:lsl imm1 (:$ arm64::tag-shift)))
  (ret))



(defarm64lapfunction %%make-disposable ((ptr arg_y) (vector arg_z))
  (check-nargs 2)
  ;; Clear tag byte and subtract bias to get header address
  (lsl imm0 vector (:$ 8))
  (lsr imm0 imm0 (:$ 8))                ; clear tag byte
  (sub imm0 imm0 (:$ arm64::misc-bias)) ; header address
  (ldurh imm1 (:@ imm0 (:$ -2)))        ; get delta
  (sub imm0 imm0 imm1)                  ; header_addr - delta = orig addr
  (str imm0 (:@ ptr (:$ arm64::macptr.address)))
  (ret))

(defarm64lapfunction %vect-data-to-macptr ((vect arg_y) (ptr arg_z))
  ;; On ARM64, misc-data-offset = misc-dfloat-offset = 0.
  ;; The tagged pointer (with TBI) is the data address.
  ;; Store a clean raw address in macptr.
  (lsl temp0 vect (:$ 8))
  (lsr temp0 temp0 (:$ 8))              ; clear tag byte
  (str temp0 (:@ arg_z (:$ arm64::macptr.address)))
  (ret))

(defarm64lapfunction %ivector-from-macptr ((ptr arg_z))
  ;; Assuming that PTR points to the first byte of vector data
  ;; (in an ivector allocated on a stack or in foreign memory),
  ;; return the (tagged) ivector.
  ;; On ARM64, misc-data-offset=0, so the raw pointer IS the effective address.
  ;; Load subtag from header (at effective_addr - 8) to determine reference tag.
  (macptr-ptr imm0 arg_z)
  (ldurb imm1 (:@ imm0 (:$ arm64::misc-header-offset))) ; low byte = subtag
  (eor imm1 imm1 (:$ #xC0))            ; reference tag = subtag ^ 0xC0
  (orr arg_z imm0 (:lsl imm1 (:$ arm64::tag-shift)))
  (ret))

(defun get-saved-register-values ()
  (values))

(defarm64lapfunction %current-db-link ()
  (ldr arg_z (:@ rcontext (:$ arm64::tcr.db-link)))
  (ret))

(defarm64lapfunction %no-thread-local-binding-marker ()
  ;; On ARM64 TBI, markers are immediates with the tag in bits 56-63.
  ;; The arch file pre-computes no-thread-local-binding-marker.
  (lri arg_z arm64::no-thread-local-binding-marker)
  (ret))



;;; Should be called with interrupts disabled.
(defarm64lapfunction %safe-get-ptr ((src arg_y) (dest arg_z))
  (check-nargs 2)
  (macptr-ptr imm0 src)
  (str imm0 (:@ rcontext (:$ arm64::tcr.safe-ref-address)))
  (ldr imm0 (:@ imm0 (:$ 0)))           ; may fault
  (str imm0 (:@ dest (:$ arm64::macptr.address)))
  (ret))



(defarm64lapfunction %%tcr-interrupt ((target arg_z))
  (check-nargs 1)
  (uuo-kernel-service (:$ arch::error-interrupt))
  (box-fixnum arg_z imm0)
  (ret))

(defarm64lapfunction %suspend-tcr ((target arg_z))
  (check-nargs 1)
  (uuo-kernel-service (:$ arch::error-suspend))
  (mov arg_z rnil)
  (cmp imm0 (:$ 0))
  (b.eq @done)
  (add arg_z rnil (:$ arm64::t-offset))
  @done
  (ret))

(defarm64lapfunction %suspend-other-threads ()
  (check-nargs 0)
  (uuo-kernel-service (:$ arch::error-suspend-all))
  (mov arg_z rnil)
  (cmp imm0 (:$ 0))
  (b.eq @done)
  (add arg_z rnil (:$ arm64::t-offset))
  @done
  (ret))

(defarm64lapfunction %resume-tcr ((target arg_z))
  (check-nargs 1)
  (uuo-kernel-service (:$ arch::error-resume))
  (mov arg_z rnil)
  (cmp imm0 (:$ 0))
  (b.eq @done)
  (add arg_z rnil (:$ arm64::t-offset))
  @done
  (ret))

(defarm64lapfunction %resume-other-threads ()
  (check-nargs 0)
  (uuo-kernel-service (:$ arch::error-resume-all))
  (mov arg_z rnil)
  (ret))

(defarm64lapfunction %kill-tcr ((target arg_z))
  (check-nargs 1)
  (uuo-kernel-service (:$ arch::error-kill))
  (mov arg_z rnil)
  (cmp imm0 (:$ 0))
  (b.eq @done)
  (add arg_z rnil (:$ arm64::t-offset))
  @done
  (ret))

(defarm64lapfunction pending-user-interrupt ()
  (mov temp0 (:$ 0))
  (ref-global arg_z arm64::intflag)
  (set-global temp0 arm64::intflag imm0)
  (ret))

#+later
(progn




(defarm64lapfunction %staticp ((x arg_z))
  (check-nargs 1)
  (ref-global temp0 arm64::static-cons-area)
  (ldr imm1 (:@ temp0 (:$ arm64::area.low)))
  (sub imm0 x imm1)
  (ldr imm1 (:@ temp0 (:$ arm64::area.ndnodes)))
  (lsr imm0 imm0 (:$ arm64::dnode-shift))
  (mov arg_z rnil)
  (sub imm1 imm1 imm0)
  (cmp imm1 (:$ 0))
  (b.le @done)
  (add imm1 imm1 (:$ 128))
  (box-fixnum arg_z imm1)
  @done
  (ret))

(defarm64lapfunction %static-inverse-cons ((n arg_z))
  (check-nargs 1)
  (extract-lisptag imm0 arg_z)
  (cmp imm0 (:$ 0))
  (ref-global temp0 arm64::static-cons-area)
  (b.ne @fail)
  (sub n n (:$ 128))
  (ldr imm0 (:@ temp0 (:$ arm64::area.ndnodes)))
  (ldr imm1 (:@ temp0 (:$ arm64::area.high)))
  (box-fixnum arg_y imm0)
  (sub imm1 imm1 n)
  (cmp arg_z arg_y)
  (sub imm1 imm1 n)
  (b.gt @fail)
  ;; Create tagged cons pointer: address + tag in bits 56-63
  (mov imm2 (:$ arm64::tag-cons))
  (orr arg_z imm1 (:lsl imm2 (:$ arm64::tag-shift)))
  (ldr arg_y (:@ arg_z (:$ arm64::cons.car)))
  ;; Check for unbound marker
  (lsr imm0 arg_y (:$ arm64::tag-shift))
  (cmp imm0 (:$ arm64::tag-unbound))
  (b.ne @out)
  @fail
  (mov arg_z rnil)
  @out
  (ret))

);#+later

(defarm64lapfunction xchgl ((newval arg_y) (ptr arg_z))
  (mov imm3 newval)                      ; fixnumshift=0, value is raw
  (macptr-ptr imm2 ptr)
  @again
  (ldaxr imm1 (:@ imm2))
  (stlxr imm0 imm3 (:@ imm2))
  (cbnz imm0 @again)
  (box-fixnum arg_z imm1)
  (ret))

(defarm64lapfunction %atomic-pop-static-cons ()
  (load-global-address imm0 arm64::static-conses)
  (load-global-address imm2 arm64::free-static-conses)
  @again
  (ldxr arg_z (:@ imm0))
  (cmp arg_z rnil)
  (b.ne @pop)
  (clrex)
  (ret)
  @pop
  (%cdr temp0 arg_z)
  (stxr imm1 temp0 (:@ imm0))
  (cbnz imm1 @again)
  @dec
  (ldxr imm3 (:@ imm2))
  (sub imm3 imm3 (:$ 1))
  (stxr imm1 imm3 (:@ imm2))
  (cbnz imm1 @dec)
  (ret))


; end of arm64-misc.lisp
