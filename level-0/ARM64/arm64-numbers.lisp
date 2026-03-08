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

(in-package "CCL")

;;; ARM64 fixnumshift=0: box-fixnum and unbox-fixnum are identity (mov).
;;; Single-float is immediate (tag 0x10 in bits 56-63, IEEE value in bits 0-31).

(defarm64lapfunction %fixnum-signum ((number arg_z))
  (cmp number (:$ 0))
  (b.eq @done)
  (mov arg_z (:$ 1))
  (b.gt @done)
  (mov arg_z (:$ -1))
  @done
  (ret))

(defarm64lapfunction %ilogcount ((number arg_z))
  ;; Kernighan bit-counting: count 1-bits by repeatedly clearing lowest set bit
  (let ((shift imm0)
        (temp imm1))
    (mov shift number)                  ; unbox-fixnum is identity
    (mov arg_z (:$ 0))
    (b @test)
    @next
    (sub temp shift (:$ 1))
    (and shift shift temp)
    (add arg_z arg_z (:$ 1))
    @test
    (cbnz shift @next)
    (ret)))

(defarm64lapfunction %iash ((number arg_y) (count arg_z))
  ;; Arithmetic shift: positive count = left, negative = right
  (mov imm1 count)                      ; unbox-fixnum is identity
  (cmp imm1 (:$ 0))
  (b.gt @left)
  (neg imm1 imm1)                       ; negate for right shift amount
  (asr arg_z number imm1)               ; arithmetic right shift
  (ret)
  @left
  (lsl arg_z number imm1)               ; left shift
  (ret))

(defparameter *double-float-zero* 0.0d0)
(defparameter *short-float-zero* 0.0s0)

(defarm64lapfunction %sfloat-hwords ((sfloat arg_z))
  ;; ARM64: single-float is immediate, IEEE value in bits 0-31
  (and imm0 sfloat (:$ #xffffffff))     ; extract 32-bit float value
  (digit-h temp0 imm0)                  ; high 16 bits (bits 16-31)
  (digit-l temp1 imm0)                  ; low 16 bits (bits 0-15)
  (vpush1 temp0)
  (vpush1 temp1)
  (add temp0 vsp (:$ 16))               ; 2 args * node-size
  (set-nargs 2)
  (spjump .SPvalues))

;;; integer-length for fixnum
;;; = (- 64 (clz (if (>= n 0) n (lognot n))))
(defarm64lapfunction %fixnum-intlen ((number arg_z))
  (mov imm0 number)                     ; unbox-fixnum is identity
  (cmp imm0 (:$ 0))
  (b.ge @nonneg)
  (mvn imm0 imm0)                       ; complement for negative
  @nonneg
  (clz imm1 imm0)
  (mov imm0 (:$ 64))
  (sub arg_z imm0 imm1)                 ; integer-length = 64 - clz
  (ret))


;;; Caller guarantees that result fits in a fixnum.
(defarm64lapfunction %truncate-double-float->fixnum ((arg arg_z))
  (get-double-float d0 arg)
  (fcvtzs arg_z d0)                     ; convert to signed integer, truncate
  (ret))

(defarm64lapfunction %truncate-short-float->fixnum ((arg arg_z))
  (get-single-float s0 arg)             ; fmov s0, arg (bits 0-31)
  (fcvtzs arg_z s0)                     ; convert to signed integer, truncate
  (ret))

;;; Round to nearest (ties to even)
(defarm64lapfunction %round-nearest-double-float->fixnum ((arg arg_z))
  (get-double-float d0 arg)
  (fcvtns arg_z d0)                     ; convert to signed, round nearest
  (ret))

(defarm64lapfunction %round-nearest-short-float->fixnum ((arg arg_z))
  (get-single-float s0 arg)
  (fcvtns arg_z s0)                     ; convert to signed, round nearest
  (ret))



;;; Fixnum division returning quotient and remainder as multiple values.
;;; ticket:666 describes one reason to handle -1 specially.
(defarm64lapfunction %fixnum-truncate ((dividend arg_y) (divisor arg_z))
  (let ((unboxed-quotient imm0)
        (unboxed-remainder imm1)
        (quotient arg_y)
        (remainder arg_z))
    (build-lisp-frame)
    (cmp divisor (:$ -1))
    (b.eq @neg)
    ;; Normal division: ARM64 has native sdiv
    (sdiv unboxed-quotient dividend divisor)
    (msub unboxed-remainder unboxed-quotient divisor dividend)
    (vpush1 unboxed-quotient)
    (vpush1 unboxed-remainder)
    (set-nargs 2)
    (spjump .SPnvalret)
    @neg
    ;; Division by -1: negate dividend.
    ;; Overflow if result doesn't fit in fixnum (most-negative-fixnum / -1).
    (neg imm0 dividend)
    ;; Validate: sign-extend from bit 55 and compare to original
    (lsl imm1 imm0 (:$ 8))
    (asr imm1 imm1 (:$ 8))
    (cmp imm1 imm0)
    (b.eq @neg-ok)
    ;; Overflow: result is a bignum
    (ldr temp0 (:@ nfn '*least-positive-bignum*))
    (ldr imm0 (:@ temp0 (:$ arm64::symbol.vcell)))
    (mov imm1 (:$ 0))
    (vpush1 imm0)
    (vpush1 imm1)
    (set-nargs 2)
    (spjump .SPnvalret)
    @neg-ok
    (mov imm1 (:$ 0))                    ; remainder = 0
    (vpush1 imm0)
    (vpush1 imm1)
    (set-nargs 2)
    (spjump .SPnvalret)))


;;; Check if called for multiple values by comparing saved LR to ret1valaddr.
(defarm64lapfunction called-for-mv-p ()
  (ldr imm0 (:@ sp (:$ arm64::lisp-frame.savelr)))
  (ref-global imm1 ret1valaddr)
  (cmp imm0 imm1)
  (mov arg_z rnil)
  (b.ne @done)
  (add arg_z arg_z (:$ arm64::t-offset))
  @done
  (ret))

;;; n1 and n2 must be positive (and non-zero)
;;; Binary GCD algorithm
(defarm64lapfunction %fixnum-gcd ((n1 arg_y) (n2 arg_z))
  (mov imm0 n1)                         ; u
  (mov imm1 n2)                         ; v
  ;; Count common trailing zeros = common power-of-2 factor
  (orr imm2 imm0 imm1)
  (rbit imm3 imm2)
  (clz imm3 imm3)                       ; k = ctz(u|v)
  (lsr imm0 imm0 imm3)                  ; u >>= k
  (lsr imm1 imm1 imm3)                  ; v >>= k
  ;; Make u odd
  (rbit imm2 imm0)
  (clz imm2 imm2)
  (lsr imm0 imm0 imm2)                  ; u >>= ctz(u)
  @loop
  ;; Make v odd
  (rbit imm2 imm1)
  (clz imm2 imm2)
  (lsr imm1 imm1 imm2)                  ; v >>= ctz(v)
  ;; Ensure u <= v, compute v = |u - v|
  (subs imm2 imm0 imm1)                 ; u - v
  (b.eq @done)
  (csel imm0 imm0 imm1 ls)             ; u = min(u, v)
  ;; Absolute difference
  (csneg imm1 imm2 imm2 ls)            ; v = |u - v|
  (b @loop)
  @done
  ;; GCD = u << k
  (lsl arg_z imm0 imm3)
  (ret))


;;; %mrg31k3p — Mersenne-twister-like PRNG
;;; NOTE: This function uses u32-ref/u32-set which need 32-bit load/store
;;; support on ARM64. The current u32-ref macro uses 64-bit loads.
;;; For correctness, we mask loaded values to 32 bits and use careful
;;; store patterns. This should be revisited when proper 32-bit LAP
;;; memory access is available.
;;; DEFERRED: This function is not critical for initial boot.
;;; TODO: Implement when 32-bit LAP memory access is available.


;;; Allocate and initialize a complex-double-float.
;;; ARM64 TBI allocation: sub allocptr, cmp allocbase, b.hi, hlt
(defarm64lapfunction %make-complex-double-float ((r arg_y) (i arg_z))
  (build-lisp-frame)
  ;; Load real and imaginary double-float values
  (get-double-float d0 r)               ; d0 = real part
  (get-double-float d1 i)               ; d1 = imaginary part
  ;; Build header: (subtag << 56) | element-count
  (lri imm0 (logior (ash arm64::subtag-complex-double-float
                          arm64::subtag-shift)
                     arm64::complex-double-float.element-count))
  ;; Allocate: complex-double-float.size bytes
  ;; sub allocptr by (size - node-size) since tagged ptr = raw + node-size
  (sub allocptr allocptr (:$ (- arm64::complex-double-float.size arm64::node-size)))
  (ldr temp0 (:@ rcontext (:$ arm64::tcr.save-allocbase)))
  (cmp allocptr temp0)
  (b.hi @no-trap)
  (uuo-alloc-trap)
  @no-trap
  ;; Store header at allocptr - node-size (= misc-header-offset from tagged ptr)
  (stur imm0 (:@ allocptr (:$ (- arm64::node-size))))
  ;; Tagged pointer = allocptr with ivector-ref tag
  (mov arg_z allocptr)
  (movk arg_z (:$ (ash arm64::subtag-complex-double-float 8)) (:lsl 48))
  ;; Clear allocptr tag bits (align to dnode)
  (and allocptr allocptr (:$ (lognot arm64::dnode-mask)))
  ;; Store real and imaginary parts
  ;; complex-double-float layout: [header][pad][realpart][imagpart]
  ;; pad at misc-data-offset (0), realpart at +8, imagpart at +16
  (str d0 (:@ arg_z (:$ arm64::complex-double-float.realpart)))
  (str d1 (:@ arg_z (:$ arm64::complex-double-float.imagpart)))
  (return-lisp-frame))

;;; Allocate and initialize a complex-single-float.
;;; ARM64: single-float is immediate, so r and i are tagged immediates.
;;; complex-single-float packs two 32-bit floats in one 8-byte slot.
(defarm64lapfunction %make-complex-single-float ((r arg_y) (i arg_z))
  (build-lisp-frame)
  ;; Extract 32-bit float values from immediate single-floats
  (and imm1 r (:$ #xffffffff))          ; real part (bits 0-31)
  (and imm2 i (:$ #xffffffff))          ; imaginary part (bits 0-31)
  ;; Pack: real in low 32 bits, imaginary in high 32 bits
  (orr imm1 imm1 (:lsl imm2 (:$ 32)))
  ;; Build header
  (lri imm0 (logior (ash arm64::subtag-complex-single-float
                          arm64::subtag-shift)
                     arm64::complex-single-float.element-count))
  ;; Allocate: complex-single-float.size = 16 bytes (header + data)
  (sub allocptr allocptr (:$ (- arm64::complex-single-float.size arm64::node-size)))
  (ldr temp0 (:@ rcontext (:$ arm64::tcr.save-allocbase)))
  (cmp allocptr temp0)
  (b.hi @no-trap)
  (uuo-alloc-trap)
  @no-trap
  ;; Store header
  (stur imm0 (:@ allocptr (:$ (- arm64::node-size))))
  ;; Tagged pointer
  (mov arg_z allocptr)
  (movk arg_z (:$ (ash arm64::subtag-complex-single-float 8)) (:lsl 48))
  ;; Clear allocptr
  (and allocptr allocptr (:$ (lognot arm64::dnode-mask)))
  ;; Store packed real+imaginary at misc-data-offset (= 0)
  (str imm1 (:@ arg_z (:$ arm64::complex-single-float.realpart)))
  (return-lisp-frame))

; End of arm64-numbers.lisp
