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

;;; level-0;ARM64;arm64-hash.lisp


(in-package "CCL")

(eval-when (:compile-toplevel :execute)
  (require "HASHENV" "ccl:xdump;hashenv"))



;;; This should stay in LAP so that it's fast
;;; Equivalent to cl:mod when both args are positive fixnums
;;; ARM64: fixnumshift=0, so number/divisor are raw integers.
;;; Use udiv + msub to compute remainder.
(defarm64lapfunction fast-mod ((number arg_y) (divisor arg_z))
  (udiv imm0 number divisor)
  (msub arg_z imm0 divisor number)
  (ret))


(defarm64lapfunction fast-mod-3 ((number arg_x) (divisor arg_y) (recip arg_z))
  ;; ARM64: fixnumshift=0, so values are raw fixnums.
  ;; Multiply number by reciprocal (high half gives quotient estimate),
  ;; then compute remainder.
  (smulh imm1 number recip)
  (mul imm0 imm1 divisor)
  (sub number number imm0)
  (sub number number divisor)
  (asr imm0 number (:$ (1- arm64::nbits-in-word)))
  (and divisor divisor imm0)
  (add arg_z number divisor)
  (ret))

(defarm64lapfunction %dfloat-hash ((key arg_z))
  ;; Double-float: 64-bit value at offset 0.
  ;; Hash by combining the two 32-bit halves.
  (ldr imm0 (:@ key (:$ arm64::double-float.value)))
  (lsr imm1 imm0 (:$ 32))
  (add imm0 imm1 imm0)
  (box-fixnum arg_z imm0)
  (ret))



(defarm64lapfunction %sfloat-hash ((key arg_z))
  ;; Single-float is immediate on ARM64 (value in low 32 bits).
  ;; Extract the raw float bits as the hash.
  (and imm0 key (:$ #xffffffff))
  (box-fixnum arg_z imm0)
  (ret))



(defarm64lapfunction %macptr-hash ((key arg_z))
  (ldr imm0 (:@ key (:$ arm64::macptr.address)))
  (lsr imm1 imm0 (:$ 24))
  (add imm0 imm0 imm1)
  ;; fixnummask=0 on ARM64, so no need to clear tag bits
  (mov arg_z imm0)
  (ret))

(defarm64lapfunction %bignum-hash ((key arg_z))
  (let ((header imm1)
        (offset imm2)
        (ndigits temp1)
        (immhash imm0))
    (mov immhash (:$ 0))
    (mov offset (:$ arm64::misc-data-offset))
    (getvheader header key)
    (header-length ndigits header)
    ;; ndigits = count of 32-bit digits.  Compute 64-bit word count.
    ;; Use 64-bit loads (ldr = 8 bytes), loop by pairs of digits.
    (add ndigits ndigits (:$ 1))
    (lsr ndigits ndigits (:$ 1))        ; ceil(ndigits/2) 64-bit words
    (let ((next header))
      @loop
      (subs ndigits ndigits (:$ 1))
      (ldr next (:@ key offset))
      (add offset offset (:$ 8))
      (ror immhash immhash (:$ 19))
      (add immhash next immhash)
      (b.ne @loop))
    ;; fixnummask=0, no need to mask
    (mov arg_z immhash)
    (ret)))




(defarm64lapfunction %get-fwdnum ()
  (ref-global arg_z arm64::fwdnum)
  (ret))


(defarm64lapfunction %get-gc-count ()
  (ref-global arg_z arm64::gc-count)
  (ret))


;;; Setting a key in a hash-table vector needs to
;;; ensure that the vector header gets memoized as well
(defarm64lapfunction %set-hash-table-vector-key ((vector arg_x) (index arg_y) (value arg_z))
  (spjump .SPset-hash-key))

(defarm64lapfunction %set-hash-table-vector-key-conditional ((offset 0) (vector arg_x) (old arg_y) (new arg_z))
  (spjump .SPset-hash-key-conditional))

;;; Strip the tag bits to turn x into a fixnum
;;; ARM64 TBI: tags are in the top byte (bits 56-63).
;;; Clear the top byte to get the raw pointer/fixnum value.
(defarm64lapfunction strip-tag-to-fixnum ((x arg_z))
  (lsl arg_z x (:$ 8))
  (lsr arg_z arg_z (:$ 8))
  (ret))

;;; end of arm64-hash.lisp
