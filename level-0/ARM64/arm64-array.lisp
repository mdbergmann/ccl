;;;-*- Mode: Lisp; Package: CCL -*-
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

(eval-when (:compile-toplevel :execute)
  (require "ARM64-ARCH")
  (require "ARM64-LAPMACROS"))


;;; Users of this shouldn't make assumptions about return value.

;;; %init-misc: Initialize all elements of a freshly allocated misc object.
;;;
;;; ARM64 adaptation notes:
;;; - All fills use 64-bit STR instructions for efficiency.
;;;   For sub-64-bit elements, values are replicated to fill a 64-bit word
;;;   and the element count is adjusted to a 64-bit word count (rounded up).
;;;   This is safe because all allocations are dnode-aligned (16 bytes).
;;; - fixnumshift=0: box/unbox fixnum is identity.
;;; - single-float is immediate (tag byte in bits 56-63, IEEE value in bits 0-31).
;;; - No 32-bit LDR/STR in LAP; use 64-bit load + masking for 32-bit values.

(defarm64lapfunction %init-misc ((val arg_y)
                                 (miscobj arg_z))
  (getvheader imm0 miscobj)
  (header-size temp1 imm0)                  ; element count
  (cbz temp1 @done)                         ; zero elements → return
  (and imm2 imm0 (:$ #xFF))                ; extract subtag
  ;; Check for gvector (node-header): bit 5 set in subtag type bits
  (tst imm2 (:$ arm64::gvector-tag-mask))
  (b.ne @node-fill)
  ;; Ivector: dispatch by element-size group
  (build-lisp-frame)
  (cmp imm2 (:$ arm64::max-32-bit-ivector-subtag))
  (b.ls @32-bit-group)
  (cmp imm2 (:$ arm64::max-64-bit-ivector-subtag))
  (b.ls @64-bit-group)
  (cmp imm2 (:$ arm64::max-8-bit-ivector-subtag))
  (b.ls @8-bit-group)
  (cmp imm2 (:$ arm64::max-16-bit-ivector-subtag))
  (b.ls @16-bit-group)
  (cmp imm2 (:$ arm64::subtag-complex-double-float-vector))
  (b.eq @complex-double-float-vector)
  (cmp imm2 (:$ arm64::subtag-bit-vector))
  (b.eq @bit-vector)
  (b @bad)

  @node-fill
  ;; Fill gvector: store val at each node-sized slot
  (mov imm1 (:$ arm64::misc-data-offset))  ; = 0
  @node-loop
  (str val (:@ miscobj imm1))
  (add imm1 imm1 (:$ arm64::node-size))
  (subs temp1 temp1 (:$ 1))
  (b.ne @node-loop)
  @done
  (ret)

  ;; ================================================================
  ;; 32-bit element group
  ;; ================================================================
  @32-bit-group
  ;; Determine specific type within 32-bit group for value validation
  (cmp imm2 (:$ arm64::subtag-single-float-vector))
  (b.eq @single-float-vector)
  (cmp imm2 (:$ arm64::subtag-simple-base-string))
  (b.eq @string)
  (cmp imm2 (:$ arm64::subtag-s32-vector))
  (b.eq @s32)
  (cmp imm2 (:$ arm64::subtag-fixnum-vector))
  (b.eq @fixnum)
  ;; All others (bignum, double-float, complex-single-float,
  ;; complex-double-float, xcode-vector, u32-vector): treat as u32
  (b @u32)

  @u32
  ;; Value must be non-negative fixnum fitting in 32 bits,
  ;; or a 1-2 digit bignum.
  (test-fixnum val)
  (b.ne @u32-check-bignum)
  ;; It's a fixnum. Check non-negative and fits in 32 bits.
  (cmp val (:$ 0))
  (b.lt @bad)
  (lsr imm0 val (:$ 32))
  (cbnz imm0 @bad)
  (mov imm0 val)
  (b @32-bit-fill)
  @u32-check-bignum
  (extract-subtag imm1 val)
  (cmp imm1 (:$ arm64::subtag-bignum))
  (b.ne @bad)
  (getvheader imm0 val)
  (header-size imm0 imm0)
  (cmp imm0 (:$ 1))
  (b.ne @u32-two-digit)
  ;; 1-digit bignum: load 64 bits, zero-extend low 32
  (ldr imm0 (:@ val (:$ arm64::misc-data-offset)))
  (lsl imm0 imm0 (:$ 32))
  (lsr imm0 imm0 (:$ 32))
  (cmp imm0 (:$ 0))
  (b.lt @bad)                               ; bit 31 set → negative → invalid for u32
  (b @32-bit-fill)
  @u32-two-digit
  (cmp imm0 (:$ 2))
  (b.ne @bad)
  ;; 2-digit bignum: load 64 bits, check high 32 = 0
  (ldr imm0 (:@ val (:$ arm64::misc-data-offset)))
  (lsr imm1 imm0 (:$ 32))
  (cbnz imm1 @bad)
  ;; Low 32 bits are the value
  (lsl imm0 imm0 (:$ 32))
  (lsr imm0 imm0 (:$ 32))
  (b @32-bit-fill)

  @s32
  ;; Value must be fixnum fitting in signed 32 bits, or 1-digit bignum.
  (test-fixnum val)
  (b.ne @s32-check-bignum)
  ;; Check val fits in signed 32-bit: sign-extend from bit 31 and compare
  (sxtw imm0 val)
  (cmp imm0 val)
  (b.ne @bad)
  (mov imm0 val)
  (b @32-bit-fill)
  @s32-check-bignum
  (extract-subtag imm1 val)
  (cmp imm1 (:$ arm64::subtag-bignum))
  (b.ne @bad)
  (getvheader imm0 val)
  (header-size imm0 imm0)
  (cmp imm0 (:$ 1))
  (b.ne @bad)
  (ldr imm0 (:@ val (:$ arm64::misc-data-offset)))
  (lsl imm0 imm0 (:$ 32))
  (lsr imm0 imm0 (:$ 32))
  (b @32-bit-fill)

  @string
  ;; Value must be a character. Extract charcode.
  ;; ARM64: character has tag byte = tag-character (0x11), charcode in bits 8-15.
  (extract-typecode imm0 val)
  (cmp imm0 (:$ arm64::subtag-character))
  (b.ne @bad)
  (lsr imm0 val (:$ arm64::charcode-shift))
  (and imm0 imm0 (:$ #xFF))
  (b @32-bit-fill)

  @fixnum
  ;; Value must be a fixnum. Validate and extract raw value (low 32 bits).
  (test-fixnum val)
  (b.ne @bad)
  ;; ARM64: fixnumshift=0. Check fits in 32 bits (unsigned for fixnum-vector fill).
  (mov imm0 val)
  (b @32-bit-fill)

  @single-float-vector
  ;; Value must be a single-float (immediate: tag=0x10, IEEE bits in 0-31).
  (extract-typecode imm0 val)
  (cmp imm0 (:$ arm64::subtag-single-float))
  (b.ne @bad)
  ;; Extract raw 32-bit IEEE value from the immediate single-float
  (lsl imm0 val (:$ 32))
  (lsr imm0 imm0 (:$ 32))
  (b @32-bit-fill)

  @32-bit-fill
  ;; imm0 has the 32-bit value to fill with (in low 32 bits).
  ;; Replicate to both halves of 64-bit register for 64-bit stores.
  (orr imm0 imm0 (:lsl imm0 (:$ 32)))
  ;; Compute 64-bit word count: ceil(element_count / 2) = (count + 1) >> 1
  (add temp1 temp1 (:$ 1))
  (lsr temp1 temp1 (:$ 1))
  (mov imm1 (:$ arm64::misc-data-offset))  ; = 0
  @32-bit-loop
  (str imm0 (:@ miscobj imm1))
  (add imm1 imm1 (:$ 8))
  (subs temp1 temp1 (:$ 1))
  (b.ne @32-bit-loop)
  (return-lisp-frame)

  ;; ================================================================
  ;; 64-bit element group
  ;; ================================================================
  @64-bit-group
  ;; Subtypes: macptr, dead-macptr, s64, u64, fixnum-vector,
  ;; double-float-vector, complex-single-float-vector.
  (cmp imm2 (:$ arm64::subtag-double-float-vector))
  (b.eq @double-float-vector)
  (cmp imm2 (:$ arm64::subtag-complex-single-float-vector))
  (b.eq @complex-single-float-vector-fill)
  (cmp imm2 (:$ arm64::subtag-fixnum-vector))
  (b.eq @fixnum-vector)
  ;; Default: treat as raw 64-bit fill (macptr, s64, u64, dead-macptr)
  ;; Value should be a fixnum (identity) or bignum.
  (test-fixnum val)
  (b.ne @64-raw-bignum)
  (mov imm0 val)
  (b @64-bit-fill)
  @64-raw-bignum
  (extract-subtag imm1 val)
  (cmp imm1 (:$ arm64::subtag-bignum))
  (b.ne @bad)
  ;; Load 64-bit value from bignum data
  (ldr imm0 (:@ val (:$ arm64::misc-data-offset)))
  (b @64-bit-fill)

  @fixnum-vector
  ;; fixnumshift=0: fixnum IS the raw value
  (test-fixnum val)
  (b.ne @bad)
  (mov imm0 val)
  (b @64-bit-fill)

  @double-float-vector
  ;; Value must be a double-float object
  (extract-typecode imm0 val)
  (cmp imm0 (:$ arm64::subtag-double-float))
  (b.ne @bad)
  ;; Load 64-bit IEEE value
  (ldr imm0 (:@ val (:$ arm64::double-float.value)))
  (b @64-bit-fill)

  @complex-single-float-vector-fill
  ;; Value must be a complex-single-float
  (extract-typecode imm0 val)
  (cmp imm0 (:$ arm64::subtag-complex-single-float))
  (b.ne @bad)
  ;; Load 64-bit packed value (two 32-bit floats)
  (ldr imm0 (:@ val (:$ arm64::complex-single-float.realpart)))
  ;; Fall through to 64-bit fill

  @64-bit-fill
  ;; imm0 has the 64-bit value, temp1 has element count = word count
  (mov imm1 (:$ arm64::misc-data-offset))
  @64-bit-loop
  (str imm0 (:@ miscobj imm1))
  (add imm1 imm1 (:$ 8))
  (subs temp1 temp1 (:$ 1))
  (b.ne @64-bit-loop)
  (return-lisp-frame)

  ;; ================================================================
  ;; 8-bit element group
  ;; ================================================================
  @8-bit-group
  ;; u8 or s8. Extract byte value and replicate.
  (cmp imm2 (:$ arm64::subtag-s8-vector))
  (b.eq @s8)
  ;; u8
  (test-fixnum val)
  (b.ne @bad)
  ;; Check val in [0, 255]
  (cmp val (:$ 256))
  (b.hs @bad)
  (mov imm0 val)
  (b @set8)
  @s8
  (test-fixnum val)
  (b.ne @bad)
  ;; Check val in [-128, 127]: sign-extend from 8 bits and compare
  (sxtb imm0 val)
  (cmp imm0 val)
  (b.ne @bad)
  (and imm0 val (:$ #xFF))
  @set8
  ;; Replicate byte to all 8 positions in a 64-bit word
  (orr imm0 imm0 (:lsl imm0 (:$ 8)))
  (orr imm0 imm0 (:lsl imm0 (:$ 16)))
  (orr imm0 imm0 (:lsl imm0 (:$ 32)))
  ;; word count = ceil(count / 8) = (count + 7) >> 3
  (add temp1 temp1 (:$ 7))
  (lsr temp1 temp1 (:$ 3))
  (mov imm1 (:$ arm64::misc-data-offset))
  @8-bit-loop
  (str imm0 (:@ miscobj imm1))
  (add imm1 imm1 (:$ 8))
  (subs temp1 temp1 (:$ 1))
  (b.ne @8-bit-loop)
  (return-lisp-frame)

  ;; ================================================================
  ;; 16-bit element group
  ;; ================================================================
  @16-bit-group
  (cmp imm2 (:$ arm64::subtag-s16-vector))
  (b.eq @s16)
  ;; u16: check val in [0, 65535]
  (test-fixnum val)
  (b.ne @bad)
  (cmp val (:$ 65536))
  (b.hs @bad)
  (mov imm0 val)
  (b @set16)
  @s16
  (test-fixnum val)
  (b.ne @bad)
  ;; Check val in [-32768, 32767]
  (sxth imm0 val)
  (cmp imm0 val)
  (b.ne @bad)
  (and imm0 val (:$ #xFFFF))
  @set16
  ;; Replicate halfword to all 4 positions
  (orr imm0 imm0 (:lsl imm0 (:$ 16)))
  (orr imm0 imm0 (:lsl imm0 (:$ 32)))
  ;; word count = ceil(count / 4) = (count + 3) >> 2
  (add temp1 temp1 (:$ 3))
  (lsr temp1 temp1 (:$ 2))
  (mov imm1 (:$ arm64::misc-data-offset))
  @16-bit-loop
  (str imm0 (:@ miscobj imm1))
  (add imm1 imm1 (:$ 8))
  (subs temp1 temp1 (:$ 1))
  (b.ne @16-bit-loop)
  (return-lisp-frame)

  ;; ================================================================
  ;; Complex-double-float-vector: 128-bit elements
  ;; ================================================================
  @complex-double-float-vector
  (extract-typecode imm0 val)
  (cmp imm0 (:$ arm64::subtag-complex-double-float))
  (b.ne @bad)
  ;; Load two 64-bit values (realpart and imagpart)
  (ldr imm0 (:@ val (:$ arm64::complex-double-float.realpart)))
  (ldr imm1 (:@ val (:$ arm64::complex-double-float.imagpart)))
  ;; Each element is 16 bytes.
  ;; Data starts at misc-complex-dfloat-offset (= 8) due to alignment pad.
  (mov imm2 (:$ arm64::misc-complex-dfloat-offset))
  @cdf-loop
  (subs temp1 temp1 (:$ 1))
  (b.mi @cdf-done)
  (str imm0 (:@ miscobj imm2))
  (add imm2 imm2 (:$ 8))
  (str imm1 (:@ miscobj imm2))
  (add imm2 imm2 (:$ 8))
  (b @cdf-loop)
  @cdf-done
  (return-lisp-frame)

  ;; ================================================================
  ;; Bit-vector
  ;; ================================================================
  @bit-vector
  (cmp val (:$ 1))
  (b.hi @bad)
  (cmp val (:$ 1))
  (b.ne @bv-zero)
  (mov imm0 (:$ -1))                       ; all 1s
  (b @bv-fill)
  @bv-zero
  (mov imm0 (:$ 0))
  @bv-fill
  ;; word count = ceil(bits / 64) = (bits + 63) >> 6
  (add temp1 temp1 (:$ 63))
  (lsr temp1 temp1 (:$ 6))
  (mov imm1 (:$ arm64::misc-data-offset))
  @bv-loop
  (str imm0 (:@ miscobj imm1))
  (add imm1 imm1 (:$ 8))
  (subs temp1 temp1 (:$ 1))
  (b.ne @bv-loop)
  (return-lisp-frame)

  @bad
  (mov arg_x '#.$xnotelt)
  (set-nargs 3)
  (spcall .SPksignalerr))



;;; argument is a vector header or an array header.  Or else.
(defarm64lapfunction %array-header-data-and-offset ((a arg_z))
  (let ((offset arg_y)
        (disp arg_x)
        (temp temp0))
    (mov offset (:$ 0))
    (mov temp a)
    @loop
    (ldr a (:@ temp (:$ target::arrayH.data-vector)))
    (extract-subtag imm0 a)
    (cmp imm0 (:$ target::subtag-vectorH))
    (b.eq @follow)
    (cmp imm0 (:$ target::subtag-arrayH))
    (b.ne @found)
    @follow
    (ldr disp (:@ temp (:$ target::arrayH.displacement)))
    (mov temp a)
    (add offset offset disp)
    (b @loop)
    @found
    (ldr disp (:@ temp (:$ target::arrayH.displacement)))
    (add offset offset disp)
    (mov temp0 vsp)
    (vpush1 a)
    (vpush1 offset)
    (set-nargs 2)
    (spjump .SPvalues)))


;;; Boole functions for simple-bit-vectors.
;;; On ARM64, these operate on 64-bit words (8 bytes per iteration).
;;; The len argument is the number of 64-bit words to process.

(defarm64lapfunction %boole-clr ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (mov imm0 (:$ 0))
  (b @test)
  @loop
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-set ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (mov imm0 (:$ -1))
  (b @test)
  @loop
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-1 ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-2 ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b1 imm2))
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-c1 ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (mvn imm0 imm0)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-c2 ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b1 imm2))
  (mvn imm0 imm0)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-and ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (and imm0 imm0 imm1)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-ior ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (orr imm0 imm0 imm1)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-xor ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (eor imm0 imm0 imm1)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-eqv ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (eon imm0 imm0 imm1)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-nand ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (and imm0 imm0 imm1)
  (mvn imm0 imm0)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-nor ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (orr imm0 imm0 imm1)
  (mvn imm0 imm0)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-andc1 ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (bic imm0 imm1 imm0)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-andc2 ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (bic imm0 imm0 imm1)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-orc1 ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (orn imm0 imm1 imm0)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defarm64lapfunction %boole-orc2 ((len 0) (b0 arg_x) (b1 arg_y) (dest arg_z))
  (vpop1 temp0)
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @test)
  @loop
  (ldr imm0 (:@ b0 imm2))
  (ldr imm1 (:@ b1 imm2))
  (orn imm0 imm0 imm1)
  (str imm0 (:@ dest imm2))
  (add imm2 imm2 (:$ 8))
  @test
  (subs temp0 temp0 (:$ 1))
  (b.pl @loop)
  (ret))

(defparameter *simple-bit-boole-functions* ())

(setq *simple-bit-boole-functions*
      (vector
       #'%boole-clr
       #'%boole-set
       #'%boole-1
       #'%boole-2
       #'%boole-c1
       #'%boole-c2
       #'%boole-and
       #'%boole-ior
       #'%boole-xor
       #'%boole-eqv
       #'%boole-nand
       #'%boole-nor
       #'%boole-andc1
       #'%boole-andc2
       #'%boole-orc1
       #'%boole-orc2))

(defun %simple-bit-boole (op b1 b2 result)
  ;; ARM64: 64-bit words, so divide by 64 (6 bits) instead of 32 (5 bits)
  (funcall (svref *simple-bit-boole-functions* op)
           (ash (the fixnum (+ (length result) 63)) -6)
           b1
           b2
           result))


(defarm64lapfunction %aref2 ((array arg_x) (i arg_y) (j arg_z))
  (check-nargs 3)
  (spjump .SParef2))

(defarm64lapfunction %aref3 ((array 0) (i arg_x) (j arg_y) (k arg_z))
  (check-nargs 4)
  (vpop1 temp0)
  (spjump .SParef3))


(defarm64lapfunction %aset2 ((array 0) (i arg_x) (j arg_y) (newval arg_z))
  (check-nargs 4)
  (vpop1 temp0)
  (spjump .SPaset2))

(defarm64lapfunction %aset3 ((array #.target::node-size) (i 0) (j arg_x) (k arg_y) (newval arg_z))
  (check-nargs 5)
  (vpop1 temp0)
  (vpop1 temp1)
  (spjump .SPaset3))


;;; If argument is an ivector typecode, return it else return 0.

