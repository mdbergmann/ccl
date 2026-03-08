;;-*- Mode: Lisp; Package: CCL -*-
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

;;; ARM64 bignum primitives.
;;; Bignums use 32-bit digits.  On ARM64 (fixnumshift=0), 32-bit digit
;;; values fit directly in fixnums.  This file matches the x86-64 interface
;;; (not the ARM32 digit-pair interface), as called by l0-bignum64.lisp.

(in-package "CCL")

(eval-when (:compile-toplevel :execute)
  (require "ARM64-ARCH")
  (require "ARM64-LAPMACROS"))

;;; The caller has allocated a two-digit bignum (quite likely on the stack).
;;; If we can fit in a single digit (if the high word is just a sign
;;; extension of the low word), truncate the bignum in place (the
;;; trailing words should already be zeroed).
(defarm64lapfunction %fixnum-to-bignum-set ((bignum arg_y) (fixnum arg_z))
  (check-nargs 2)
  ;; fixnumshift=0, so fixnum IS the raw value.
  ;; Sign-extend low 32 bits to 64 and compare.
  (sxtw imm0 fixnum)
  (cmp imm0 fixnum)
  (b (:? eq) @chop)
  ;; Two-digit: store full 64-bit value (both digits at once)
  (str fixnum (:@ bignum (:$ arm64::misc-data-offset)))
  (ret)
  @chop
  ;; One-digit: set 1-digit header and store 32-bit value
  (lri imm0 arm64::one-digit-bignum-header)
  (stur imm0 (:@ bignum (:$ arm64::misc-header-offset)))
  (str32 fixnum (:@ bignum (:$ arm64::misc-data-offset)))
  (ret))


;;; Core multiply-and-add loop for bignum multiplication.
;;; Multiplies the 64-bit "digit pair" x[i] by each y[j] (also 64-bit pairs),
;;; accumulating into r[i..], propagating carries.
;;; Arguments: xs, ys are bignums; r is result bignum; i is 64-bit pair index;
;;; ylen is count of 64-bit pairs.
;;; All indices are 64-bit pair indices (each pair = 2 × 32-bit digits).
;;;
;;; Register allocation: x-val and carry are raw 64-bit digit pairs that can
;;; have arbitrary top bytes.  They MUST live in imm registers (not GC-scanned)
;;; rather than on vsp (GC-scanned) or in temp registers (GC-scanned).
(defarm64lapfunction %multiply-and-add-loop64
    ((xs 8) (ys 0) (r arg_x) (i arg_y) (ylen arg_z))
  (check-nargs 5)
  (let ((x-val imm3)            ; loaded once, persistent (not GC-scanned)
        (carry imm2)             ; persistent carry digit (not GC-scanned)
        (prod-hi imm1)           ; scratch within loop iteration
        (prod-lo imm0)           ; scratch within loop iteration
        (r-val imm4)             ; scratch for loading r[i] (not GC-scanned)
        (idx-i temp0)            ; byte offset for r (small int = valid fixnum)
        (idx-j temp1)            ; byte offset for ys (small int = valid fixnum)
        (y-ptr temp2))           ; tagged bignum pointer (GC-safe)
    ;; Convert pair index i to byte offset: i * 8
    (lsl idx-i i (:$ 3))
    ;; Load x[i] (64-bit pair) — persists in imm3 across loop
    (ldr y-ptr (:@ vsp (:$ xs)))  ; xs pointer (temporarily in y-ptr)
    (ldr x-val (:@ y-ptr idx-i))  ; x-val = xs[i]
    ;; Load ys pointer (stays in y-ptr for loop duration)
    (ldr y-ptr (:@ vsp (:$ ys)))  ; y-ptr = ys
    ;; Initialize
    (mov idx-j (:$ 0))            ; j byte offset = 0
    (mov carry (:$ 0))            ; carry = 0
    @loop
    ;; Load y[j] into prod-lo (scratch use of imm0)
    (ldr prod-lo (:@ y-ptr idx-j))
    ;; 128-bit multiply: x-val * y[j]
    ;; umulh must precede mul since mul overwrites prod-lo (the y source)
    (umulh prod-hi x-val prod-lo)  ; imm1 = high(x-val * y[j])
    (mul prod-lo x-val prod-lo)    ; imm0 = low(x-val * y[j])
    ;; Add r[i] to product
    (ldr r-val (:@ r idx-i))      ; load r[i]
    (adds prod-lo prod-lo r-val)   ; prod-lo += r[i], set CF
    (adc prod-hi prod-hi zr)       ; prod-hi += CF
    ;; Add old carry digit
    (adds prod-lo prod-lo carry)   ; prod-lo += carry, set CF
    (adc carry prod-hi zr)         ; new carry = prod-hi + CF
    ;; Store result
    (str prod-lo (:@ r idx-i))    ; r[i] = prod-lo
    ;; Advance indices
    (add idx-i idx-i (:$ 8))       ; next 64-bit pair in r
    (add idx-j idx-j (:$ 8))       ; next 64-bit pair in y
    (subs ylen ylen (:$ 1))        ; decrement pair count
    (b (:? hi) @loop)              ; loop while ylen > 0
    ;; Store final carry (idx-i points one past last processed pair)
    (str carry (:@ r idx-i))
    ;; Clean up vsp: pop 2 stack args (xs, ys)
    (add vsp vsp (:$ 16))
    (ret)))


;;; Multiply the (32-bit) digits X and Y, producing a 64-bit result.
;;; Add the 32-bit "prev" digit and the 32-bit carry-in digit to that 64-bit
;;; result; return the halves as (VALUES high low).
(defarm64lapfunction %multiply-and-add4 ((x 0) (y arg_x) (prev arg_y) (carry-in arg_z))
  (check-nargs 4)
  (let ((product imm0)
        (high temp0)
        (low temp1))
    (ldr temp0 (:@ vsp (:$ x)))
    ;; 32×32→64 multiply (both values are ≤ 32 bits, result fits in 64)
    (mul product temp0 y)
    ;; Add prev and carry-in
    (add product product prev)
    (add product product carry-in)
    ;; Split into high and low 32-bit halves
    (and low product (:$ #xffffffff))
    (lsr high product (:$ 32))
    ;; Return (VALUES high low)
    (vpush1 high)
    (vpush1 low)
    (add temp0 vsp (:$ 24))     ; frame pointer: 2 values + 1 stack arg + 8
    (set-nargs 2)
    (spjump .SPvalues)))


;;; Multiply the (32-bit) digits X and Y, producing a 64-bit result.
;;; Add carry-in; return the halves as (VALUES high low).
(defarm64lapfunction %multiply-and-add3 ((x arg_x) (y arg_y) (carry-in arg_z))
  (check-nargs 3)
  (let ((product imm0)
        (high temp0)
        (low temp1))
    ;; 32×32→64 multiply
    (mul product x y)
    ;; Add carry-in
    (add product product carry-in)
    ;; Split into high and low 32-bit halves
    (and low product (:$ #xffffffff))
    (lsr high product (:$ 32))
    ;; Return (VALUES high low)
    (vpush1 high)
    (vpush1 low)
    (add temp0 vsp (:$ 16))
    (set-nargs 2)
    (spjump .SPvalues)))


;;; Multiply bignum X by fixnum Y, storing result in RESULT.
;;; Processes 64-bit pairs (each = 2 × 32-bit digits).
;;; LEN64 is the number of 64-bit pairs in X.
(defarm64lapfunction %multiply-and-add-fixnum-loop ((len64 0) (x arg_x) (y arg_y) (result arg_z))
  (check-nargs 4)
  (let ((carry imm2)
        (idx temp0)
        (rlen temp1))
    (ldr rlen (:@ vsp (:$ len64)))
    ;; Convert rlen from pair count to byte count
    (lsl rlen rlen (:$ 3))
    (mov carry (:$ 0))
    (mov idx (:$ 0))
    (b @test)
    @loop
    ;; Load x[i] (64-bit pair)
    (ldr imm0 (:@ x idx))
    ;; 64×64→128: y * x[i]
    (umulh imm1 y imm0)
    (mul imm0 y imm0)
    ;; Add carry
    (adds imm0 imm0 carry)
    (adc carry imm1 zr)
    ;; Store to result[i]
    (str imm0 (:@ result idx))
    (add idx idx (:$ 8))
    @test
    (cmp idx rlen)
    (b (:? lo) @loop)
    ;; Store final carry
    (str carry (:@ result idx))
    (add vsp vsp (:$ 8))       ; pop len64
    (ret)))


;;; Set the ith 64-bit "digit pair" of BIGNUM to the value from R[0].
(defarm64lapfunction %set-digit ((bignum arg_x) (i arg_y) (r arg_z))
  (check-nargs 3)
  ;; Load 64-bit value from r at misc-data-offset
  (ldr imm0 (:@ r (:$ arm64::misc-data-offset)))
  ;; Store to bignum at byte offset i*8
  (lsl imm1 i (:$ 3))
  (str imm0 (:@ bignum imm1))
  (ret))


;;; Return the (possibly truncated) 32-bit quotient and remainder
;;; resulting from dividing hi:low by divisor.
;;; All args are fixnums (32-bit unsigned values).
(defarm64lapfunction %floor ((num-high arg_x) (num-low arg_y) (divisor arg_z))
  (check-nargs 3)
  (build-lisp-frame)
  ;; Compose 64-bit dividend: (num-high << 32) | num-low
  (orr imm0 num-low (:lsl num-high (:$ 32)))
  ;; 64-bit unsigned divide
  (udiv imm1 imm0 divisor)
  ;; Remainder = dividend - quotient * divisor
  (msub imm2 imm1 divisor imm0)
  ;; Box results (fixnumshift=0, they're already fixnums if ≤ 56 bits)
  ;; quotient in imm1, remainder in imm2
  (and imm1 imm1 (:$ #xffffffff))
  (and imm2 imm2 (:$ #xffffffff))
  (vpush1 imm1)
  (vpush1 imm2)
  (set-nargs 2)
  (spjump .SPnvalret))


;;; Multiply two (UNSIGNED-BYTE 32) arguments, return the high and
;;; low halves of the 64-bit result.
(defarm64lapfunction %multiply ((x arg_y) (y arg_z))
  (check-nargs 2)
  (build-lisp-frame)
  ;; 32×32→64: since both are ≤ 32 bits, mul gives full 64-bit result
  (mul imm0 x y)
  ;; Split
  (lsr imm1 imm0 (:$ 32))       ; high
  (and imm0 imm0 (:$ #xffffffff)) ; low
  (vpush1 imm1)
  (vpush1 imm0)
  (set-nargs 2)
  (spjump .SPnvalret))


;;; Any words in the "tail" of the bignum should have been
;;; zeroed by the caller.
(defarm64lapfunction %set-bignum-length ((newlen arg_y) (bignum arg_z))
  (check-nargs 2)
  ;; Header = (subtag-bignum << subtag-shift) | newlen
  (mov imm0 newlen)
  (movk imm0 (:$ (:apply ash arm64::subtag-bignum 8)) (:lsl 48))
  (stur imm0 (:@ bignum (:$ arm64::misc-header-offset)))
  (ret))


;;; Count the sign bits in the most significant digit of bignum;
;;; return fixnum count.
(defarm64lapfunction %bignum-sign-bits ((bignum arg_z))
  (check-nargs 1)
  ;; Get bignum length (number of 32-bit digits)
  (vector-length imm0 bignum imm1)
  ;; Compute byte offset of last 32-bit digit: (len-1)*4
  (sub imm0 imm0 (:$ 1))
  (lsl imm0 imm0 (:$ 2))
  ;; Load last 32-bit digit
  (ldr32 imm0 (:@ bignum imm0))
  ;; If negative, invert before counting leading zeros
  (sxtw imm1 imm0)              ; sign-extend to 64 bits
  (cmp imm1 (:$ 0))
  (b (:? ge) @positive)
  (mvn imm0 imm0)
  (and imm0 imm0 (:$ #xffffffff))
  @positive
  ;; Count leading zeros in 32-bit value
  ;; CLZ on 64-bit register counts from bit 63, so adjust
  (clz imm0 imm0)
  (sub arg_z imm0 (:$ 32))      ; subtract 32 for upper zero bits
  (ret))


;;; Load bignum digit at INDEX, sign-extending from 32 to 64 bits.
(defarm64lapfunction %signed-bignum-ref ((bignum arg_y) (index arg_z))
  (check-nargs 2)
  ;; Byte offset = index * 4
  (lsl imm0 index (:$ 2))
  ;; Sign-extending 32-bit load (LDRSW)
  (ldrsw imm0 (:@ bignum imm0))
  (mov arg_z imm0)
  (ret))


;;; If the bignum is a one-digit bignum, return the value of the
;;; single digit as a fixnum.  Otherwise, if it's a two-digit bignum
;;; and the two 32-bit words can be represented in a fixnum,
;;; return that fixnum; else return nil.
(defarm64lapfunction %maybe-fixnum-from-one-or-two-digit-bignum ((bignum arg_z))
  (check-nargs 1)
  (getvheader imm1 bignum)
  ;; Check for one-digit bignum
  (lri imm0 arm64::one-digit-bignum-header)
  (cmp imm1 imm0)
  (b (:? eq) @one)
  ;; Check for two-digit bignum
  (lri imm0 arm64::two-digit-bignum-header)
  (cmp imm1 imm0)
  (b (:? ne) @no)
  ;; Two-digit: load both digits as 64-bit value
  (ldr imm0 (:@ bignum (:$ arm64::misc-data-offset)))
  ;; Check if it fits in a fixnum (56-bit signed range).
  ;; box-fixnum is identity, so check: does value survive box+unbox?
  ;; On ARM64 TBI: fixnum tag is in top byte.  A value is a valid fixnum
  ;; if it's in [-2^55, 2^55-1].  Check by sign-extending from bit 55.
  (lsl imm1 imm0 (:$ 8))
  (asr imm1 imm1 (:$ 8))
  (cmp imm0 imm1)
  (b (:? eq) @done)
  @no
  (mov arg_z rnil)
  (ret)
  @one
  ;; One-digit: sign-extend 32-bit value to 64 bits
  (ldrsw imm0 (:@ bignum (:$ arm64::misc-data-offset)))
  @done
  (mov arg_z imm0)
  (ret))


;;; Logical shift right of a 32-bit digit value.
(defarm64lapfunction %digit-logical-shift-right ((digit arg_y) (count arg_z))
  (check-nargs 2)
  ;; Mask digit to 32 bits, then shift right
  (and imm0 digit (:$ #xffffffff))
  (lsr arg_z imm0 count)
  (ret))


;;; Arithmetic shift right of a 32-bit digit value (sign-extending).
(defarm64lapfunction %ashr ((digit arg_y) (count arg_z))
  (check-nargs 2)
  ;; Sign-extend 32-bit value to 64, then arithmetic shift right
  (sxtw imm0 digit)
  (asr arg_z imm0 count)
  (ret))


;;; Shift left, result masked to 32 bits.
(defarm64lapfunction %ashl ((digit arg_y) (count arg_z))
  (check-nargs 2)
  (lsl imm0 digit count)
  (and arg_z imm0 (:$ #xffffffff))
  (ret))


;;; Extract macptr address as a fixnum.
(defarm64lapfunction macptr->fixnum ((ptr arg_z))
  (check-nargs 1)
  (macptr-ptr arg_z ptr)
  (ret))


;;; Logical AND of fixnum with bignum digit 0, storing to dest (or returning).
(defarm64lapfunction fix-digit-logand ((fix arg_x) (big arg_y) (dest arg_z))
  (check-nargs 3)
  ;; Load bignum digit 0 (32-bit, zero-extended)
  (ldr32 imm0 (:@ big (:$ arm64::misc-data-offset)))
  (and imm0 fix imm0)
  (cmp dest rnil)
  (b (:? ne) @store)
  (mov arg_z imm0)
  (ret)
  @store
  (str32 imm0 (:@ dest (:$ arm64::misc-data-offset)))
  (ret))


;;; LOGANDC2: fix AND NOT bignum[0]
(defarm64lapfunction fix-digit-logandc2 ((fix arg_x) (big arg_y) (dest arg_z))
  (check-nargs 3)
  (ldr32 imm0 (:@ big (:$ arm64::misc-data-offset)))
  (bic imm0 fix imm0)
  (cmp dest rnil)
  (b (:? ne) @store)
  (mov arg_z imm0)
  (ret)
  @store
  (str32 imm0 (:@ dest (:$ arm64::misc-data-offset)))
  (ret))


;;; LOGANDC1: NOT fix AND bignum[0]
(defarm64lapfunction fix-digit-logandc1 ((fix arg_x) (big arg_y) (dest arg_z))
  (check-nargs 3)
  (ldr32 imm0 (:@ big (:$ arm64::misc-data-offset)))
  (bic imm0 imm0 fix)
  (cmp dest rnil)
  (b (:? ne) @store)
  (mov arg_z imm0)
  (ret)
  @store
  (str32 imm0 (:@ dest (:$ arm64::misc-data-offset)))
  (ret))


;;; Do LOGIOR on the N 32-bit words in A and B, storing the result in C.
;;; Process 64 bits (2 digits) at a time for efficiency.
(defarm64lapfunction %bignum-logior ((n 0) (a arg_x) (b arg_y) (c arg_z))
  (check-nargs 4)
  (ldr temp0 (:@ vsp (:$ n)))
  ;; Convert N (count of 32-bit words) to byte count
  (lsl temp0 temp0 (:$ 2))
  ;; Process 64-bit chunks (8 bytes at a time)
  ;; If odd number of 32-bit words, do the last one as 32-bit first
  (tst temp0 (:$ 4))
  (b (:? eq) @test64)
  (sub temp0 temp0 (:$ 4))
  (ldr32 imm0 (:@ a temp0))
  (ldr32 imm1 (:@ b temp0))
  (orr imm0 imm0 imm1)
  (str32 imm0 (:@ c temp0))
  @test64
  (subs temp0 temp0 (:$ 8))
  (b (:? lo) @done)
  @loop64
  (ldr imm0 (:@ a temp0))
  (ldr imm1 (:@ b temp0))
  (orr imm0 imm0 imm1)
  (str imm0 (:@ c temp0))
  (subs temp0 temp0 (:$ 8))
  (b (:? hs) @loop64)
  @done
  (add vsp vsp (:$ 8))         ; pop n
  (ret))


;;; Do LOGAND on the N 32-bit words in A and B, storing the result in C.
;;; Process 64 bits at a time.
(defarm64lapfunction %bignum-logand ((n 0) (a arg_x) (b arg_y) (c arg_z))
  (check-nargs 4)
  (ldr temp0 (:@ vsp (:$ n)))
  ;; Convert N to byte count
  (lsl temp0 temp0 (:$ 2))
  ;; Handle odd 32-bit word
  (tst temp0 (:$ 4))
  (b (:? eq) @test64)
  (sub temp0 temp0 (:$ 4))
  (ldr32 imm0 (:@ a temp0))
  (ldr32 imm1 (:@ b temp0))
  (and imm0 imm0 imm1)
  (str32 imm0 (:@ c temp0))
  @test64
  (subs temp0 temp0 (:$ 8))
  (b (:? lo) @done)
  @loop64
  (ldr imm0 (:@ a temp0))
  (ldr imm1 (:@ b temp0))
  (and imm0 imm0 imm1)
  (str imm0 (:@ c temp0))
  (subs temp0 temp0 (:$ 8))
  (b (:? hs) @loop64)
  @done
  (add vsp vsp (:$ 8))
  (ret))


;;; Test if the first 32-bit digit of bignum is odd.
(defarm64lapfunction %bignum-oddp ((bignum arg_z))
  (check-nargs 1)
  (ldr32 imm0 (:@ bignum (:$ arm64::misc-data-offset)))
  (tst imm0 (:$ 1))
  (mov arg_z rnil)
  (b (:? eq) @done)
  (add arg_z rnil (:$ arm64::t-offset))
  @done
  (ret))


;; End of arm64-bignum.lisp
