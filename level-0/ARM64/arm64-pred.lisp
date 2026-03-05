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
  (require "ARM64-LAPMACROS"))

(defarm64lapfunction eql ((x arg_y) (y arg_z))
  "Return T if OBJ1 and OBJ2 represent the same object, otherwise NIL."
  (check-nargs 2)
  (spjump .SPbuiltin-eql))


(defarm64lapfunction equal ((x arg_y) (y arg_z))
  "Return T if X and Y are EQL or if they are structured components
  whose elements are EQUAL. Strings and bit-vectors are EQUAL if they
  are the same length and have identical components. Other arrays must be
  EQ to be EQUAL.  Pathnames are EQUAL if their components are."
  (check-nargs 2)
  @top
  (cmp x y)
  (b.eq @win)
  (extract-fulltag imm0 x)
  (extract-fulltag imm1 y)
  (cmp imm0 imm1)
  (b.ne @lose)
  (cmp imm0 (:$ arm64::tag-cons))
  (b.eq @cons)
  ;; Uvector references have the uvector-ref bit (#x40) set in the tag byte.
  ;; Since both tags are the same, if one is uvector, both are.
  (tst imm0 (:$ arm64::uvector-ref))
  (b.ne @misc)
  @lose
  (mov arg_z rnil)
  (ret)
  @win
  (add arg_z rnil (:$ arm64::t-offset))
  (ret)
  @cons
  (%car temp0 x)
  (%car temp1 y)
  (cmp temp0 temp1)
  (b.ne @recurse)
  (%cdr x x)
  (%cdr y y)
  (b @top)
  @recurse
  (vpush1 x)
  (vpush1 y)
  (vpush1 nfn)                          ; save function pointer (no fn reg on ARM64)
  (build-lisp-frame)
  (mov x temp0)
  (mov y temp1)
  (bl @top)
  (cmp arg_z rnil)
  (restore-lisp-frame)
  (vpop1 nfn)                           ; restore function pointer
  (vpop1 y)
  (vpop1 x)
  (b.eq  @lose)
  (%cdr x x)
  (%cdr y y)
  (b @top)
  @misc
  (extract-subtag imm0 x)
  (extract-subtag imm1 y)
  ;; If either is a vector header, let HAIRY-EQUAL deal with them.
  ;; ARM32 used cmpne; ARM64: check each separately.
  (cmp imm0 (:$ arm64::subtag-vectorH))
  (b.eq @hairy)
  (cmp imm1 (:$ arm64::subtag-vectorH))
  (b.eq @hairy)
  ;; If both are istructs (and potentially pathnames), try HAIRY-EQUAL
  (cmp imm0 (:$ arm64::subtag-istruct))
  (b.ne @not-both-istruct)
  (cmp imm1 (:$ arm64::subtag-istruct))
  (b.eq @hairy)
  @not-both-istruct
  (getvheader imm0 x)
  (getvheader imm1 y)
  (cmp imm0 imm1)
  (b.ne @try-eql)
  (and imm2 imm0 (:$ #xff))
  (cmp imm2 (:$ arm64::subtag-bit-vector))
  (b.eq @bit-vector)
  (cmp imm2 (:$ arm64::subtag-simple-base-string))
  (b.ne @try-eql)
  ;; Same-length simple strings.  Compare 64-bit words.
  ;; header-length gives count of 32-bit elements; convert to 64-bit word count.
  (header-length temp0 imm0)
  @compare-words
  ;; temp0 = count of 32-bit words.  Convert to 64-bit word count (ceiling).
  (add temp0 temp0 (:$ 1))
  (lsr temp0 temp0 (:$ 1))
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @string-next)
  @string-loop
  (ldr imm0 (:@ x imm2))
  (ldr imm1 (:@ y imm2))
  (cmp imm0 imm1)
  (b.ne @lose)
  (add imm2 imm2 (:$ 8))
  @string-next
  (subs temp0 temp0 (:$ 1))
  (b.ge @string-loop)
  (add arg_z rnil (:$ arm64::t-offset))
  (ret)
  @try-eql
  (spjump .SPbuiltin-eql)
  @hairy
  (set-nargs 2)
  (ldr fname (:@ nfn 'hairy-equal))
  (ldr nfn (:@ fname (:$ arm64::symbol.fcell)))
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr)
  @bit-vector
  ;; Go through the bitvectors, comparing 64-bit words.
  ;; If the number of bits isn't a multiple of 64, we have to mask
  ;; the last word.
  (header-size imm2 imm1)               ; imm2 = number of bits
  (lsr imm1 imm2 (:$ 6))               ; imm1 = number of complete 64-bit words
  (box-fixnum temp0 imm1)               ; temp0 = word count (fixnum=identity)
  (ands imm2 imm2 (:$ 63))             ; imm2 = remaining bits
  (b.eq @compare-words64)
  ;; Handle partial last word
  (mov imm0 (:$ 1))
  (lsl imm2 imm0 imm2)
  (sub imm2 imm2 (:$ 1))               ; mask for remaining bits
  (lsl imm1 temp0 (:$ 3))              ; byte offset of last word
  (add imm1 imm1 (:$ arm64::misc-data-offset))
  (ldr imm0 (:@ x imm1))
  (ldr imm1 (:@ y imm1))
  (and imm0 imm0 imm2)
  (and imm1 imm1 imm2)
  (cmp imm1 imm0)
  (b.eq @compare-words64)
  (b @lose)
  @compare-words64
  ;; temp0 = count of complete 64-bit words to compare.
  (mov imm2 (:$ arm64::misc-data-offset))
  (b @bv-next)
  @bv-loop
  (ldr imm0 (:@ x imm2))
  (ldr imm1 (:@ y imm2))
  (cmp imm0 imm1)
  (b.ne @lose)
  (add imm2 imm2 (:$ 8))
  @bv-next
  (subs temp0 temp0 (:$ 1))
  (b.ge @bv-loop)
  (add arg_z rnil (:$ arm64::t-offset))
  (ret))

;;; end of arm64-pred.lisp
