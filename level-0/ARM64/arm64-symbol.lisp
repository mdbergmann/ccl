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

;;; This assumes that macros & special-operators
;;; have something that's not FUNCTIONP in their
;;; function-cells.
(defarm64lapfunction %function ((sym arg_z))
  (check-nargs 1)
  (let ((symptr temp0)
        (symbol temp1)
        (def arg_z))
    (cmp sym rnil)
    (mov symbol sym)
    (lri symptr arm64::nil-value)
    (add symptr symptr (:$ arm64::nilsym-offset))
    (b.ne @notnil)
    (b @ref)
    @notnil
    (trap-unless-xtype= sym arm64::subtag-symbol)
    (mov symptr sym)
    @ref
    (ldr def (:@ symptr (:$ arm64::symbol.fcell)))
    (extract-typecode imm0 def)
    (cmp imm0 (:$ arm64::subtag-function))
    (b.eq @ok)
    (uuo-error-udf symbol)
    @ok
    (ret)))



;;; Traps unless sym is NIL or some other symbol.
;;; On ARM64, NIL isn't really a symbol; this function maps from NIL
;;; to an internal proxy symbol ("nilsym").
(defarm64lapfunction %symbol->symptr ((sym arg_z))
  (cmp sym rnil)
  (b.ne @notnilsym)
  (add sym sym (:$ arm64::nilsym-offset))
  (ret)
  @notnilsym
  (trap-unless-xtype= sym arm64::subtag-symbol)
  (ret))

;;; Traps unless symptr is a symbol; returns NIL if symptr
;;; is NILSYM.
(defarm64lapfunction %symptr->symbol ((symptr arg_z))
  (lri imm1 arm64::nil-value)
  (add imm1 imm1 (:$ arm64::nilsym-offset))
  (cmp imm1 symptr)
  (b.ne @notnilsym)
  (mov arg_z rnil)
  (ret)
  @notnilsym
  (trap-unless-xtype= symptr arm64::subtag-symbol)
  (ret))

(defarm64lapfunction %symptr-value ((symptr arg_z))
  (spjump .SPspecref))

(defarm64lapfunction %set-symptr-value ((symptr arg_y) (val arg_z))
  (spjump .SPspecset))

(defarm64lapfunction %symptr-binding-address ((symptr arg_z))
  (ldr imm0 (:@ symptr (:$ arm64::symbol.binding-index)))
  (lsl imm0 imm0 (:$ arm64::word-shift))  ;; binding-index → byte offset
  (ldr imm2 (:@ rcontext (:$ arm64::tcr.tlb-limit)))
  (ldr imm1 (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (cmp imm0 imm2)
  (b.hs @sym)
  (ldr temp0 (:@ imm1 imm0))
  (lri imm2 arm64::no-thread-local-binding-marker)
  (cmp temp0 imm2)
  (b.eq @sym)
  (unbox-fixnum imm0 imm0)
  (vpush1 imm1)
  (vpush1 imm0)
  (set-nargs 2)
  (add temp0 vsp (:$ 16))
  (spjump .SPvalues)
  @sym
  (mov arg_y (:$ arm64::symbol.vcell))
  (vpush1 arg_z)
  (vpush1 arg_y)
  (set-nargs 2)
  (add temp0 vsp (:$ 16))
  (spjump .SPvalues))

(defarm64lapfunction %tcr-binding-location ((tcr arg_y) (sym arg_z))
  (ldr imm1 (:@ sym (:$ arm64::symbol.binding-index)))
  (lsl imm1 imm1 (:$ arm64::word-shift))  ;; binding-index → byte offset
  (ldr imm2 (:@ tcr (:$ arm64::tcr.tlb-limit)))
  (ldr imm0 (:@ tcr (:$ arm64::tcr.tlb-pointer)))
  (mov arg_z rnil)
  (cmp imm1 imm2)
  (b.hs @done)
  (ldr temp0 (:@ imm0 imm1))
  (lri imm2 arm64::no-thread-local-binding-marker)
  (cmp temp0 imm2)
  (b.eq @done)
  (add arg_z imm0 imm1)
  @done
  (ret))


(defarm64lapfunction %pname-hash ((str arg_y) (len arg_z))
  (let ((nextw imm1)
        (accum imm0)
        (offset imm2))
    (cmp len (:$ 0))
    (mov offset (:$ arm64::misc-data-offset))
    (mov accum (:$ 0))
    (b.eq @done)
    @loop
    (subs len len (:$ 1))
    ;; 32-bit elements: load 64 bits (2 elements), step by 8 bytes.
    ;; This hashes pairs of characters, but the hash quality doesn't
    ;; need to exactly match ARM32.
    (ldr nextw (:@ str offset))
    (add offset offset (:$ 8))
    (ror accum accum (:$ 27))
    (eor accum accum nextw)
    (b.ne @loop)
    ;; Strip top bits: shift left 8, then right 8 to clear top byte (tag).
    (lsl accum accum (:$ 8))
    (lsr arg_z accum (:$ 8))
    @done
    (ret)))

(defarm64lapfunction %string-hash ((start arg_x) (str arg_y) (len arg_z))
  (let ((nextw imm1)
        (accum imm0)
        (offset imm2))
    (cmp len (:$ 0))
    ;; start is already a fixnum (= raw index on ARM64), scale by 8 for 64-bit loads
    (lsl offset start (:$ 3))
    (add offset offset (:$ arm64::misc-data-offset))
    (mov accum (:$ 0))
    (b.eq @done)
    @loop
    (subs len len (:$ 1))
    (ldr nextw (:@ str offset))
    (add offset offset (:$ 8))
    (ror accum accum (:$ 27))
    (eor accum accum nextw)
    (b.ne @loop)
    ;; Strip top bits
    (lsl accum accum (:$ 8))
    (lsr arg_z accum (:$ 8))
    @done
    (ret)))

;;; Ensure that the current thread's thread-local-binding vector
;;; contains room for an entry with index INDEX.
;;; Return the fixnum-tagged tlb vector.
(defarm64lapfunction %ensure-tlb-index ((idx arg_z))
  (ldr arg_y (:@ rcontext (:$ arm64::tcr.tlb-limit)))
  (cmp arg_y idx)
  (b.hi @ok)
  (uuo-tlb-too-small idx)
  @ok
  (ldr arg_z (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (ret))
