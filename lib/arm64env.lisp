;;; -*- Mode:Lisp; Package:CCL; -*-
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

(defconstant $numarm64saveregs 0)
(defconstant $numarm64argregs 3)


(defconstant arm64-nonvolatile-registers-mask
  0)

(defconstant arm64-arg-registers-mask
  (logior (ash 1 arm64::arg_z)
          (ash 1 arm64::arg_y)
          (ash 1 arm64::arg_x)))

(defconstant arm64-temp-registers-mask
  (logior (ash 1 arm64::temp0)
          (ash 1 arm64::temp1)
          (ash 1 arm64::temp2)
          (ash 1 arm64::temp3)))


(defconstant arm64-tagged-registers-mask
  (logior arm64-temp-registers-mask
          arm64-arg-registers-mask
          arm64-nonvolatile-registers-mask))



;;; NOTE: temp2 = nfn = x10 is NOT included here.
;;; On ARM64, fn and nfn are the same register (x10).  Unlike ARM32 where
;;; fn=r11 (callee-saved) is separate from nfn=r9=temp2, ARM64 uses x10
;;; for both ref-constant (function immediates) and nfn (current function).
;;; If the allocator assigns x10 for temp use, it clobbers nfn, and
;;; subsequent ref-constant vinsns will load from address 0 → crash.
;;;
;;; NOTE: temp3 = fname = x9 is also NOT included here.
;;; Bug 127: fname is used implicitly by call-known-symbol to hold the
;;; target symbol.  Before each symbol call, the compiler loads the symbol
;;; into x9 via ref-constant, clobbering any local variable the allocator
;;; placed there.  Although :call vinsns mark all registers as clobbered,
;;; the register allocator's linear-scan approach doesn't always insert
;;; proper spill/reload around loop back-edges that cross function calls.
;;; Excluding x9 from allocatable temps avoids this class of bugs entirely.
(defconstant arm64-temp-node-regs
  (make-mask arm64::temp0
             arm64::temp1
             arm64::arg_x
             arm64::arg_y
             arm64::arg_z))

(defconstant arm64-nonvolatile-node-regs
  0)


(defconstant arm64-node-regs (logior arm64-temp-node-regs arm64-nonvolatile-node-regs))

(defconstant arm64-imm-regs (make-mask
                            arm64::imm0
                            arm64::imm1
                            arm64::imm2
                            arm64::imm3
                            arm64::imm4))

(defconstant arm64-temp-fp-regs (1- (ash 1 30)))

(defconstant arm64-cr-fields (make-mask 0))





(defconstant $undo-arm64-c-frame 16)


(ccl::provide "ARM64ENV")
