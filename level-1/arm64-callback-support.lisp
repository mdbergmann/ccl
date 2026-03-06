;;;-*-Mode: LISP; Package: CCL -*-
;;;
;;; Copyright 2024 Clozure Associates
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

;;; ARM64 callback trampoline generation.
;;; Port of arm-callback-support.lisp for the AAPCS64 calling convention.

(in-package "CCL")

;;; Generate a callback trampoline for the given callback INDEX.
;;; The trampoline loads the callback index into x12 (imm2),
;;; then loads and branches to the .SPaapcs64-callback subprim.
;;;
;;; ARM64 trampoline layout (24 bytes, 6 instructions worth but we use
;;; 3 instructions + 1 address = 20 bytes, padded to 24):
;;;   MOVZ  x12, #(low16 index)           ; load low 16 bits of index
;;;   MOVK  x12, #(high16 index), lsl #16 ; load high 16 bits of index
;;;   LDR   x16, [pc, #4]                 ; load callback handler address
;;;   BR    x16                            ; jump to handler
;;;   <8-byte address of .SPaapcs64-callback>
;;;
;;; Total size = 4*4 + 8 = 24 bytes.

(defun make-callback-trampoline (index &optional info)
  (declare (ignore info))
  (let* ((p (%allocate-callback-pointer 24))
         (low16 (ldb (byte 16 0) index))
         (high16 (ldb (byte 16 16) index))
         (handler (%lookup-subprim-address
                   #.(subprim-name->offset '.SPaapcs64-callback))))
    ;; MOVZ x12, #low16
    ;; Encoding: 1 10 100101 00 <imm16> <Rd>
    ;; = 0xD280000C | (low16 << 5)
    (setf (%get-unsigned-long p 0)
          (logior #xD280000C (ash low16 5)))
    ;; MOVK x12, #high16, LSL #16
    ;; Encoding: 1 11 100101 01 <imm16> <Rd>
    ;; = 0xF2A0000C | (high16 << 5)
    (setf (%get-unsigned-long p 4)
          (logior #xF2A0000C (ash high16 5)))
    ;; LDR x16, [pc, #8]  (loads from current PC + 8 = offset 16 in trampoline)
    ;; PC-relative literal load: opc=01 011 0 00 <imm19> <Rt>
    ;; imm19 = 8/4 = 2 (word offset from this instruction's PC)
    ;; = 0x58000010 | (2 << 5) = 0x58000050
    (setf (%get-unsigned-long p 8)
          #x58000050)
    ;; BR x16
    ;; Encoding: 1101011 0000 11111 000000 10000 00000
    ;; = 0xD61F0200
    (setf (%get-unsigned-long p 12)
          #xD61F0200)
    ;; 8-byte address of callback handler at offset 16
    (setf (%%get-unsigned-longlong p 16)
          (%ptr-to-int handler))
    ;; Flush instruction cache
    (ff-call (%kernel-import #.arm64::kernel-import-makedataexecutable)
             :address p
             :unsigned-fullword 24
             :void)
    p))
