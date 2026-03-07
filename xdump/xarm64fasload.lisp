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
  (require "FASLENV" "ccl:xdump;faslenv")
  (require "ARM64-LAP"))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require "XFASLOAD" "ccl:xdump;xfasload"))


;;; Encode a single ARM64 instruction s-expression into a 32-bit word.
;;; Uses arm64-encode-instruction directly — no full LAP pipeline needed.
(defun xload-arm64-lap-word (instruction-form)
  (if (listp instruction-form)
    (arm64::arm64-encode-instruction instruction-form)
    instruction-form))


;;; Register numbers (from arm64-arch.lisp defarm64gpr):
;;;   fname = temp3 = x9  = 9
;;;   nfn   = temp2 = x10 = 10
;;;   arg_x = x13, arg_y = x14, arg_z = x15
;;;   nargs = x5, vsp = x25, rcontext = x28
;;;   lr = x30, fp = x29, sp = 31 (hardware)

;;; Macro-apply code: called when someone funcalls a macro or special operator.
;;; Must save fname (temp3=x9) to arg_y BEFORE the spcall clobbers temp3.
;;;
;;;   stp lr, vsp, [sp, #-16]!    ; build lisp frame
;;;   mov arg_y, fname             ; save fname before spcall
;;;   ldr temp3, [rcontext, #<.SPheap-rest-arg>]
;;;   blr temp3                    ; collect &rest args
;;;   ldr arg_z, [vsp], #8        ; vpop1 rest-arg list
;;;   mov arg_x, #$xnotfun        ; error code (13, unshifted)
;;;   mov nargs, #24               ; set-nargs 3 (3 * 8 bytes)
;;;   ldr temp3, [rcontext, #<.SPksignalerr>]
;;;   br temp3                     ; tail-call error signaler

(defparameter *arm64-macro-apply-code*
  (let* ((sp-heap-rest-arg (arm64::arm64-subprimitive-offset '.SPheap-rest-arg))
         (sp-ksignalerr (arm64::arm64-subprimitive-offset '.SPksignalerr))
         (code (list
                ;; stp lr(x30), vsp(x25), [sp, #-16]!
                (xload-arm64-lap-word `(stp 30 25 (:@! sp (:$ -16))))
                ;; mov arg_y(x14), fname(x9)
                (xload-arm64-lap-word `(mov 14 9))
                ;; ldr temp3(x9), [rcontext(x28), #offset]
                (xload-arm64-lap-word `(ldr 9 (:@ 28 (:$ ,sp-heap-rest-arg))))
                ;; blr temp3(x9)
                (xload-arm64-lap-word `(blr 9))
                ;; ldr arg_z(x15), [vsp(x25)], #8  (post-index)
                (xload-arm64-lap-word `(ldr 15 (:@+ 25 (:$ 8))))
                ;; mov arg_x(x13), #13  ($xnotfun=13, fixnumshift=0)
                (xload-arm64-lap-word `(mov 13 (:$ ,#.$xnotfun)))
                ;; mov nargs(x5), #24  (3 args * 8 bytes)
                (xload-arm64-lap-word `(mov 5 (:$ 24)))
                ;; ldr temp3(x9), [rcontext(x28), #offset]
                (xload-arm64-lap-word `(ldr 9 (:@ 28 (:$ ,sp-ksignalerr))))
                ;; br temp3(x9)
                (xload-arm64-lap-word `(br 9)))))
    (make-array (length code)
                :element-type '(unsigned-byte 32)
                :initial-contents code)))


(defun arm64-fixup-macro-apply-code ()
  *arm64-macro-apply-code*)


;;; Closure trampoline: jump to .SPcall-closure subprim.
;;;   ldr temp3(x9), [rcontext(x28), #<.SPcall-closure>]
;;;   br  temp3(x9)

(defparameter *arm64-closure-trampoline-code*
  (let* ((sp-call-closure (arm64::arm64-subprimitive-offset '.SPcall-closure))
         (code (list
                (xload-arm64-lap-word `(ldr 9 (:@ 28 (:$ ,sp-call-closure))))
                (xload-arm64-lap-word `(br 9)))))
    (make-array (length code)
                :element-type '(unsigned-byte 32)
                :initial-contents code)))


;;; Undefined function trampoline:
;;;   uuo-error-udf fname(x9)     ; HLT-based UUO; kernel patches function
;;;   ldr nfn(x10), [fname(x9), #16]   ; symbol.fcell = 16
;;;   ldr temp3(x9), [nfn(x10), #0]    ; function.entrypoint = 0
;;;   br  temp3(x9)

(defparameter *arm64-udf-code*
  (let* ((code (list
                (xload-arm64-lap-word `(uuo-error-udf 9))
                (xload-arm64-lap-word `(ldr 10 (:@ 9 (:$ ,arm64::symbol.fcell))))
                (xload-arm64-lap-word `(ldr 9 (:@ 10 (:$ ,arm64::function.entrypoint))))
                (xload-arm64-lap-word `(br 9)))))
    (make-array (length code)
                :element-type '(unsigned-byte 32)
                :initial-contents code)))


;;; Initialize static space with a u64 vector and the NIL cons pair.
;;; Follows x86-64 pattern for 64-bit platform.
(defun arm64-initialize-static-space ()
  (xload-make-ivector *xload-static-space*
                      (xload-target-subtype :unsigned-64-bit-vector)
                      (1- (/ 4096 8)))     ; 511 u64 elements
  ;; Make NIL — one dnode (16 bytes) at nil-base.
  ;; CDR(NIL) at nil-base+0, CAR(NIL) at nil-base+8.
  ;; ARM64 TBI tagging needs only one cons cell (unlike x8664 which
  ;; needs two for its misaligned fulltag scheme).
  ;; T's symbol header follows immediately at nil-base+16.
  (xload-make-cons *xload-target-nil* *xload-target-nil* *xload-static-space*))


;;; Backend registration for darwinarm64.
;;;
;;; Address computation (16KB-page-aligned for macOS ARM64):
;;;   nil-value = #x0200000200011008  (tag-nil=2 in top byte, effective addr = #x200011008)
;;;   untagged-nil = nil-value - (ash tag-nil tag-shift) = #x200011008
;;;   static-space-address = untagged-nil - node-size - 4096 = #x200010000 (16KB-aligned)
;;;   image-base-address = untagged-nil - node-size + 4096 = #x200012000

(defparameter *darwinarm64-xload-backend*
  (make-backend-xload-info
   :name :darwinarm64
   :macro-apply-code-function 'arm64-fixup-macro-apply-code
   :closure-trampoline-code *arm64-closure-trampoline-code*
   :udf-code *arm64-udf-code*
   :default-image-name "ccl:ccl;arm64-boot.image"
   :default-startup-file-name "level-1.da64fsl"
   :subdirs '("ccl:level-0;ARM64;")
   :compiler-target-name :darwinarm64
   :image-base-address (+ (- arm64::nil-value (ash arm64::tag-nil arm64::tag-shift))
                          (- arm64::node-size)
                          (ash 1 12))
   :nil-relative-symbols arm64::*arm64-nil-relative-symbols*
   :static-space-init-function 'arm64-initialize-static-space
   :purespace-reserve (ash 128 30)       ; 128 MB (64-bit, like x86-64)
   :static-space-address (- (- arm64::nil-value (ash arm64::tag-nil arm64::tag-shift))
                            arm64::node-size
                            (ash 1 12))))

(add-xload-backend *darwinarm64-xload-backend*)

(provide "XARM64FASLOAD")
