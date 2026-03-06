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

;;; ARM64 error/UUO dispatch.
;;; Port of arm-error-signal.lisp for the ARM64 HLT-based UUO scheme.
;;;
;;; ARM64 UUOs use the HLT instruction with a 16-bit immediate.
;;; The kernel extracts: imm16 = (instruction >> 5) & 0xFFFF
;;;   format = imm16 & 0x7          (bits 0-2)
;;;   reg    = (imm16 >> 3) & 0x1F  (bits 3-7)
;;;   info   = (imm16 >> 8) & 0xFF  (bits 8-15)
;;;
;;; Format codes (from arm64-constants.h):
;;;   0 = nullary (wrong-nargs, etc.)
;;;   1 = unary-reg-not-lisptag
;;;   2 = unary-reg-not-fulltag
;;;   3 = unary-reg-not-subtag
;;;   4 = unary-reg-not-xtype
;;;   5 = unary-misc (not-callable, no-throw-tag, unbound, tlb-too-small)
;;;   6 = binary (vector-bounds, slot-unbound, array-rank, etc.)
;;;
;;; The kernel calls handle_error which calls callback_for_trap(errdisp, xp, 0, the_uuo, &bump).
;;; So %xerr-disp receives: error-number=0, arg=the raw HLT instruction.

(in-package "CCL")

;;; xtype specifiers table — maps ARM64 xtype codes to CL type specifiers.
(defparameter *arm64-xtype-specifiers* (make-array 256 :initial-element nil))

(macrolet ((init-arm64-xtype-table (&rest pairs)
             (let* ((table (gensym)))
               (collect ((body))
                 (dolist (pair pairs)
                   (destructuring-bind (code . spec) pair
                     (body `(setf (svref ,table ,code) ',spec))))
                 `(let* ((,table *arm64-xtype-specifiers*))
                   ,@(body))))))
  (init-arm64-xtype-table
   ;; Tag-based types (top byte values)
   (arm64::tag-positive-fixnum . fixnum)
   (arm64::tag-cons . list)
   ;; Extended types (xtype-* constants)
   (arm64::xtype-integer . integer)
   (arm64::xtype-s64 . (signed-byte 64))
   (arm64::xtype-u64 . (unsigned-byte 64))
   (arm64::xtype-s32 . (signed-byte 32))
   (arm64::xtype-u32 . (unsigned-byte 32))
   (arm64::xtype-s16 . (signed-byte 16))
   (arm64::xtype-u16 . (unsigned-byte 16))
   (arm64::xtype-s8  . (signed-byte 8))
   (arm64::xtype-u8  . (unsigned-byte 8))
   (arm64::xtype-bit . bit)
   (arm64::xtype-rational . rational)
   (arm64::xtype-real . real)
   (arm64::xtype-number . number)
   (arm64::xtype-char-code . (mod #x110000))
   (arm64::xtype-unsigned-byte-24 . (unsigned-byte 24))
   (arm64::xtype-array2d . (array * (* *)))
   (arm64::xtype-array3d . (array * (* * *)))
   ;; Subtag-based types
   (arm64::subtag-bignum . bignum)
   (arm64::subtag-ratio . ratio)
   (arm64::subtag-double-float . double-float)
   (arm64::subtag-complex . complex)
   (arm64::subtag-macptr . macptr)
   (arm64::subtag-xcode-vector . xcode-vector)
   (arm64::subtag-catch-frame . catch-frame)
   (arm64::subtag-function . function)
   (arm64::subtag-basic-stream . basic-stream)
   (arm64::subtag-symbol . symbol)
   (arm64::subtag-lock . lock)
   (arm64::subtag-hash-vector . hash-vector)
   (arm64::subtag-pool . pool)
   (arm64::subtag-weak . population)
   (arm64::subtag-package . package)
   (arm64::subtag-slot-vector . slot-vector)
   (arm64::subtag-instance . standard-object)
   (arm64::subtag-struct . structure-object)
   (arm64::subtag-istruct . istruct)
   (arm64::subtag-value-cell . value-cell)
   (arm64::subtag-xfunction . xfunction)
   (arm64::subtag-arrayH . array-header)
   (arm64::subtag-vectorH . vector-header)
   (arm64::subtag-simple-vector . simple-vector)
   (arm64::subtag-single-float-vector . (simple-array single-float (*)))
   (arm64::subtag-u32-vector . (simple-array (unsigned-byte 32) (*)))
   (arm64::subtag-s32-vector . (simple-array (signed-byte 32) (*)))
   (arm64::subtag-fixnum-vector . (simple-array fixnum (*)))
   (arm64::subtag-simple-base-string . simple-base-string)
   (arm64::subtag-u8-vector . (simple-array (unsigned-byte 8) (*)))
   (arm64::subtag-s8-vector . (simple-array (signed-byte 8) (*)))
   (arm64::subtag-u16-vector . (simple-array (unsigned-byte 16) (*)))
   (arm64::subtag-double-float-vector . (simple-array double-float (*)))
   (arm64::subtag-bit-vector . simple-bit-vector)
   (arm64::subtag-complex-single-float-vector . (simple-array (complex single-float) (*)))
   (arm64::subtag-complex-double-float-vector . (simple-array (complex double-float) (*)))))


;;; Extract argument list from the exception context.
;;; ARM64: nargs is in x5 and counts in bytes (n * node-size = n * 8).
;;; On ARM64 with fixnumshift=0, nargs IS the byte count AND the fixnum count.
;;; Actually nargs = n * 8. So (/ nargs 8) gives the count.
(defun xp-argument-list (xp)
  (let ((nargs-bytes (xp-gpr-lisp xp arm64::nargs))
        (arg-x (xp-gpr-lisp xp arm64::arg_x))
        (arg-y (xp-gpr-lisp xp arm64::arg_y))
        (arg-z (xp-gpr-lisp xp arm64::arg_z)))
    ;; nargs is in bytes: 8 per arg (fixnumshift=0, node-size=8)
    (let ((nargs (ash nargs-bytes -3)))
      (cond ((eql nargs 0) nil)
            ((eql nargs 1) (list arg-z))
            ((eql nargs 2) (list arg-y arg-z))
            (t (let ((args (list arg-x arg-y arg-z)))
                 (if (eql nargs 3)
                   args
                   (let ((vsp (xp-gpr-macptr xp arm64::vsp)))
                     (dotimes (i (- nargs 3))
                       (push (%get-object vsp (* i target::node-size)) args))
                     args))))))))

;;; Handle an undefined function call.
(defun handle-udf-call (xp frame-ptr)
  (let* ((args (xp-argument-list xp))
         (values (multiple-value-list
                  (%kernel-restart-internal
                   $xudfcall
                   (list (maybe-setf-name (xp-gpr-lisp xp arm64::fname)) args)
                   frame-ptr)))
         (stack-argcnt (max 0 (- (length args) 3)))
         (vsp (%i+ (xp-gpr-lisp xp arm64::vsp)
                    (* stack-argcnt arm64::node-size)))
         (f #'(lambda (values) (apply #'values values))))
    (setf (xp-gpr-lisp xp arm64::vsp) vsp
          ;; nargs = 1 arg, in bytes = 8
          (xp-gpr-lisp xp arm64::nargs) arm64::node-size
          (xp-gpr-lisp xp arm64::arg_z) values
          (xp-gpr-lisp xp arm64::nfn) f)
    ;; Set the PC in the mcontext to the function's entrypoint.
    ;; ARM64 PC is not a GPR; use set-xp-pc to modify the mcontext directly.
    (set-xp-pc xp (uvref f 0))))


;;; Main UUO dispatch callback.
;;; Called from the kernel via handle_error → callback_for_trap → callback_to_lisp.
;;; error-number = 0 for UUOs, non-zero for other errors.
;;; arg = the raw HLT instruction (32-bit) when error-number = 0.
(defcallback %xerr-disp (:address xp
                                  :signed-fullword error-number
                                  :unsigned-fullword arg
                                  :unsigned-fullword fnreg
                                  :unsigned-fullword relative-pc
                                  :int)
  (let* ((fn (unless (eql 0 fnreg) (xp-gpr-lisp xp fnreg)))
         (delta 0))
    (with-xp-stack-frames (xp fn frame-ptr)
      (with-error-reentry-detection
          (cond
            ((eql 0 error-number)       ; UUO (HLT instruction)
             (setq delta 4)
             ;; Extract the 16-bit immediate from the HLT instruction.
             ;; HLT encoding: 0xD4400000 | (imm16 << 5)
             (let* ((imm16 (ldb (byte 16 5) arg))
                    (format (ldb (byte 3 0) imm16))
                    (reg (ldb (byte 5 3) imm16))
                    (info (ldb (byte 8 8) imm16)))

               (case format
                 ;; Format 0: Nullary — wrong nargs
                 (0
                  (let* ((nullary-info (ldb (byte 13 3) imm16)))
                    (case nullary-info
                      (1                ;wrong-nargs
                       ;; Determine too-few vs too-many from CPSR carry flag.
                       ;; The nargs check does CMP nargs, #expected:
                       ;; if nargs < expected → carry clear → too-few
                       ;; if nargs >= expected → carry set → too-many
                       ;; (but we got here because NE, so not equal)
                       (let* ((condition-name
                               ;; CPSR bit 29 = carry flag
                               (let* ((cpsr (xp-cpsr xp)))
                                 (if (logbitp 29 cpsr)
                                   'too-many-arguments
                                   'too-few-arguments))))
                         (%error condition-name
                                 (list :nargs (ash (xp-gpr-lisp xp arm64::nargs) -3)
                                       :fn fn)
                                 frame-ptr)))
                      (t
                       (%error "Unknown nullary UUO code ~d"
                               (list nullary-info)
                               frame-ptr)))))

                 ;; Format 1: unary-reg-not-lisptag
                 (1
                  (%error (make-condition
                           'type-error
                           :datum (xp-gpr-lisp xp reg)
                           :expected-type
                           (svref *arm64-xtype-specifiers* info))
                          nil
                          frame-ptr))

                 ;; Format 2: unary-reg-not-fulltag
                 (2
                  (%error (make-condition
                           'type-error
                           :datum (xp-gpr-lisp xp reg)
                           :expected-type
                           (svref *arm64-xtype-specifiers* info))
                          nil
                          frame-ptr))

                 ;; Format 3: unary-reg-not-subtag
                 (3
                  (%error (make-condition
                           'type-error
                           :datum (xp-gpr-lisp xp reg)
                           :expected-type
                           (svref *arm64-xtype-specifiers* info))
                          nil
                          frame-ptr))

                 ;; Format 4: unary-reg-not-xtype
                 (4
                  (%error (make-condition
                           'type-error
                           :datum (xp-gpr-lisp xp reg)
                           :expected-type
                           (svref *arm64-xtype-specifiers* info))
                          nil
                          frame-ptr))

                 ;; Format 5: unary-misc
                 (5
                  (let* ((misc-code info))
                    (case misc-code
                      (0                ;not-callable / udf
                       (setq delta 0)
                       (handle-udf-call xp frame-ptr))
                      (1                ;no-throw-tag
                       (%error (make-condition 'cant-throw-error
                                               :tag (xp-gpr-lisp xp reg))
                               nil frame-ptr))
                      (3                ;unbound
                       (setf (xp-gpr-lisp xp reg)
                             (%kernel-restart-internal $xvunbnd
                                                       (list (xp-gpr-lisp xp reg))
                                                       frame-ptr)))
                      (t
                       (error "Unknown unary-misc UUO with code ~d." misc-code)))))

                 ;; Format 6: binary
                 (6
                  (let* ((reg1 reg)         ; bits 3-7
                         (reg2 (ldb (byte 5 8) imm16))  ; bits 8-12
                         (subcode (ldb (byte 3 13) imm16))) ; bits 13-15
                    (case subcode
                      (0                ;vector-bounds / array-axis-bounds
                       (%error (%rsc-string $xarroob)
                               (list (xp-gpr-lisp xp reg1)
                                     (xp-gpr-lisp xp reg2))
                               frame-ptr))
                      (1                ;slot-unbound
                       (let* ((instance (xp-gpr-lisp xp reg1))
                              (index (xp-gpr-lisp xp reg2)))
                         (setq *error-reentry-count* 0)
                         (%slot-unbound-trap instance index frame-ptr)))
                      (t
                       (error "Unknown binary UUO with subcode ~d" subcode)))))

                 (t
                  (error "Unknown UUO, format ~d" format)))))
            ((eql error-number arch::error-stack-overflow)
             (%error
              (make-condition
               'stack-overflow-condition
               :format-control "Stack overflow on ~a stack."
               :format-arguments (list (if (eql arg arm64::vsp) "value" "control")))
              nil frame-ptr))
            ((eql error-number arch::error-allocation-disabled)
             (restart-case (%error 'allocation-disabled nil frame-ptr)
               (continue ()
                         :report (lambda (stream)
                                   (format stream "retry the heap allocation.")))))
            (t
             (error "%errdisp callback: error-number = ~d, arg = #x~x, fnreg = ~d, rpc = ~d"
                    error-number arg fnreg relative-pc)))))
    delta))
