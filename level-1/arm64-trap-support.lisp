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

;;; ARM64 trap/exception support.
;;; Port of arm-trap-support.lisp for Darwin ARM64 (AArch64).
;;;
;;; Darwin ARM64 mcontext layout (from platform-darwinarm64.h):
;;;   uc_mcontext->__ss.__x[0..28]  : GPRs x0-x28 (8 bytes each)
;;;   uc_mcontext->__ss.__fp         : x29 (contiguous after __x[28])
;;;   uc_mcontext->__ss.__lr         : x30 (contiguous after __fp)
;;;   uc_mcontext->__ss.__sp         : hardware SP
;;;   uc_mcontext->__ss.__pc         : program counter
;;;   uc_mcontext->__ss.__cpsr       : condition flags
;;;
;;; GPR register numbers 0-30 can be accessed via indexing from __x[0]
;;; since __fp and __lr are contiguous in memory.

(in-package "CCL")

;;; Darwin ARM64: access GPRs via uc_mcontext->__ss
(defmacro with-xp-registers-and-gpr-offset ((xp register-number)
                                            (registers offset) &body body)
  (let* ((regform `(pref ,xp :ucontext_t.uc_mcontext.__ss)))
    `(with-macptrs ((,registers ,regform))
      (let ((,offset (xp-gpr-offset ,register-number)))
        ,@body))))

;;; GPR offset: register-number * 8 (node-size).
;;; Valid register numbers: 0-30 (x0 through x30/lr).
(defun xp-gpr-offset (register-number)
  (unless (and (fixnump register-number)
               (<= 0 (the fixnum register-number))
               (< (the fixnum register-number) 31))
    (setq register-number (require-type register-number '(integer 0 (31)))))
  (the fixnum (* (the fixnum register-number) arm64::node-size)))

;;; CPSR is at a separate offset in the thread state structure.
;;; In __darwin_arm_thread_state64: __x[29], __fp, __lr, __sp, __pc, __cpsr
;;; Offset of __cpsr relative to __x[0]:
;;;   29*8 + 8 + 8 + 8 + 8 = 264 bytes
;;; CPSR is a 32-bit field.
(defconstant cpsr-offset-in-register-context
  (get-field-offset :__darwin_arm_thread_state64.__cpsr))

(defun xp-cpsr (xp)
  "Read the CPSR (condition flags) from the exception context."
  (with-macptrs ((regs (pref xp :ucontext_t.uc_mcontext.__ss)))
    (%get-unsigned-long regs cpsr-offset-in-register-context)))

;;; Read a GPR as a lisp object (64-bit).
(defun xp-gpr-lisp (xp register-number)
  (with-xp-registers-and-gpr-offset (xp register-number) (registers offset)
    (values (%get-object registers offset))))

(defun (setf xp-gpr-lisp) (value xp register-number)
  (with-xp-registers-and-gpr-offset (xp register-number) (registers offset)
    (%set-object registers offset value)))

;;; Read a GPR as a signed 32-bit value.
(defun xp-gpr-signed-long (xp register-number)
  (with-xp-registers-and-gpr-offset (xp register-number) (registers offset)
    (values (%get-signed-long registers offset))))

;;; Read a GPR as an unsigned 32-bit value.
(defun xp-gpr-unsigned-long (xp register-number)
  (with-xp-registers-and-gpr-offset (xp register-number) (registers offset)
    (values (%get-unsigned-long registers offset))))

;;; Read a GPR as a signed 64-bit doubleword.
(defun xp-gpr-signed-doubleword (xp register-number)
  (with-xp-registers-and-gpr-offset (xp register-number) (registers offset)
    (values (%%get-signed-longlong registers offset))))

;;; Read a GPR as an unsigned 64-bit doubleword.
(defun xp-gpr-unsigned-doubleword (xp register-number)
  (with-xp-registers-and-gpr-offset (xp register-number) (registers offset)
    (values (%%get-unsigned-longlong registers offset))))

;;; Read a GPR as a macptr.
(defun xp-gpr-macptr (xp register-number)
  (with-xp-registers-and-gpr-offset (xp register-number) (registers offset)
    (values (%get-ptr registers offset))))

;;; Return the code offset within FN for a return address at the given
;;; machine-state-offset in the register context.
(defun return-address-offset (xp fn machine-state-offset)
  (with-macptrs ((regs (pref xp :ucontext_t.uc_mcontext.__ss)))
    (if (functionp fn)
      ;; ARM64: code-vector is at slot 2 (xcode-vector) in the function object
      (or (%code-vector-pc (uvref fn 1) (%inc-ptr regs machine-state-offset))
           (%get-ptr regs machine-state-offset))
      (%get-ptr regs machine-state-offset))))

;;; LR and PC offsets within the __darwin_arm_thread_state64 structure.
(defconstant lr-offset-in-register-context
  (get-field-offset :__darwin_arm_thread_state64.__lr))

(defconstant pc-offset-in-register-context
  (get-field-offset :__darwin_arm_thread_state64.__pc))

;;; Set the PC in the exception context (for UDF call restarts, etc.)
(defun set-xp-pc (xp new-pc)
  (with-macptrs ((regs (pref xp :ucontext_t.uc_mcontext.__ss)))
    (%set-object regs pc-offset-in-register-context new-pc)))

;;; Build fake stack frames from the exception context and call THUNK.
;;; ARM64 uses nfn (x10) as the primary function register (no separate fn).
(defun funcall-with-xp-stack-frames (xp trap-function thunk)
  (cond ((null trap-function)
         ;; Maybe inside a subprim from a lisp function.
         ;; On ARM64, nfn is the function register.
         (let* ((fn (xp-gpr-lisp xp arm64::nfn))
                (lr (return-address-offset
                     xp fn lr-offset-in-register-context)))
           (if (fixnump lr)
             (let* ((sp (xp-gpr-lisp xp arm64::fp))
                    (vsp (xp-gpr-lisp xp arm64::vsp))
                    (frame (make-fake-stack-frame sp sp fn lr vsp xp)))
               (declare (dynamic-extent frame))
               (funcall thunk (%dnode-address-of frame)))
             (funcall thunk (xp-gpr-lisp xp arm64::fp)))))
        ((eq trap-function (xp-gpr-lisp xp arm64::nfn))
         (let* ((sp (xp-gpr-lisp xp arm64::fp))
                (fn trap-function)
                (lr (return-address-offset
                     xp fn pc-offset-in-register-context))
                (vsp (xp-gpr-lisp xp arm64::vsp))
                (frame (make-fake-stack-frame sp sp fn lr vsp xp)))
           (declare (dynamic-extent frame))
           (funcall thunk (%dnode-address-of frame))))
        (t (funcall thunk (xp-gpr-lisp xp arm64::fp)))))

(defparameter *pending-gc-notification-hook* nil)

;;; xcmain: the callback from the kernel's signal handler.
;;; Signature matches callback_to_lisp in arm64-exceptions.c:
;;;   callback_ptr(xp, arg1, arg2, fnreg, offset)
;;; where arg1 = signal number, arg2 = extra info.
(defcallback xcmain (:address xp
                              :signed-fullword signal
                              :signed-fullword arg
                              :signed-fullword fnreg
                              :signed-fullword offset)
  (with-xp-stack-frames (xp (unless (eql 0 fnreg) (xp-gpr-lisp xp fnreg)) frame-ptr)
    (cond ((eql signal 0) (cmain))
          ((or (eql signal #$SIGBUS)
               (eql signal #$SIGSEGV))
           (%error (make-condition 'invalid-memory-access
                                   :address arg
                                   :write-p (eql signal #$SIGBUS))
                   ()
                   frame-ptr))
          ((eql signal #$SIGTRAP)
           (let* ((hook *pending-gc-notification-hook*))
               (declare (special *pending-gc-notification-hook*))
               (when hook (funcall hook))))
          (t
           (error "cmain callback: signal = ~d, arg = #x~x, fnreg = ~d, offset = ~d"
                  signal arg fnreg offset)))))
