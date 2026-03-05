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

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require "ARM64-ARCH")
  (require "DLL-NODE")
  (require "ARM64-ASM")
  (require "SUBPRIMS"))


(defun arm64-lap-macro-function (name)
  (declare (special *arm64-backend*))
  (gethash (string name) (backend-lap-macros *arm64-backend*)))

(defun (setf arm64-lap-macro-function) (def name)
  (declare (special *arm64-backend*))
  (let* ((s (string name)))
    (setf (gethash s (backend-lap-macros *arm64-backend*)) def)))

(defmacro defarm64lapmacro (name arglist &body body)
  `(progn
     (setf (arm64-lap-macro-function ',name)
           (nfunction (arm64-lap-macro ,name) ,(parse-macro name arglist body)))
     (record-source-file ',name 'lap-macro)
     ',name))

(defvar *arm64-lap-lfun-bits* 0)


(defun arm64-lap-macroexpand-1 (form)
  (unless (and (consp form) (atom (car form)))
    (values form nil))
  (let* ((expander (arm64-lap-macro-function (car form))))
    (if expander
      (values (funcall expander form nil) t)
      (values form nil))))


;;; ARM64: no constant pool, no data section needed.
;;; Instructions are encoded as s-expressions and stored in lap-instruction
;;; source slots.  arm64-finalize handles encoding and label resolution.
(defun %define-arm64-lap-function (name body &optional (bits 0))
  (with-dll-node-freelist (primary arm64::*lap-instruction-freelist*)
    (let* ((arm64::*lap-labels* ())
           (name-cell (list name))
           (arm64::*arm64-constants* ())
           (*arm64-lap-lfun-bits* bits)
           (arm64::*arm64-register-names* arm64::*standard-arm64-register-names*))
      (dolist (form body)
        (arm64-lap-form form primary))
      (rplacd name-cell (length arm64::*arm64-constants*))
      (push name-cell arm64::*arm64-constants*)
      (arm64-lap-generate-code primary
                               (arm64::arm64-finalize primary)
                               *arm64-lap-lfun-bits*))))


;;; ARM64 code vectors use 32-bit words stored as u32 elements.
(defun set-arm64-code-vector-word (code-vector i insn)
  (declare (type (simple-array (unsigned-byte 32) (*)) code-vector)
           (fixnum i)
           (optimize (speed 3) (safety 0)))
  (setf (aref code-vector i)
        (arm64::lap-instruction-opcode insn)))


(defun arm64-lap-generate-code (seg code-vector-size bits)
  (declare (fixnum code-vector-size))
  (let* ((target-backend *target-backend*)
         (cross-compiling (target-arch-case
                           (:arm64 (not (eq *host-backend* target-backend)))
                           (t t)))
         (constants-size (+ 3 (length arm64::*arm64-constants*)))
         (constants-vector (%alloc-misc
                            constants-size
                            (if cross-compiling
                              target::subtag-xfunction
                              target::subtag-function)))
         (i 0))
    (declare (fixnum i constants-size))
    (let* ((code-vector (%alloc-misc
                         code-vector-size
                         (if cross-compiling
                           target::subtag-xcode-vector
                           arm64::subtag-code-vector))))
      (do-dll-nodes (insn seg)
        (when (typep insn 'arm64::lap-instruction)
          (unless (eql (arm64::instruction-element-size insn) 0)
            (set-arm64-code-vector-word code-vector i insn)
            (incf i))))
      (dolist (immpair arm64::*arm64-constants*)
        (let* ((imm (car immpair))
               (k (cdr immpair)))
          (declare (fixnum k))
          (setf (uvref constants-vector (+ 2 k)) imm)))
      (setf (uvref constants-vector (1- constants-size)) bits ; lfun-bits
            (uvref constants-vector 1) code-vector
            (uvref constants-vector 0) 0)
      #+arm64-target (progn
                       (%fix-fn-entrypoint constants-vector)
                       (%make-code-executable code-vector))
      constants-vector)))


;;; ARM64 has no constant pool, so no drain-constant-pool needed.
(defun arm64-lap-pseudo-op (directive arg current)
  (ecase directive
    (:arglist (setq *arm64-lap-lfun-bits* (encode-lambda-list arg)))
    ((:code :text) current)  ; no-op, already in code section
    ((:word :opcode)
     (let* ((val (logand #xffffffff (eval arg)))
            (instruction (arm64::make-lap-instruction nil)))
       (setf (arm64::lap-instruction-opcode instruction) val)
       (arm64::emit-lap-instruction-element instruction current))))
  current)


(defun arm64-lap-form (form current)
  (if (and form (symbolp form))
    (arm64::emit-lap-label current form)
    (if (or (atom form) (not (symbolp (car form))))
      (error "~& unknown ARM64-LAP form: ~S ." form)
      (multiple-value-bind (expansion expanded)
                           (arm64-lap-macroexpand-1 form)
        (if expanded
          (arm64-lap-form expansion current)
          (let* ((name (car form)))
            (if (keywordp name)
              (arm64-lap-pseudo-op name (cadr form) current)
              (case name
                ((progn) (dolist (f (cdr form))
                           (arm64-lap-form f current)))
                ((let) (arm64-lap-equate-form (cadr form) (cddr form) current))
                (t
                 (arm64::assemble-instruction current form)))))))))
  current)

;;; (let ((name val) ...) &body body)
;;; each "val" gets a chance to be treated as an ARM64 register name
;;; before being evaluated.
(defun arm64-lap-equate-form (eqlist body current)
  (collect ((symbols)
            (vals))
    (let* ((arm64::*arm64-register-names* arm64::*arm64-register-names*))
      (dolist (pair eqlist)
        (destructuring-bind (symbol value) pair
          (unless (and symbol
                       (symbolp symbol)
                       (not (constant-symbol-p symbol))
                       (not (arm64::get-arm64-register symbol)))
            (error "~s is not a bindable symbol name . " symbol))
          (let* ((regval (and value
                              (or (typep value 'symbol)
                                  (typep value 'string))
                              (arm64::get-arm64-register value))))
            (if regval
              (arm64::define-arm64-register symbol regval)
              (progn
                (symbols symbol)
                (vals (eval value)))))))
    (progv (symbols) (vals)
      (dolist (form body current)
        (arm64-lap-form form current))))))


;;; ARM64 assemble-instruction for LAP: store the s-expression form in
;;; the lap-instruction source slot.  arm64-finalize encodes + resolves labels.
(defun arm64::assemble-instruction (seg form)
  (let* ((insn (arm64::make-lap-instruction form)))
    (arm64::emit-lap-instruction-element insn seg)))


(defmacro defarm64lapfunction (&environment env name arglist &body body
                               &aux doc)
  (if (not (endp body))
      (and (stringp (car body))
           (cdr body)
           (setq doc (car body))
           (setq body (cdr body))))
  `(progn
     (eval-when (:compile-toplevel)
       (note-function-info ',name t ,env))
     #-arm64-target
     (progn
       (eval-when (:load-toplevel)
         (%defun (nfunction ,name (lambda (&lap 0)
                                    (arm64-lap-function ,name ,arglist ,@body)))
                 ,doc))
       (eval-when (:execute)
         (%define-arm64-lap-function ',name '((let ,arglist ,@body)))))
     #+arm64-target
     (%defun (nfunction ,name (lambda (&lap 0)
                                (arm64-lap-function ,name ,arglist ,@body)))
             ,doc)))


(provide "ARM64-LAP")
