;;;-*- Mode: Lisp; Package: CCL -*-
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

;;; FFI support for Darwin ARM64 (AAPCS64 calling convention).
;;;
;;; AAPCS64 key rules:
;;;   - Up to 8 GP registers (x0-x7) for integer/pointer args
;;;   - Up to 8 FP registers (d0-d7) for float/double args
;;;   - Stack args are 8-byte aligned
;;;   - Structs <= 16 bytes returned in x0/x1
;;;   - Structs > 16 bytes returned via implicit first pointer arg
;;;   - HFA (Homogeneous Float Aggregate) of up to 4 floats/doubles
;;;     returned in FP regs — treated as large struct for simplicity initially

(in-package "CCL")

;;; Returns T if the record type is too large to be returned in registers
;;; and must be returned via an implicit pointer argument.
;;; AAPCS64: structs <= 16 bytes are returned in x0/x1.
(defun arm64-darwin::record-type-returns-structure-as-first-arg (rtype)
  (when (and rtype
             (not (typep rtype 'unsigned-byte))
             (not (member rtype *foreign-representation-type-keywords*
                          :test #'eq)))
    (let* ((ftype (if (typep rtype 'foreign-type)
                    rtype
                    (parse-foreign-type rtype))))
      (when (typep ftype 'foreign-record-type)
        (ensure-foreign-type-bits ftype)
        (> (foreign-type-bits ftype) 128)))))


;;; Expand an ff-call form for AAPCS64.
;;; Records > 16 bytes are passed by pointer (address).
;;; Smaller records are passed by value (as integer).
(defun arm64-darwin::expand-ff-call (callform args &key (arg-coerce #'null-coerce-foreign-arg) (result-coerce #'null-coerce-foreign-result))
  (let* ((result-type-spec (or (car (last args)) :void))
         (enclosing-form nil)
         (result-form nil))
    (multiple-value-bind (result-type error)
        (ignore-errors (parse-foreign-type result-type-spec))
      (if error
        (setq result-type-spec :void result-type *void-foreign-type*)
        (setq args (butlast args)))
      (collect ((argforms))
        (when (typep result-type 'foreign-record-type)
          (setq result-form (pop args))
          (if (arm64-darwin::record-type-returns-structure-as-first-arg result-type)
            (progn
              (setq result-type *void-foreign-type*
                    result-type-spec :void)
              (argforms :address)
              (argforms result-form))
            ;; Small struct: returned in x0 (and possibly x1) as integer
            (let* ((bits (ensure-foreign-type-bits result-type)))
              (if (<= bits 64)
                (progn
                  (setq result-type (parse-foreign-type :unsigned-doubleword)
                        result-type-spec :unsigned-doubleword
                        enclosing-form `(setf (%%get-unsigned-longlong ,result-form 0))))
                ;; 65-128 bits: returned in x0/x1
                ;; For now, treat as implicit pointer (caller provides buffer)
                (progn
                  (setq result-type *void-foreign-type*
                        result-type-spec :void)
                  (argforms :address)
                  (argforms result-form))))))
        (unless (evenp (length args))
          (error "~s should be an even-length list of alternating foreign types and values" args))
        (do* ((args args (cddr args)))
             ((null args))
          (let* ((arg-type-spec (car args))
                 (arg-value-form (cadr args)))
            (if (or (member arg-type-spec *foreign-representation-type-keywords*
                           :test #'eq)
                    (typep arg-type-spec 'unsigned-byte))
              (progn
                (argforms arg-type-spec)
                (argforms arg-value-form))
              (let* ((ftype (parse-foreign-type arg-type-spec)))
                (if (typep ftype 'foreign-record-type)
                  (let* ((bits (ensure-foreign-type-bits ftype)))
                    (if (> bits 128)
                      ;; Large struct: pass by pointer
                      (progn
                        (argforms :address)
                        (argforms arg-value-form))
                      ;; Small struct (<=16 bytes): pass by value
                      ;; Passed as 1 or 2 doublewords
                      (if (<= bits 64)
                        (progn
                          (argforms :unsigned-doubleword)
                          (argforms `(%%get-unsigned-longlong ,arg-value-form 0)))
                        (progn
                          (argforms :unsigned-doubleword)
                          (argforms `(%%get-unsigned-longlong ,arg-value-form 0))
                          (argforms :unsigned-doubleword)
                          (argforms `(%%get-unsigned-longlong ,arg-value-form 8))))))
                  (progn
                    (argforms (foreign-type-to-representation-type ftype))
                    (argforms (funcall arg-coerce arg-type-spec arg-value-form))))))))
        (argforms (foreign-type-to-representation-type result-type))
        (let* ((call (funcall result-coerce result-type-spec `(,@callform ,@(argforms)))))
          (if enclosing-form
            `(,@enclosing-form ,call)
            call))))))


;;; Generate let-bindings for callback arguments.
;;; AAPCS64: GP args at 8-byte offsets from stack-ptr.
;;; FP args are in a separate area pointed to by fp-args-ptr.
;;;
;;; Return 7 values:
;;; A list of RLET bindings
;;; A list of LET* bindings
;;; A list of DYNAMIC-EXTENT declarations
;;; A list of initialization forms for structure args
;;; A FOREIGN-TYPE representing the "actual" return type
;;; A form to initialize FP-ARGS-PTR (relative to STACK-PTR)
;;; The byte offset of the foreign return address relative to STACK-PTR
(defun arm64-darwin::generate-callback-bindings (stack-ptr fp-args-ptr argvars argspecs result-spec struct-result-name)
  (collect ((lets)
            (rlets)
            (dynamic-extent-names))
    (let* ((rtype (parse-foreign-type result-spec)))
      (when (typep rtype 'foreign-record-type)
        (let* ((bits (ensure-foreign-type-bits rtype)))
          (if (<= bits 128)
            (rlets (list struct-result-name (foreign-record-type-name rtype)))
            (setq argvars (cons struct-result-name argvars)
                  argspecs (cons :address argspecs)
                  rtype *void-foreign-type*))))
      (let* ((gp-offset 0)
             (fp-offset 0))
        (do* ((argvars argvars (cdr argvars))
              (argspecs argspecs (cdr argspecs)))
             ((null argvars)
              (values (rlets) (lets) (dynamic-extent-names) nil rtype nil 0))
          (let* ((name (car argvars))
                 (spec (car argspecs))
                 (argtype (parse-foreign-type spec)))
            (if (typep argtype 'foreign-record-type)
              (setq argtype (parse-foreign-type :address)))
            (let* ((access-form
                    (cond
                      ((typep argtype 'foreign-single-float-type)
                       (prog1
                         `(%get-single-float ,fp-args-ptr ,fp-offset)
                         (incf fp-offset 8))) ; FP slots are 8 bytes
                      ((typep argtype 'foreign-double-float-type)
                       (prog1
                         `(%get-double-float ,fp-args-ptr ,fp-offset)
                         (incf fp-offset 8)))
                      ((and (typep argtype 'foreign-integer-type)
                            (= (foreign-integer-type-bits argtype) 64)
                            (foreign-integer-type-signed argtype))
                       (prog1
                         `(%%get-signed-longlong ,stack-ptr ,gp-offset)
                         (incf gp-offset 8)))
                      ((and (typep argtype 'foreign-integer-type)
                            (= (foreign-integer-type-bits argtype) 64)
                            (not (foreign-integer-type-signed argtype)))
                       (prog1
                         `(%%get-unsigned-longlong ,stack-ptr ,gp-offset)
                         (incf gp-offset 8)))
                      ((typep argtype 'foreign-pointer-type)
                       (prog1
                         `(%get-ptr ,stack-ptr ,gp-offset)
                         (incf gp-offset 8)))
                      ((typep argtype 'foreign-integer-type)
                       (let* ((bits (foreign-integer-type-bits argtype))
                              (signed (foreign-integer-type-signed argtype)))
                         (prog1
                           (cond ((<= bits 8)
                                  (if signed
                                    `(%get-signed-byte ,stack-ptr ,gp-offset)
                                    `(%get-unsigned-byte ,stack-ptr ,gp-offset)))
                                 ((<= bits 16)
                                  (if signed
                                    `(%get-signed-word ,stack-ptr ,gp-offset)
                                    `(%get-unsigned-word ,stack-ptr ,gp-offset)))
                                 ((<= bits 32)
                                  (if signed
                                    `(%get-signed-long ,stack-ptr ,gp-offset)
                                    `(%get-unsigned-long ,stack-ptr ,gp-offset)))
                                 (t
                                  (error "Don't know how to access foreign argument of type ~s" (unparse-foreign-type argtype))))
                           (incf gp-offset 8)))) ; All GP slots are 8 bytes
                      (t
                       (error "Don't know how to access foreign argument of type ~s" (unparse-foreign-type argtype))))))
              (when name (lets (list name access-form))))))))))


;;; Generate code to store the callback return value.
;;; AAPCS64: return value at offset -8 from stack-ptr (same convention as ARM32).
(defun arm64-darwin::generate-callback-return-value (stack-ptr fp-args-ptr result return-type struct-return-arg)
  (declare (ignore fp-args-ptr))
  (unless (eq return-type *void-foreign-type*)
    (let* ((return-type-keyword
            (if (typep return-type 'foreign-record-type)
              (let* ((bits (ensure-foreign-type-bits return-type)))
                (if (<= bits 64)
                  (progn
                    (setq result `(%%get-unsigned-longlong ,struct-return-arg 0))
                    :unsigned-doubleword)
                  (progn
                    (setq result `(%%get-unsigned-longlong ,struct-return-arg 0))
                    :unsigned-doubleword)))
              (foreign-type-to-representation-type return-type)))
           (offset -8))
      `(setf (,
              (case return-type-keyword
                (:address '%get-ptr)
                (:signed-doubleword '%%get-signed-longlong)
                (:unsigned-doubleword '%%get-unsigned-longlong)
                (:double-float '%get-double-float)
                (:single-float '%get-single-float)
                (t '%get-long)) ,stack-ptr ,offset) ,result))))
