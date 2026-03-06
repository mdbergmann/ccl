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
  (require "NXENV")
  (require "ARM64ENV")
  (unless (boundp 'platform-cpu-arm64)
    (defconstant platform-cpu-arm64 (ash 4 3))))

(next-nx-defops)
(defvar *arm642-specials* nil)
(let* ((newsize (%i+ (next-nx-num-ops) 10))
       (old *arm642-specials*)
       (oldsize (length old)))
  (declare (fixnum newsize oldsize))
  (unless (>= oldsize newsize)
    (let* ((v (make-array newsize :initial-element nil)))
      (dotimes (i oldsize (setq *arm642-specials* v))
        (setf (svref v i) (svref old i))))))

;;; Stub subprimitive lookup for ARM64 (mirrors arm::arm-subprimitive-offset)
(defun arm64::arm64-subprimitive-offset (x)
  (if (and x (or (symbolp x) (stringp x)))
    (let* ((info (find x arm64::*arm64-subprims* :test #'string-equal :key #'subprimitive-info-name)))
      (when info
        (subprimitive-info-offset info)))))

;;; Stub vinsn instruction simplifier for ARM64.
;;; This will be fleshed out when the full instruction encoding is implemented.
(defun arm64::vinsn-simplify-instruction (form vinsn-params)
  (declare (ignore vinsn-params))
  ;; For now, just return the form as-is.
  ;; A real implementation will encode instructions like arm::vinsn-simplify-instruction.
  form)

;;; This defines a template.  All expressions in the body must be
;;; evaluable at macroexpansion time.
(defun %define-arm64-vinsn (backend vinsn-name results args temps body)
  (let* ((arch-name (backend-target-arch-name backend))
	 (template-hash (backend-p2-template-hash-name backend))
	 (name-list ())
	 (attrs 0)
         (nhybrids 0)
         (local-labels ())
         (referenced-labels ())
	 (source-indicator (form-symbol arch-name "-VINSN"))
         (opcode-alist ()))
    (flet ((valid-spec-name (x)
	     (or (and (consp x)
		      (consp (cdr x))
		      (null (cddr x))
		      (atom (car x))
		      (or (assoc (cadr x) *vreg-specifier-constant-constraints* :test #'eq)
			  (assoc (cadr x) *spec-class-storage-class-alist* :test #'eq)
			  (eq (cadr x) :label)
			  (and (consp (cadr x))
			       (or
				(assoc (caadr x) *vreg-specifier-constant-constraints* :test #'eq)
				(assoc (caadr x) *spec-class-storage-class-alist* :test #'eq))))
		      (car x))
		 (error "Invalid vreg spec: ~s" x)))
           (add-spec-name (vname)
             (if (member vname name-list :test #'eq)
               (error "Duplicate name ~s in vinsn ~s" vname vinsn-name)
               (push vname name-list))))
      (declare (dynamic-extent #'valid-spec-name #'add-spec-name))
      (when (consp vinsn-name)
        (setq attrs (encode-vinsn-attributes (cdr vinsn-name))
              vinsn-name (car vinsn-name)))
      (unless (and (symbolp vinsn-name) (eq *CCL-PACKAGE* (symbol-package vinsn-name)))
        (setq vinsn-name (intern (string vinsn-name) *CCL-PACKAGE*)))
      ;; First, make sure that there are no duplicate
      ;; result names (and validate "results".)
      (do* ((res results tail)
            (tail (cdr res) (cdr tail)))
           ((null res))
        (let* ((name (valid-spec-name (car res))))
          (if (assoc name tail :test #'eq)
            (error "Duplicate result name ~s in ~s." name results))))
      (let* ((non-hybrid-results ())
             (match-args args))
        (dolist (res results)
          (let* ((res-name (car res)))
            (if (not (assoc res-name args :test #'eq))
              (if (not (= nhybrids 0))
                (error "result ~s should also name an argument. " res-name)
                (push res-name non-hybrid-results))
              (if (eq res-name (caar match-args))
                (setf nhybrids (1+ nhybrids)
                      match-args (cdr match-args))
                (error "~S - hybrid results should appear in same order as arguments." res-name))))))
      ;; Build name-list in vp order: results&args then temps.
      ;; results&args = results + (nthcdr nhybrids args).
      ;; This must match the vp layout from match-template-vregs.
      (dolist (n (append results (nthcdr nhybrids args) temps))
        (add-spec-name (valid-spec-name n)))
      (setq name-list (nreverse name-list))
      (let* ((k -1))
        (declare (fixnum k))
        (let* ((name-alist (mapcar #'(lambda (n) (cons n (list (incf k)))) name-list)))
          (flet ((find-name (n)
                   (let* ((pair (assoc n name-alist :test #'eq)))
                     (declare (list pair))
                     (if pair
                       (cdr pair)
                       (or (arm64::arm64-subprimitive-offset n)
                           (error "Unknown name ~s" n))))))
            (labels ((simplify-operand (op)
                       (if (atom op)
                         (if (typep op 'fixnum)
                           op
                           (if (constantp op)
                             (progn
                               (if (keywordp op)
                                 (pushnew op referenced-labels))
                               (eval op))
                             (find-name op)))
                         (if (eq (car op) :apply)
                           `(,(cadr op) ,@(mapcar #'simplify-operand (cddr op)))
                           (simplify-operand (eval op))))))
              (labels ((simplify-constraint (guard)
                         (destructuring-bind (guardname &rest others) guard
                           (ecase guardname
                             (:not
                              (destructuring-bind (negation) others
                                `(:not ,(simplify-constraint negation))))
                             (:pred
                              (destructuring-bind (predicate &rest operands) others
                                `(:pred ,predicate ,@(mapcar #'simplify-operand operands))))
                             ((:eq :lt :gt :type)
                              (destructuring-bind (vreg constant) others
                                (unless (constantp constant)
                                  (error "~S : not constant in constraint ~s ." constant guard))
                                `(,guardname ,(find-name vreg) ,(eval constant))))
                             ((:or :and)
                              (unless others (error "Missing constraint list in ~s ." guard))
                              `(,guardname ,(mapcar #'simplify-constraint others))))))
                       (simplify-form (form)
                         (if (atom form)
                           (progn
                             (if (keywordp form) (push form local-labels) )
                             form)
                           (destructuring-bind (&whole w opname &rest opvals) form
                             (declare (ignore w))
                             (if (consp opname)
                               (cons (simplify-constraint opname)
                                     (mapcar #'simplify-form opvals))
                               (if (keywordp opname)
                                 (ecase opname
                                   ((:code :data :lock-constant-pool :unlock-constant-pool)  form)
                                   (:word (destructuring-bind (val) opvals
                                            (list opname
                                                  (let* ((p (position val name-list)))
                                                    (if p (list p) (eval val)))))))
                                 (arm64::vinsn-simplify-instruction form name-list)))))))
                (let* ((template (make-vinsn-template
                                  :name vinsn-name
                                  :result-vreg-specs results
                                  :argument-vreg-specs args
                                  :temp-vreg-specs temps
                                  :nhybrids nhybrids
                                  :results&args (append results (nthcdr nhybrids args))
                                  :nvp (- (+ (length results) (length args) (length temps))
                                          nhybrids)
                                  :body (prog1 (mapcar #'simplify-form body)
                                          (dolist (ref referenced-labels)
                                            (unless (memq ref local-labels)
                                              (error
                                               "local label ~S was referenced but never defined in VINSN-TEMPLATE definition for ~s" ref vinsn-name))))
                                  :local-labels local-labels :attributes attrs :opcode-alist
                                  opcode-alist)))
                  `(progn (set-vinsn-template ',vinsn-name ,template
                           ,template-hash) (record-source-file ',vinsn-name ',source-indicator)
                    ',vinsn-name))))))))))



(defvar *arm64-vinsn-templates* (make-hash-table :test #'eq))



(defvar *known-arm64-backends* ())


#+(or darwinarm64-target (not arm64-target))
(defvar *darwinarm64-backend*
  (make-backend :lookup-opcode #'false
		:lookup-macro #'false
		:lap-opcodes #()
                :define-vinsn '%define-arm64-vinsn
                :platform-syscall-mask (logior platform-os-darwin platform-cpu-arm64)
		:p2-dispatch *arm642-specials*
		:p2-vinsn-templates *arm64-vinsn-templates*
		:p2-template-hash-name '*arm64-vinsn-templates*
		:p2-compile 'arm642-compile
		:target-specific-features
		'(:arm64 :arm64-target :darwin-target :darwinarm64-target :64-bit-target :little-endian-target)
		:target-fasl-pathname (make-pathname :type "da64fsl")
		:target-platform (logior platform-word-size-64
                                         platform-cpu-arm64
                                         platform-os-darwin)
		:target-os :darwinarm64
		:name :darwinarm64
		:target-arch-name :arm64
		:target-foreign-type-data nil
                :target-arch arm64::*arm64-target-arch*))


#+(or linuxarm64-target (not arm64-target))
(defvar *linuxarm64-backend*
  (make-backend :lookup-opcode #'false
		:lookup-macro #'false
		:lap-opcodes #()
                :define-vinsn '%define-arm64-vinsn
                :platform-syscall-mask (logior platform-os-linux platform-cpu-arm64)
		:p2-dispatch *arm642-specials*
		:p2-vinsn-templates *arm64-vinsn-templates*
		:p2-template-hash-name '*arm64-vinsn-templates*
		:p2-compile 'arm642-compile
		:target-specific-features
		'(:arm64 :arm64-target :linux-target :linuxarm64-target :64-bit-target :little-endian-target)
		:target-fasl-pathname (make-pathname :type "la64fsl")
		:target-platform (logior platform-word-size-64
                                         platform-cpu-arm64
                                         platform-os-linux)
		:target-os :linuxarm64
		:name :linuxarm64
		:target-arch-name :arm64
		:target-foreign-type-data nil
                :target-arch arm64::*arm64-target-arch*))


#+(or darwinarm64-target (not arm64-target))
(pushnew *darwinarm64-backend* *known-arm64-backends* :key #'backend-name)

#+(or linuxarm64-target (not arm64-target))
(pushnew *linuxarm64-backend* *known-arm64-backends* :key #'backend-name)

(defvar *arm64-backend* (car *known-arm64-backends*))

(defun fixup-arm64-backend ()
  (dolist (b *known-arm64-backends*)
    (setf (backend-p2-dispatch b) *arm642-specials*
	  (backend-p2-vinsn-templates b) *arm64-vinsn-templates*)
    (or (backend-lap-macros b) (setf (backend-lap-macros b)
                                     (make-hash-table :test #'equalp)))))



(fixup-arm64-backend)

#+arm64-target
(setq *host-backend* *arm64-backend* *target-backend* *arm64-backend*)

(defun setup-arm64-ftd (backend)
  (or (backend-target-foreign-type-data backend)
      (let* ((name (backend-name backend))
             (pkg-name (case name
                         (:darwinarm64 "ARM64-DARWIN")
                         (:linuxarm64 "ARM64-LINUX"))))
        (when pkg-name
          (or (find-package pkg-name) (make-package pkg-name :use '("COMMON-LISP"))))
        (let* ((ftd
              (case name
                (:darwinarm64
                 (make-ftd :interface-db-directory "ccl:darwin-arm64-headers;"
			   :interface-package-name "ARM64-DARWIN"
                           :attributes '(:bits-per-word  64
                                         :signed-char t
                                         :struct-by-value t
                                         :natural-alignment t
                                         :prepend-underscore t)
                           :ff-call-expand-function
                           (intern "EXPAND-FF-CALL" "ARM64-DARWIN")
			   :ff-call-struct-return-by-implicit-arg-function
                           (intern "RECORD-TYPE-RETURNS-STRUCTURE-AS-FIRST-ARG"
                                   "ARM64-DARWIN")
                           :callback-bindings-function
                           (intern "GENERATE-CALLBACK-BINDINGS" "ARM64-DARWIN")
                           :callback-return-value-function
                           (intern "GENERATE-CALLBACK-RETURN-VALUE" "ARM64-DARWIN")))
                (:linuxarm64
                 (make-ftd :interface-db-directory "ccl:arm64-headers;"
			   :interface-package-name "ARM64-LINUX"
                           :attributes '(:bits-per-word  64
                                         :signed-char nil
                                         :natural-alignment t
                                         :struct-by-value t)
                           :ff-call-expand-function
                           (intern "EXPAND-FF-CALL" "ARM64-LINUX")
			   :ff-call-struct-return-by-implicit-arg-function
                           (intern "RECORD-TYPE-RETURNS-STRUCTURE-AS-FIRST-ARG"
                                   "ARM64-LINUX")
                           :callback-bindings-function
                           (intern "GENERATE-CALLBACK-BINDINGS" "ARM64-LINUX")
                           :callback-return-value-function
                           (intern "GENERATE-CALLBACK-RETURN-VALUE" "ARM64-LINUX"))))))
          (install-standard-foreign-types ftd)
          (use-interface-dir :libc ftd)
          (setf (backend-target-foreign-type-data backend) ftd)))))

#-arm64-target
(setup-arm64-ftd *arm64-backend*)

(pushnew *arm64-backend* *known-backends* :key #'backend-name)
#-arm64-target
(progn
  #+(or darwinarm64-target (not arm64-target))
  (progn
    (setup-arm64-ftd *darwinarm64-backend*)
    (pushnew *darwinarm64-backend* *known-backends* :key #'backend-name))
  #+(or linuxarm64-target (not arm64-target))
  (progn
    (setup-arm64-ftd *linuxarm64-backend*)
    (pushnew *linuxarm64-backend* *known-backends* :key #'backend-name)))


;;; AAPCS64 FFI stubs.
;;; These will be fleshed out when the full compiler is working.

(defun arm64::aapcs64-record-type-returns-structure-as-first-arg (rtype)
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

(defun arm64::aapcs64-expand-ff-call (callform args &key (arg-coerce #'null-coerce-foreign-arg) (result-coerce #'null-coerce-foreign-result))
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
          (if (arm64::aapcs64-record-type-returns-structure-as-first-arg result-type)
            (progn
              (setq result-type *void-foreign-type*
                    result-type-spec :void)
              (argforms :address)
              (argforms result-form))
            (progn
              (setq result-type (parse-foreign-type :unsigned-doubleword)
                    result-type-spec :unsigned-doubleword
                    enclosing-form `(setf (%%get-unsigned-longlong ,result-form 0))))))
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
                  (progn
                    (argforms :address)
                    (argforms arg-value-form))
                  (progn
                    (argforms (foreign-type-to-representation-type ftype))
                    (argforms (funcall arg-coerce arg-type-spec arg-value-form))))))))
        (argforms (foreign-type-to-representation-type result-type))
        (let* ((call (funcall result-coerce result-type-spec `(,@callform ,@(argforms)))))
          (if enclosing-form
            `(,@enclosing-form ,call)
            call))))))

(defun arm64::aapcs64-generate-callback-bindings (stack-ptr fp-args-ptr argvars argspecs result-spec struct-result-name)
  (declare (ignore fp-args-ptr))
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
      (let* ((offset 0)
             (nextoffset offset))
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
                    `(,(cond
                        ((typep argtype 'foreign-single-float-type)
                         (setq nextoffset (+ offset 8))
                         '%get-single-float)
                        ((typep argtype 'foreign-double-float-type)
                         (setq nextoffset (+ offset 8))
                         '%get-double-float)
                        ((and (typep argtype 'foreign-integer-type)
                              (= (foreign-integer-type-bits argtype) 64)
                              (foreign-integer-type-signed argtype))
                         (setq nextoffset (+ offset 8))
                         '%%get-signed-longlong)
                        ((and (typep argtype 'foreign-integer-type)
                              (= (foreign-integer-type-bits argtype) 64)
                              (not (foreign-integer-type-signed argtype)))
                         (setq nextoffset (+ offset 8))
                         '%%get-unsigned-longlong)
                        (t
                         (setq nextoffset (+ offset 8))
                         (cond ((typep argtype 'foreign-pointer-type) '%get-ptr)
                               ((typep argtype 'foreign-integer-type)
                                (let* ((bits (foreign-integer-type-bits argtype))
                                       (signed (foreign-integer-type-signed argtype)))
                                  (cond ((<= bits 8)
                                         (if signed
                                           '%get-signed-byte
                                           '%get-unsigned-byte))
                                        ((<= bits 16)
                                         (if signed
                                           '%get-signed-word
                                           '%get-unsigned-word))
                                        ((<= bits 32)
                                         (if signed
                                           '%get-signed-long
                                           '%get-unsigned-long))
                                        (t
                                         (error "Don't know how to access foreign argument of type ~s" (unparse-foreign-type argtype))))))
                               (t
                                (error "Don't know how to access foreign argument of type ~s" (unparse-foreign-type argtype))))))
                      ,stack-ptr
                      ,offset)))
              (when name (lets (list name access-form)))
              (setq offset nextoffset))))))))

(defun arm64::aapcs64-generate-callback-return-value (stack-ptr fp-args-ptr result return-type struct-return-arg)
  (declare (ignore fp-args-ptr))
  (unless (eq return-type *void-foreign-type*)
    (let* ((return-type-keyword
            (if (typep return-type 'foreign-record-type)
              (progn
                (setq result `(%%get-unsigned-longlong ,struct-return-arg 0))
                :unsigned-doubleword)
              (foreign-type-to-representation-type return-type)))
           (offset -8))
      `(setf (,
              (case return-type-keyword
                (:address '%get-ptr)
                (:signed-doubleword '%%get-signed-longlong)
                (:unsigned-doubleword '%%get-unsigned-longlong)
                (:double-float '%get-double-float)
                (:single-float '%get-single-float)
                (:unsigned-fullword '%get-unsigned-long)
                (t '%get-long)) ,stack-ptr ,offset) ,result))))

#+arm64-target
(require "ARM64-VINSNS")
