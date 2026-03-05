;;-*-Mode: LISP; Package: CCL -*-
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

;;; ARM64 code generator — translates acode (compiler IR) into vinsns.
;;; Adapted from compiler/ARM/arm2.lisp for AArch64 with TBI tagging.

(in-package "CCL")

(eval-when (:compile-toplevel :execute)
  (require "NXENV")
  (require "ARM64ENV"))

(eval-when (:load-toplevel :execute :compile-toplevel)
  (require "ARM64-BACKEND"))

(defparameter *arm642-debug-mask* 0)
(defconstant arm642-debug-verbose-bit 0)
(defconstant arm642-debug-vinsns-bit 1)
(defparameter *arm642-target-node-size* 0)
(defparameter *arm642-target-fixnum-shift* 0)
(defparameter *arm642-target-node-shift* 0)
(defparameter *arm642-target-bits-in-word* 0)
(defparameter *arm642-half-fixnum-type* '(signed-byte 55))
(defparameter *arm642-target-half-fixnum-type* nil)
(defparameter *arm642-operator-supports-u8-target* ())
;;; No constant pool on ARM64 — autodrain removed
(defparameter *arm642-nfp-depth* 0)
(defparameter *arm642-max-nfp-depth* ())
(defparameter *arm642-all-nfp-pushes* ())
(defparameter *arm642-nfp-vars* ())

(defun arm642-max-nfp-depth ()
  (or *arm642-max-nfp-depth*
      (setq *arm642-max-nfp-depth*
            (let* ((max 0))
              (declare (fixnum max))
              (dolist (v *arm642-all-nfp-pushes* max)
                (when (and v (vinsn-succ v))    ;not elided
                  (let* ((depth (+ (the fixnum (svref (vinsn-variable-parts v) 1))
                                   (if (vinsn-attribute-p v :uses-frame-pointer)
                                     16
                                     8))))
                    (declare (fixnum depth))
                    (if (> depth max)
                      (setq max depth)))))))))


(defmacro with-arm642-p2-declarations (declsform &body body)
  `(let* ((*arm642-tail-allow* *arm642-tail-allow*)
          (*arm642-reckless* *arm642-reckless*)
          (*arm642-open-code-inline* *arm642-open-code-inline*)
          (*arm642-trust-declarations* *arm642-trust-declarations*)
          (*arm642-full-safety* *arm642-full-safety*)
          (*arm642-float-safety* *arm642-float-safety*))
     (arm642-decls ,declsform)
     ,@body))


(defun arm642-emit-vinsn (vlist name vinsn-table &rest vregs)
  (arm642-update-regmap (apply #'%emit-vinsn vlist name vinsn-table vregs)))

(defmacro with-arm64-local-vinsn-macros ((segvar &optional vreg-var xfer-var) &body body)
  (declare (ignorable xfer-var))
  (let* ((template-name-var (gensym))
         (template-temp (gensym))
         (args-var (gensym))
         (labelnum-var (gensym))
         (retvreg-var (gensym))
         (label-var (gensym)))
    `(macrolet ((! (,template-name-var &rest ,args-var)
                  (let* ((,template-temp (get-vinsn-template-cell ,template-name-var (backend-p2-vinsn-templates *target-backend*))))
                    (unless ,template-temp
                      (warn "VINSN \"~A\" not defined" ,template-name-var))
                    `(arm642-emit-vinsn ,',segvar ',,template-name-var (backend-p2-vinsn-templates *target-backend*) ,@,args-var))))
       (macrolet ((<- (,retvreg-var)
                    `(arm642-copy-register ,',segvar ,',vreg-var ,,retvreg-var))
                  (@  (,labelnum-var)
                    `(progn
                      (arm642-invalidate-regmap)
                      (backend-gen-label ,',segvar ,,labelnum-var)))
                  (@+ (,labelnum-var)
                    `(progn             ;keep regmap
                      (backend-gen-label ,',segvar ,,labelnum-var)))
                  (-> (,label-var)
                    `(! jump (aref *backend-labels* ,,label-var)))
                  (^ (&rest branch-args)
                    `(arm642-branch ,',segvar ,',xfer-var ,',vreg-var ,@branch-args))
                  (? (&key (class :gpr)
                          (mode :lisp))
                   (let* ((class-val
                           (ecase class
                             (:gpr hard-reg-class-gpr)
                             (:fpr hard-reg-class-fpr)
                             (:crf hard-reg-class-crf)))
                          (mode-val
                           (if (eq class :gpr)
                             (gpr-mode-name-value mode)
                             (if (eq class :fpr)
                               (if (eq mode :single-float)
                                 hard-reg-class-fpr-mode-single
                                 hard-reg-class-fpr-mode-double)
                               0))))
                     `(make-unwired-lreg nil
                       :class ,class-val
                       :mode ,mode-val)))
                  ($ (reg &key (class :gpr) (mode :lisp))
                   (let* ((class-val
                           (ecase class
                             (:gpr hard-reg-class-gpr)
                             (:fpr hard-reg-class-fpr)
                             (:crf hard-reg-class-crf)))
                          (mode-val
                           (if (eq class :gpr)
                             (gpr-mode-name-value mode)
                             (if (eq class :fpr)
                               (if (eq mode :single-float)
                                 hard-reg-class-fpr-mode-single
                                 hard-reg-class-fpr-mode-double)
                               0))))
                     `(make-wired-lreg ,reg
                       :class ,class-val
                       :mode ,mode-val))))
         ,@body))))


(defvar *arm64-current-context-annotation* nil)
(defvar *arm642-woi* nil)
(defvar *arm642-open-code-inline* nil)
(defvar *arm642-optimize-for-space* nil)
(defvar *arm642-register-restore-count* 0)
(defvar *arm642-register-restore-ea* nil)
(defvar *arm642-non-volatile-fpr-count* 0)
(defvar *arm642-compiler-register-save-note* nil)

(defparameter *arm642-tail-call-aliases*
  ()
  #| '((%call-next-method . (%tail-call-next-method . 1))) |#
)


(defvar *arm642-icode* nil)
(defvar *arm642-undo-stack* nil)
(defvar *arm642-undo-because* nil)


(defvar *arm642-cur-afunc* nil)
(defvar *arm642-vstack* 0)
(defvar *arm642-cstack* 0)
(defvar *arm642-undo-count* 0)
(defvar *arm642-returning-values* nil)
(defvar *arm642-vcells* nil)
(defvar *arm642-fcells* nil)
(defvar *arm642-entry-vsp-saved-p* nil)

(defvar *arm642-entry-label* nil)
(defvar *arm642-fixed-args-label* nil)
(defvar *arm642-fixed-args-tail-label* nil)
(defvar *arm642-fixed-nargs* nil)
(defvar *arm642-tail-allow* t)
(defvar *arm642-reckless* nil)
(defvar *arm642-full-safety* nil)
(defvar *arm642-float-safety* nil)
(defvar *arm642-trust-declarations* nil)
(defvar *arm642-entry-vstack* nil)
(defvar *arm642-need-nargs* t)

(defparameter *arm642-inhibit-register-allocation* nil)
(defvar *arm642-record-symbols* nil)
(defvar *arm642-recorded-symbols* nil)
(defvar *arm642-emitted-source-notes* nil)

(defvar *arm642-result-reg* arm64::arg_z)
(defparameter *arm642-nvrs* nil)
(defparameter *arm642-first-nvr* -1)

(defvar *arm642-gpr-locations* nil)
(defvar *arm642-gpr-locations-valid-mask* 0)
(defvar *arm642-gpr-constants* nil)
(defvar *arm642-gpr-constants-valid-mask* 0)


(declaim (fixnum *arm642-vstack* *arm642-cstack*))


;;; ======================================================================
;;; Chunk 2: Core infrastructure functions
;;; ======================================================================

(defun arm642-gprs-containing-constant (c)
  (let* ((in *arm642-gpr-constants-valid-mask*)
         (vals *arm642-gpr-constants*)
         (out 0))
    (declare (fixnum in out) (simple-vector vals))
    (dotimes (i 32 out)
      (declare (type (mod 32) i))
      (when (and (logbitp i in)
                 (eql c (svref vals i)))
        (setq out (logior out (ash 1 i)))))))

(defun arm642-nfp-ref (seg vreg ea)
  (with-arm64-local-vinsn-macros (seg vreg)
    (let* ((offset (logand #xfff8 ea))
           (type (logand #x7 ea))
           (vreg-class (hard-regspec-class vreg))
           (vreg-mode (get-regspec-mode vreg))
           (nested (> *arm642-undo-count* 0))
           (vinsn nil)
           (reg vreg))
      (ecase type
        (#. memspec-nfp-type-natural
            (unless (and (eql vreg-class hard-reg-class-gpr)
                         (eql vreg-mode hard-reg-class-gpr-mode-u32))
              (setq reg (available-imm-temp
                         *available-backend-imm-temps*
                         :u32)))
            (setq vinsn
                  (if nested
                    (! nfp-load-unboxed-word-nested reg offset)
                    (! nfp-load-unboxed-word reg offset))))
        (#. memspec-nfp-type-double-float
            (unless (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-double))
              (setq reg (available-fp-temp
                         *available-backend-fp-temps*
                         :double-float)))
            (setq vinsn
                  (if nested
                    (! nfp-load-double-float-nested reg offset)
                    (! nfp-load-double-float reg offset))))
        (#. memspec-nfp-type-single-float
            (unless (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-single))
              (setq reg (available-fp-temp
                         *available-backend-fp-temps*
                         :single-float)))
            (setq vinsn
                  (if nested
                    (! nfp-load-single-float-nested reg offset)
                    (! nfp-load-single-float  reg offset))))
        (#. memspec-nfp-type-complex-double-float
            (unless (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-complex-double-float))
              (setq reg (available-fp-temp
                         *available-backend-fp-temps*
                         :complex-double-float)))
            (setq vinsn
                  (if nested
                    (! nfp-load-complex-double-float-nested reg offset)
                    (! nfp-load-complex-double-float reg offset))))
        (#. memspec-nfp-type-complex-single-float
            (unless (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-complex-single-float))
              (setq reg (available-fp-temp
                         *available-backend-fp-temps*
                         :complex-single-float)))
            (setq vinsn
                  (if nested
                    (! nfp-load-complex-single-float-nested reg offset)
                    (! nfp-load-complex-single-float  reg offset)))))
      (when (memspec-single-ref-p ea)
        (let* ((push-vinsn
                (find offset *arm642-all-nfp-pushes*
                      :key (lambda (v)
                             (when (typep v 'vinsn)
                               (svref (vinsn-variable-parts v) 1))))))
          (when push-vinsn
            (arm642-elide-pushes seg push-vinsn vinsn))))
      (<- reg))))

(defun arm642-reg-for-nfp-set (vreg ea)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((type (logand #x7 ea))
           (vreg-class (if vreg (hard-regspec-class vreg)))
           (vreg-mode (if vreg (get-regspec-mode vreg))))
      (ecase type
        (#. memspec-nfp-type-natural
            (if (and (eql vreg-class hard-reg-class-gpr)
                     (eql vreg-mode hard-reg-class-gpr-mode-u32))
              vreg
              (make-unwired-lreg
               (available-imm-temp *available-backend-imm-temps* :u32))))
        (#. memspec-nfp-type-double-float
            (if (and (eql vreg-class hard-reg-class-fpr)
                     (eql vreg-mode hard-reg-class-fpr-mode-double))
              vreg
              (make-unwired-lreg
               (available-fp-temp *available-backend-fp-temps* :double-float))))
        (#. memspec-nfp-type-single-float
            (if (and (eql vreg-class hard-reg-class-fpr)
                     (eql vreg-mode hard-reg-class-fpr-mode-single))
              vreg
              (make-unwired-lreg
               (available-fp-temp *available-backend-fp-temps* :single-float))))
        (#. memspec-nfp-type-complex-double-float
            (if (and (eql vreg-class hard-reg-class-fpr)
                     (eql vreg-mode hard-reg-class-fpr-mode-complex-double-float))
              vreg
              (make-unwired-lreg
               (available-fp-temp *available-backend-fp-temps* :complex-double-float))))
        (#. memspec-nfp-type-complex-single-float
            (if (and (eql vreg-class hard-reg-class-fpr)
                     (eql vreg-mode hard-reg-class-fpr-mode-complex-single-float))
              vreg
              (make-unwired-lreg
               (available-fp-temp *available-backend-fp-temps* :complex-single-float))))))))

(defun arm642-nfp-set (seg reg ea)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((offset (logand #xfff8 ea))
           (nested (> *arm642-undo-count* 0)))
      (ecase (logand #x7 ea)
        (#. memspec-nfp-type-natural
            (if nested
              (! nfp-store-unboxed-word-nested reg offset)
              (! nfp-store-unboxed-word reg offset)))
        (#. memspec-nfp-type-double-float
            (if nested
              (! nfp-store-double-float-nested reg offset)
              (! nfp-store-double-float reg offset)))
        (#. memspec-nfp-type-single-float
            (if nested
              (! nfp-store-single-float-nested reg offset)
              (! nfp-store-single-float  reg offset)))
        (#. memspec-nfp-type-complex-double-float
            (if nested
              (! nfp-store-complex-double-float-nested reg offset)
              (! nfp-store-complex-double-float reg offset)))
        (#. memspec-nfp-type-complex-single-float
            (if nested
              (! nfp-store-complex-single-float-nested reg offset)
              (! nfp-store-complex-single-float  reg offset)))))))

;;; Depending on the variable's type and other attributes, maybe
;;; push it on the NFP.  Return the nfp-relative EA if we push it.
(defun arm642-nfp-bind (seg var initform)
  (let* ((bits (nx-var-bits var)))
    (unless (logtest bits (logior (ash 1 $vbitspecial)
                                  (ash 1 $vbitclosed)
                                  (ash 1 $vbitdynamicextent)))
      (let* ((type (acode-var-type var *arm642-trust-declarations*))
             (reg nil)
             (nfp-bits 0))
        (cond ((and (subtypep type '(unsigned-byte 32))
                    NIL
                    (not (subtypep type '(signed-byte 30))))
               (setq reg (available-imm-temp
                          *available-backend-imm-temps* :u32)
                     nfp-bits memspec-nfp-type-natural))
              ((subtypep type 'single-float)
               (setq reg (available-fp-temp *available-backend-fp-temps*
                                            :single-float)
                     nfp-bits memspec-nfp-type-single-float))
              ((subtypep type 'double-float)
               (setq reg (available-fp-temp *available-backend-fp-temps*
                                            :double-float)
                     nfp-bits memspec-nfp-type-double-float))
              ((subtypep type 'complex-single-float)
               (setq reg (available-fp-temp *available-backend-fp-temps*
                                            :complex-single-float)
                     nfp-bits memspec-nfp-type-complex-single-float))
              ((subtypep type 'complex-double-float)
               (setq reg (available-fp-temp *available-backend-fp-temps*
                                            :complex-double-float)
                     nfp-bits memspec-nfp-type-complex-double-float)))
        (when reg
          (let* ((vinsn (arm642-push-register
                         seg
                         (arm642-one-untargeted-reg-form seg initform reg))))
            (when vinsn
              (push (cons vinsn var) *arm642-nfp-vars*)
              (make-nfp-address
               (svref (vinsn-variable-parts vinsn) 1)
               nfp-bits))))))))


(defun arm642-do-lexical-reference (seg vreg ea)
  (when vreg
    (with-arm64-local-vinsn-macros (seg vreg)
      (if (memory-spec-p ea)
        (if (eql (memspec-type ea) memspec-nfp-offset)
          (arm642-nfp-ref seg vreg ea)
          (ensuring-node-target (target vreg)
            (let* ((reg (unless (node-reg-p vreg)
                          (or (arm642-reg-for-ea ea)
                              (arm642-try-non-conflicting-reg target 0)))))
              (when reg (setq target reg))
              (arm642-stack-to-register seg ea target)
              (if (addrspec-vcell-p ea)
                (! vcell-ref target target)))))
        (<- ea)))))

(defun arm642-do-lexical-setq (seg vreg ea valreg)
  (with-arm64-local-vinsn-macros (seg vreg)
    (cond ((typep ea 'lreg)
            (arm642-copy-register seg ea valreg))
          ((addrspec-vcell-p ea)     ; closed-over vcell
           (arm642-copy-register seg arm64::arg_z valreg)
           (arm642-stack-to-register seg ea arm64::arg_x)
           (arm642-lri seg arm64::arg_y 0)
           (! call-subprim-3 arm64::arg_z (arm64::arm64-subprimitive-offset  '.SPgvset) arm64::arg_x arm64::arg_y arm64::arg_z)
           (setq valreg arm64::arg_z))
          ((memory-spec-p ea)    ; vstack slot or fp offset
           (arm642-register-to-stack seg valreg ea))
          (t
           (arm642-copy-register seg ea valreg)))
    (when vreg
      (<- valreg))))

;;; ensure that next-method-var is heap-consed (if it's closed over.)
(defun arm642-heap-cons-next-method-var (seg var)
  (with-arm64-local-vinsn-macros (seg)
    (when (eq (ash 1 $vbitclosed)
              (logand (logior (ash 1 $vbitclosed)
                              (ash 1 $vbitcloseddownward))
                      (the fixnum (nx-var-bits var))))
      (let* ((ea (var-ea var))
             (arg ($ arm64::arg_z))
             (result ($ arm64::arg_z)))
        (arm642-do-lexical-reference seg arg ea)
        (arm642-set-nargs seg 1)
        (let ((idx (backend-immediate-index (arm642-symbol-entry-locative '%cons-magic-next-method-arg))))
          (if (< (+ arm64::misc-data-offset (ash (+ idx 2) arm64::word-shift)) 32768)
            (! ref-constant ($ arm64::fname) idx)
            (with-imm-target () (idxreg :s64)
              (arm642-lri seg idxreg (+ arm64::misc-data-offset (ash (+ idx 2) arm64::word-shift)))
              (! ref-indexed-constant ($ arm64::fname) idxreg))))
        (! call-known-symbol arg)
        (arm642-do-lexical-setq seg nil ea result)))))


(defun acode-condition-to-arm64-cr-bit (cond)
  (condition-to-arm64-cr-bit (car (acode-operands cond))))

(defun condition-to-arm64-cr-bit (cond)
  (case cond
    (:EQ (values arm64::arm64-cond-eq t))
    (:NE (values arm64::arm64-cond-eq nil))
    (:GT (values arm64::arm64-cond-gt t))
    (:LE (values arm64::arm64-cond-gt nil))
    (:LT (values arm64::arm64-cond-lt t))
    (:GE (values arm64::arm64-cond-lt nil))))


(defun arm64-cr-bit-to-arm64-unsigned-cr-bit (cr-bit)
  (case cr-bit
    (#.arm64::arm64-cond-eq arm64::arm64-cond-eq)
    (#.arm64::arm64-cond-ne arm64::arm64-cond-ne)
    (#.arm64::arm64-cond-gt arm64::arm64-cond-hi)
    (#.arm64::arm64-cond-le arm64::arm64-cond-ls)
    (#.arm64::arm64-cond-lt arm64::arm64-cond-lo)
    (#.arm64::arm64-cond-ge arm64::arm64-cond-hs)))

;;; If we have to change the order of operands in a comparison, we
;;; generally need to change the condition we're testing.
(defun arm642-cr-bit-for-reversed-comparison (cr-bit)
  (ecase cr-bit
    (#.arm64::arm64-cond-eq arm64::arm64-cond-eq)
    (#.arm64::arm64-cond-ne arm64::arm64-cond-ne)
    (#.arm64::arm64-cond-lt arm64::arm64-cond-gt)
    (#.arm64::arm64-cond-le arm64::arm64-cond-ge)
    (#.arm64::arm64-cond-gt arm64::arm64-cond-lt)
    (#.arm64::arm64-cond-ge arm64::arm64-cond-le)
    (#.arm64::arm64-cond-lo arm64::arm64-cond-hi)
    (#.arm64::arm64-cond-ls arm64::arm64-cond-hs)
    (#.arm64::arm64-cond-hi arm64::arm64-cond-lo)
    (#.arm64::arm64-cond-hs arm64::arm64-cond-ls)))


(defun arm642-ensure-binding-indices-for-vcells (vcells)
  (dolist (cell vcells)
    (ensure-binding-index (car cell)))
  vcells)

(defun arm642-compile (afunc &optional lambda-form *arm642-record-symbols*)
  (progn
    (dolist (a  (afunc-inner-functions afunc))
      (unless (afunc-lfun a)
        (arm642-compile a
                        (if lambda-form
                          (afunc-lambdaform a))
                        *arm642-record-symbols*))) ; always compile inner guys
    (let* ((*arm642-cur-afunc* afunc)
           (*arm642-returning-values* nil)
           (*arm64-current-context-annotation* nil)
           (*arm642-woi* nil)
           (*encoded-reg-value-byte* (byte 5 0))
           (*arm642-open-code-inline* nil)
           (*arm642-optimize-for-space* nil)
           (*arm642-register-restore-count* nil)
           (*arm642-compiler-register-save-note* nil)
           (*arm642-non-volatile-fpr-count* 0)
           (*arm642-register-restore-ea* nil)
           (*arm642-vstack* 0)
           (*arm642-cstack* 0)
           (*arm642-target-fixnum-shift* (arch::target-fixnum-shift (backend-target-arch *target-backend*)))
           (*arm642-target-node-shift* (arch::target-word-shift  (backend-target-arch *target-backend*)))
           (*arm642-target-bits-in-word* (arch::target-nbits-in-word (backend-target-arch *target-backend*)))
           (*arm642-target-node-size* (arch::target-lisp-node-size (backend-target-arch *target-backend*)))
           (*arm642-target-half-fixnum-type* *arm642-half-fixnum-type*)
           (*backend-vinsns* (backend-p2-vinsn-templates *target-backend*))
           (*backend-node-regs* arm64-node-regs)
           (*backend-node-temps* arm64-temp-node-regs)
           (*available-backend-node-temps* arm64-temp-node-regs)
           (*backend-imm-temps* arm64-imm-regs)
           (*available-backend-imm-temps* arm64-imm-regs)
           (*backend-fp-temps* arm64-temp-fp-regs)
           (*available-backend-fp-temps* arm64-temp-fp-regs)
           (*backend-crf-temps* arm64-cr-fields)
           (*available-backend-crf-temps* arm64-cr-fields)
           (bits 0)
           (*logical-register-counter* -1)
           (*arm642-undo-count* 0)
           (*backend-labels* (arm642-make-stack 64 target::subtag-simple-vector))
           (*arm642-undo-stack* (arm642-make-stack 64  target::subtag-simple-vector))
           (*arm642-undo-because* (arm642-make-stack 64))
           (*backend-immediates* (arm642-make-stack 64  target::subtag-simple-vector))
           (*arm642-entry-label* nil)
           (*arm642-fixed-args-label* nil)
           (*arm642-fixed-args-tail-label*)
           (*arm642-fixed-nargs* nil)
           (*arm642-inhibit-register-allocation* nil)
           (*arm642-tail-allow* t)
           (*arm642-reckless* nil)
           (*arm642-full-safety* nil)
           (*arm642-float-safety* nil)
           (*arm642-trust-declarations* t)
           (*arm642-entry-vstack* nil)
           (*arm642-need-nargs* t)
           (fname (afunc-name afunc))
           (*arm642-entry-vsp-saved-p* nil)
           (*arm642-vcells* (arm642-ensure-binding-indices-for-vcells (afunc-vcells afunc)))
           (*arm642-fcells* (afunc-fcells afunc))
           *arm642-recorded-symbols*
           (*arm642-emitted-source-notes* '())
           (*arm642-gpr-locations-valid-mask* 0)
           (*arm642-gpr-locations* (make-array 32 :initial-element nil))
           (*arm642-gpr-constants-valid-mask* 0)
           (*arm642-gpr-constants* (make-array 32 :initial-element nil))
           (*arm642-nfp-depth* 0)
           (*arm642-max-nfp-depth* ())
           (*arm642-all-nfp-pushes* ())
           (*arm642-nfp-vars* ()))
      (declare (dynamic-extent *arm642-gpr-locations* *arm642-gpr-constants*))
      (set-fill-pointer
       *backend-labels*
       (set-fill-pointer
        *arm642-undo-stack*
        (set-fill-pointer
         *arm642-undo-because*
         (set-fill-pointer
          *backend-immediates* 0))))
      (backend-get-next-label)          ; start @ label 1, 0 is confused with NIL in compound cd
      (let* ((vinsns (make-vinsn-list))
             (*vinsn-list* vinsns))
        (unwind-protect
             (progn
               (setq bits (arm642-toplevel-form vinsns (make-wired-lreg *arm642-result-reg*) $backend-return (afunc-acode afunc)))
               (dotimes (i (length *backend-immediates*))
                 (let ((imm (aref *backend-immediates* i)))
                   (when (arm642-symbol-locative-p imm) (aset *backend-immediates* i (car imm)))))
               (optimize-vinsns vinsns)
               (when (logbitp arm642-debug-vinsns-bit *arm642-debug-mask*)
                 (format t "~% vinsns for ~s (after generation)" (afunc-name afunc))
                 (do-dll-nodes (v vinsns) (format t "~&~s" v))
                 (format t "~%~%"))

               ;;; ARM64: no constant pool, single code section
               (with-dll-node-freelist (code arm64::*lap-instruction-freelist*)
                 (let* ((arm64::*lap-labels* nil)
                        (sections (vector code))
                        debug-info)
                   (declare (dynamic-extent sections))
                   (arm642-expand-vinsns vinsns code sections)
                   (if (logbitp $fbitnonnullenv (the fixnum (afunc-bits afunc)))
                     (setq bits (+ bits (ash 1 $lfbits-nonnullenv-bit))))
                   (setq debug-info (afunc-lfun-info afunc))
                   (when lambda-form
                     (setq debug-info (list* 'function-lambda-expression lambda-form debug-info)))
                   (when *arm642-recorded-symbols*
                     (setq debug-info (list* 'function-symbol-map *arm642-recorded-symbols* debug-info)))
                   (when (and (getf debug-info '%function-source-note) *arm642-emitted-source-notes*)
                     (setq debug-info (list* 'pc-source-map *arm642-emitted-source-notes* debug-info)))
                   (when debug-info
                     (setq bits (logior (ash 1 $lfbits-info-bit) bits))
                     (backend-new-immediate debug-info))
                   (if (or fname lambda-form *arm642-recorded-symbols*)
                     (backend-new-immediate fname)
                     (setq bits (logior (ash -1 $lfbits-noname-bit) bits)))

                   (unless (afunc-parent afunc)
                     (arm642-fixup-fwd-refs afunc))
                   (setf (afunc-all-vars afunc) nil)
                   (setf (afunc-argsword afunc) bits)
                   (setf (afunc-lfun afunc)
                         (arm642-xmake-function
                          code
                          *backend-immediates*
                          bits))
                   (when (getf debug-info 'pc-source-map)
                     (setf (getf debug-info 'pc-source-map) (arm642-generate-pc-source-map debug-info)))
                   (when (getf debug-info 'function-symbol-map)
                     (setf (getf debug-info 'function-symbol-map) (arm642-digest-symbols)))))))))
    afunc))

;;; ARM64: no constant pool, no data section
(defun arm642-xmake-function (code imms bits)
  (collect ((lap-imms))
    (dotimes (i (length imms))
      (lap-imms (cons (aref imms i) i)))
    (let* ((arm64::*arm64-constants* (lap-imms)))
      (arm64-lap-generate-code code
                               (arm64::arm64-finalize code)
                               bits))))



(defun arm642-make-stack (size &optional (subtype target::subtag-s16-vector))
  (make-uarray-1 subtype size t 0 nil nil nil nil t nil))

(defun arm642-fixup-fwd-refs (afunc)
  (dolist (f (afunc-inner-functions afunc))
    (arm642-fixup-fwd-refs f))
  (let ((fwd-refs (afunc-fwd-refs afunc)))
    (when fwd-refs
      (let* ((v (afunc-lfun afunc))
             (vlen (uvsize v)))
        (declare (fixnum vlen))
        (dolist (ref fwd-refs)
          (let* ((ref-fun (afunc-lfun ref)))
            (do* ((i 1 (1+ i)))
                 ((= i vlen))
              (declare (fixnum i))
              (if (eq (%svref v i) ref)
                (setf (%svref v i) ref-fun)))))))))

(eval-when (:compile-toplevel)
  (declaim (inline arm642-invalidate-regmap)))

(defun arm642-invalidate-regmap ()
  (setq *arm642-gpr-locations-valid-mask* 0
        *arm642-gpr-constants-valid-mask* 0))


(defun arm642-update-regmap (vinsn)
  (if (vinsn-attribute-p vinsn :call)
    (arm642-invalidate-regmap)
    (let* ((clobbered-regs (vinsn-gprs-set vinsn)))
      (setq *arm642-gpr-locations-valid-mask* (logandc2 *arm642-gpr-locations-valid-mask* clobbered-regs)
            *arm642-gpr-constants-valid-mask* (logandc2 *arm642-gpr-constants-valid-mask* clobbered-regs))))
  vinsn)

(defun arm642-invalidate-regmap-entry (i loc)
  (when (and (logbitp i *arm642-gpr-locations-valid-mask*)
             (memq loc (svref *arm642-gpr-locations* i)))
    (when (null (setf (svref *arm642-gpr-locations* i)
                      (delete loc (svref *arm642-gpr-locations* i))))
      (setq *arm642-gpr-locations-valid-mask* (logandc2 *arm642-gpr-locations-valid-mask* (ash 1 i))))))

(defun arm642-regmap-note-store (gpr loc)
  (let* ((gpr (%hard-regspec-value gpr)))
    ;; Any other GPRs that had contained loc no longer do so.
    (dotimes (i 32)
      (unless (eql i gpr)
        (arm642-invalidate-regmap-entry i loc)))
    (if (logbitp gpr *arm642-gpr-locations-valid-mask*)
      (push loc (svref *arm642-gpr-locations* gpr))
      (setf (svref *arm642-gpr-locations* gpr) (list loc)))

    (setq *arm642-gpr-locations-valid-mask* (logior *arm642-gpr-locations-valid-mask* (ash 1 gpr)))))

;;; For vpush: nothing else should claim to contain loc.
(defun arm642-regmap-note-reg-location (gpr loc)
  (let* ((gpr (%hard-regspec-value gpr)))
    (if (logbitp gpr *arm642-gpr-locations-valid-mask*)
      (push loc (svref *arm642-gpr-locations* gpr))
      (setf (svref *arm642-gpr-locations* gpr) (list loc)))
    (setq *arm642-gpr-locations-valid-mask* (logior *arm642-gpr-locations-valid-mask* (ash 1 gpr)))))

(defun arm642-regmap-note-vstack-delta (new old)
  (when (< new old)
    (let* ((mask *arm642-gpr-locations-valid-mask*)
           (info *arm642-gpr-locations*))
    (unless (eql 0 mask)
      (dotimes (i 32 (setq *arm642-gpr-locations-valid-mask* mask))
        (when (logbitp i mask)
          (let* ((locs (svref info i))
                 (head (cons nil locs))
                 (tail head))
            (declare (dynamic-extent head))
            (dolist (loc locs)
              (if (>= loc new)
                (setf (cdr tail) (cddr tail))
                (setq tail (cdr tail))))
            (when (null (setf (svref info i) (cdr head)))
              (setq mask (logandc2 mask (ash 1 i)))))))))))

(defun arm642-copy-regmap (mask from to)
  (dotimes (i 32)
    (when (logbitp i mask)
      (setf (svref to i) (copy-list (svref from i))))))

(defun arm642-copy-constmap (mask from to)
  (dotimes (i 32)
    (when (logbitp i mask)
      (setf (svref to i) (svref from i)))))


(defmacro with-arm642-saved-regmaps ((mask constmask map constmap) &body body)
  `(let* ((,mask *arm642-gpr-locations-valid-mask*)
          (,constmask *arm642-gpr-constants-valid-mask*)
          (,map (make-array 32 :initial-element nil))
          (,constmap (make-array 32)))
    (declare (dynamic-extent ,map ,constmap))
    (arm642-copy-regmap ,mask *arm642-gpr-locations* ,map)
    (arm642-copy-constmap ,constmask *arm642-gpr-constants* ,constmap)
    ,@body))


;;; ======================================================================
;;; Chunk 3: Debug info, NVR, lambda entry
;;; ======================================================================

(defun arm642-generate-pc-source-map (debug-info)
  (let* ((definition-source-note (getf debug-info '%function-source-note))
         (emitted-source-notes (getf debug-info 'pc-source-map))
         (def-start (source-note-start-pos definition-source-note))
         (n (length emitted-source-notes))
         (nvalid 0)
         (max 0)
         (pc-starts (make-array n))
         (pc-ends (make-array n))
         (text-starts (make-array n))
         (text-ends (make-array n)))
    (declare (fixnum n nvalid)
             (dynamic-extent pc-starts pc-ends text-starts text-ends))
    (dolist (start emitted-source-notes)
      (let* ((pc-start (arm642-vinsn-note-label-address start t))
             (pc-end (arm642-vinsn-note-label-address (vinsn-note-peer start) nil))
             (source-note (aref (vinsn-note-info start) 0))
             (text-start (- (source-note-start-pos source-note) def-start))
             (text-end (- (source-note-end-pos source-note) def-start)))
        (declare (fixnum pc-start pc-end text-start text-end))
        (when (and (plusp pc-start)
                   (plusp pc-end)
                   (plusp text-start)
                   (plusp text-end))
          (if (> pc-start max) (setq max pc-start))
          (if (> pc-end max) (setq max pc-end))
          (if (> text-start max) (setq max text-start))
          (if (> text-end max) (setq max text-end))
          (setf (svref pc-starts nvalid) pc-start
                (svref pc-ends nvalid) pc-end
                (svref text-starts nvalid) text-start
                (svref text-ends nvalid) text-end)
          (incf nvalid))))
    (let* ((nentries (* nvalid 4))
           (vec (cond ((< max #x100) (make-array nentries :element-type '(unsigned-byte 8)))
                      ((< max #x10000) (make-array nentries :element-type '(unsigned-byte 16)))
                      (t (make-array nentries :element-type '(unsigned-byte 32))))))
      (declare (fixnum nentries))
      (do* ((i 0 (+ i 4))
            (j 1 (+ j 4))
            (k 2 (+ k 4))
            (l 3 (+ l 4))
            (idx 0 (1+ idx)))
          ((= i nentries) vec)
        (declare (fixnum i j k l idx))
        (setf (aref vec i) (svref pc-starts idx)
              (aref vec j) (svref pc-ends idx)
              (aref vec k) (svref text-starts idx)
              (aref vec l) (svref text-ends idx))))))

(defun arm642-vinsn-note-label-address (note &optional start-p sym)
  (let* ((lap-label (vinsn-note-address note)))
    (if lap-label
      (arm64::lap-label-address lap-label)
      (compiler-bug "Missing or bad ~s label: ~s"
                    (if start-p 'start 'end) sym))))

(defun arm642-digest-symbols ()
  (when *arm642-recorded-symbols*
    (setq *arm642-recorded-symbols* (nx2-recorded-symbols-in-arglist-order *arm642-recorded-symbols* *arm642-cur-afunc*))
    (let* ((symlist *arm642-recorded-symbols*)
           (len (length symlist))
           (syms (make-array len))
           (ptrs (make-array (%i+  (%i+ len len) len) :element-type '(unsigned-byte 32)))
           (i -1)
           (j -1))
      (declare (fixnum i j))
      (dolist (info symlist (progn (%rplaca symlist syms)
                                   (%rplacd symlist ptrs)))
        (destructuring-bind (var sym startlab endlab) info
          (let* ((ea (var-ea var))
                 (ea-val (ldb (byte 16 0) ea)))
            (setf (aref ptrs (incf i)) (if (memory-spec-p ea)
                                         (logior (ash ea-val 6) #o77)
                                         ea-val)))
          (setf (aref syms (incf j)) sym)
          (setf (aref ptrs (incf i)) (arm642-vinsn-note-label-address startlab t sym))
          (setf (aref ptrs (incf i)) (arm642-vinsn-note-label-address endlab nil sym))))
      *arm642-recorded-symbols*)))

(defun arm642-decls (decls)
  (if (fixnump decls)
    (locally (declare (fixnum decls))
      (setq *arm642-tail-allow* (neq 0 (%ilogand2 $decl_tailcalls decls))
            *arm642-open-code-inline* (neq 0 (%ilogand2 $decl_opencodeinline decls))
            *arm642-full-safety* (neq 0 (%ilogand2 $decl_full_safety decls))
            *arm642-reckless* (neq 0 (%ilogand2 $decl_unsafe decls))
            *arm642-float-safety*  (neq 0 (%ilogand2 $decl_float_safety decls))
            *arm642-trust-declarations* (neq 0 (%ilogand2 $decl_trustdecls decls))))))


;;; ARM64 fixnum overflow check.
;;; The fixnum-*-set-flags vinsns use lsl/asr/cmp to detect 56-bit overflow:
;;; EQ = no overflow, NE = overflow.
(defun arm642-check-fixnum-overflow (seg crf target &optional labelno)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((no-overflow (backend-get-next-label))
           (label (if labelno (aref *backend-labels* labelno))))
      (! cbranch-false (or label (aref *backend-labels* no-overflow)) crf arm64::arm64-cond-ne)
      (if *arm642-open-code-inline*
        (! handle-fixnum-overflow-inline target target)
        (let* ((target-other (not (eql (hard-regspec-value target)
                                       arm64::arg_z)))
               (arg (if target-other
                      (make-wired-lreg arm64::arg_z)
                      target))
               (result (make-wired-lreg arm64::arg_z)))
          (when target-other
            (arm642-copy-register seg arg target))
          (! call-subprim-1 result (subprim-name->offset '.SPfix-overflow) arg)
          (when target-other
            (arm642-copy-register seg target result))))
        (when labelno (-> labelno))
        (@ no-overflow))))



;;; Vpush the first N non-volatile-registers.
;;; ARM64: no NVRs ($numarm64saveregs = 0), so n is always 0.
(defun arm642-save-nvrs (seg n)
  (declare (fixnum n))
  (when (> n 0)
    (setq *arm642-compiler-register-save-note* (enqueue-vinsn-note seg :regsave))
    (with-arm64-local-vinsn-macros (seg)
      (! save-nvrs n))
    (incf *arm642-vstack* (the fixnum (* n *arm642-target-node-size*)))
    (setq *arm642-register-restore-ea* *arm642-vstack*
          *arm642-register-restore-count* n)))

(defun arm642-save-non-volatile-fprs (seg n)
  (unless (eql n 0)
    (with-arm64-local-vinsn-macros (seg)
      (! push-nvfprs n (logior (ash n arm64::num-subtag-bits) arm64::subtag-double-float-vector)))
    (setq *arm642-non-volatile-fpr-count* n)))

(defun arm642-restore-non-volatile-fprs (seg)
  (let* ((n *arm642-non-volatile-fpr-count*))
    (unless (eql n 0)
      (with-arm64-local-vinsn-macros (seg)
        (! pop-nvfprs n)))))


;;; ARM64: no NVRs, so this is effectively a no-op.
(defun arm642-restore-nvrs (seg multiple-values-on-stack)
  (let* ((ea *arm642-register-restore-ea*)
         (n *arm642-register-restore-count*))
    (when (and ea n)
      (with-arm64-local-vinsn-macros (seg)
        (let* ((diff (- *arm642-vstack* ea)))
          (if (and (eql 0 diff)
                   (not multiple-values-on-stack))
            (! restore-nvrs n arm64::vsp)
            (let* ((reg (make-unwired-lreg
                         (if (= *available-backend-imm-temps* 0)
                           (select-node-temp)
                           (select-imm-temp))
                         :class hard-reg-class-gpr
                         :mode hard-reg-class-gpr-mode-node)))
              (if (eql 0 diff)
                (! fixnum-add reg arm64::vsp arm64::nargs)
                (progn
                  (if (< diff 4096)
                    (! add-immediate reg arm64::vsp diff)
                    (progn
                      (arm642-lri seg reg diff)
                      (! fixnum-add reg arm64::vsp reg)))
                  (when multiple-values-on-stack
                    (! fixnum-add reg reg arm64::nargs))))
              (! restore-nvrs n reg))))))))


(defun arm642-bind-lambda (seg req opt rest keys auxen optsupvloc passed-in-regs lexpr &optional inherited
                             &aux (vloc 0)
                             (nkeys (list-length (%cadr keys)))
                             reg)
  (declare (fixnum vloc))
  (dolist (arg inherited)
    (if (memq arg passed-in-regs)
      (arm642-set-var-ea seg arg (var-ea arg))
      (progn
        (if (setq reg (nx2-assign-register-var arg))
          (arm642-init-regvar seg arg reg (arm642-vloc-ea vloc))
          (arm642-bind-var seg arg vloc))
        (setq vloc (%i+ vloc *arm642-target-node-size*)))))
  (dolist (arg req)
    (if (memq arg passed-in-regs)
      (arm642-set-var-ea seg arg (var-ea arg))
      (progn
        (if (setq reg (nx2-assign-register-var arg))
          (arm642-init-regvar seg arg reg (arm642-vloc-ea vloc))
          (arm642-bind-var seg arg vloc))
        (setq vloc (%i+ vloc *arm642-target-node-size*)))))
  (when opt
    (if (arm642-hard-opt-p opt)
      (setq vloc (apply #'arm642-initopt seg vloc optsupvloc opt))
      (dolist (var (%car opt))
        (if (memq var passed-in-regs)
          (arm642-set-var-ea seg var (var-ea var))
          (progn
            (if (setq reg (nx2-assign-register-var var))
              (arm642-init-regvar seg var reg (arm642-vloc-ea vloc))
              (arm642-bind-var seg var vloc))
            (setq vloc (+ vloc *arm642-target-node-size*)))))))
  (when rest
    (if lexpr
      (progn
        (if (setq reg (nx2-assign-register-var rest))
          (progn
            (arm642-load-lexpr-address seg reg)
            (arm642-set-var-ea seg rest reg))
          (with-imm-temps () ((nargs-cell :natural))
            (arm642-load-lexpr-address seg nargs-cell)
            (let* ((loc *arm642-vstack*))
              (arm642-vpush-register seg nargs-cell)
              (arm642-bind-var seg rest loc)))))
      (let* ((rvloc (+ vloc (* 2 *arm642-target-node-size* nkeys))))
        (if (setq reg (nx2-assign-register-var rest))
          (arm642-init-regvar seg rest reg (arm642-vloc-ea rvloc))
          (arm642-bind-var seg rest rvloc)))))
  (when keys
    (apply #'arm642-init-keys seg vloc  keys))
  (arm642-seq-bind seg (%car auxen) (%cadr auxen)))

(defun arm642-initopt (seg vloc spvloc vars inits spvars)
  (with-arm64-local-vinsn-macros (seg)
    (dolist (var vars vloc)
      (let* ((initform (pop inits))
             (spvar (pop spvars))
             (reg (nx2-assign-register-var var))
             (sp-reg ($ arm64::arg_z))
             (regloadedlabel (if reg (backend-get-next-label))))
        (unless (nx-null initform)
          (arm642-stack-to-register seg (arm642-vloc-ea spvloc) sp-reg)
          (let ((skipinitlabel (backend-get-next-label)))
            (with-crf-target () crf
              (arm642-compare-register-to-nil seg crf (arm642-make-compound-cd 0 skipinitlabel) sp-reg  arm64::arm64-cond-eq t))
            (if reg
              (arm642-form seg reg regloadedlabel initform)
              (arm642-register-to-stack seg (arm642-one-untargeted-reg-form seg initform ($ arm64::arg_z)) (arm642-vloc-ea vloc)))
            (@ skipinitlabel)))
        (if reg
          (progn
            (arm642-init-regvar seg var reg (arm642-vloc-ea vloc))
            (@ regloadedlabel))
          (arm642-bind-var seg var vloc))
        (when spvar
          (if (setq reg (nx2-assign-register-var spvar))
            (arm642-init-regvar seg spvar reg (arm642-vloc-ea spvloc))
            (arm642-bind-var seg spvar spvloc))))
      (setq vloc (%i+ vloc *arm642-target-node-size*))
      (if spvloc (setq spvloc (%i+ spvloc *arm642-target-node-size*))))))

(defun arm642-init-keys (seg vloc allow-others keyvars keysupp keyinits keykeys)
  (declare (ignore keykeys allow-others))
  (with-arm64-local-vinsn-macros (seg)
    (dolist (var keyvars)
      (let* ((spvar (pop keysupp))
             (initform (pop keyinits))
             (reg (nx2-assign-register-var var))
             (regloadedlabel (if reg (backend-get-next-label)))
             (sp-reg ($ arm64::arg_z))
             (sploc (%i+ vloc *arm642-target-node-size*)))
        (unless (nx-null initform)
          (arm642-stack-to-register seg (arm642-vloc-ea sploc) sp-reg)
          (let ((skipinitlabel (backend-get-next-label)))
            (with-crf-target () crf
              (arm642-compare-register-to-nil seg crf (arm642-make-compound-cd 0 skipinitlabel) sp-reg  arm64::arm64-cond-eq t))
            (if reg
              (arm642-form seg reg regloadedlabel initform)
              (arm642-register-to-stack seg (arm642-one-untargeted-reg-form seg initform ($ arm64::arg_z)) (arm642-vloc-ea vloc)))
            (@ skipinitlabel)))
        (if reg
          (progn
            (arm642-init-regvar seg var reg (arm642-vloc-ea vloc))
            (@ regloadedlabel))
          (arm642-bind-var seg var vloc))
        (when spvar
          (if (setq reg (nx2-assign-register-var spvar))
            (arm642-init-regvar seg spvar reg (arm642-vloc-ea sploc))
            (arm642-bind-var seg spvar sploc))))
      (setq vloc (%i+ vloc (* 2 *arm642-target-node-size*))))))

;;; Return NIL if arg register should be vpushed, else var.
(defun arm642-retain-arg-register (var)
  (if var
    (when (var-nvr var)
      var)
    (compiler-bug "Missing var!")))


;;; nargs has been validated, arguments defaulted and canonicalized.
;;; Save caller's context, then vpush any argument registers that
;;; didn't get global registers assigned to their variables.
;;; Return a list of vars/nils for each argument register
;;;  (nil if vpushed, var if still in arg_reg).
(defun arm642-argregs-entry (seg revargs)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((nargs (length revargs))
           (reg-vars ()))
      (declare (type (unsigned-byte 16) nargs))
      (when (and
             (<= nargs $numarm64argregs)
             (not (some #'null revargs)))
        (setq *arm642-fixed-nargs* nargs))
      (if (<= nargs $numarm64argregs)       ; caller didn't vpush anything
        (! save-lisp-context-vsp)
        (let* ((offset (* (the fixnum (- nargs $numarm64argregs)) *arm642-target-node-size*)))
          (declare (fixnum offset))
          (! save-lisp-context-offset offset)))
      (when *arm642-fixed-args-label*
        (@ (setq *arm642-fixed-args-tail-label* (backend-get-next-label))))
      (destructuring-bind (&optional zvar yvar xvar &rest stack-args) revargs
        (let* ((nstackargs (length stack-args)))
          (arm642-set-vstack (* nstackargs *arm642-target-node-size*))
          ;; ARM64: no vpush-multiple-registers, push individually
          (when (>= nargs 3)
            (let* ((retain-x (arm642-retain-arg-register xvar)))
              (push retain-x reg-vars)
              (unless retain-x
                (arm642-regmap-note-store arm64::arg_x *arm642-vstack*)
                (arm642-adjust-vstack *arm642-target-node-size*)
                (! vpush-register ($ arm64::arg_x)))))
          (when (>= nargs 2)
            (let* ((retain-y (arm642-retain-arg-register yvar)))
              (push retain-y reg-vars)
              (unless retain-y
                (arm642-regmap-note-store arm64::arg_y *arm642-vstack*)
                (arm642-adjust-vstack *arm642-target-node-size*)
                (! vpush-register ($ arm64::arg_y)))))
          (when (>= nargs 1)
            (let* ((retain-z (arm642-retain-arg-register zvar)))
              (push retain-z reg-vars)
              (unless retain-z
                (arm642-regmap-note-store arm64::arg_z *arm642-vstack*)
                (arm642-adjust-vstack *arm642-target-node-size*)
                (! vpush-register ($ arm64::arg_z)))))))
      reg-vars)))

;;; Just required args.
(defun arm642-req-nargs-entry (seg rev-fixed-args)
  (let* ((nargs (length rev-fixed-args)))
    (declare (type (unsigned-byte 16) nargs))
    (with-arm64-local-vinsn-macros (seg)
      (unless *arm642-reckless*
        ;; ARM64 check-exact-nargs vinsn handles encoding internally
        (! check-exact-nargs nargs))
      (arm642-argregs-entry seg rev-fixed-args))))

;;; No more than three &optional args; all default to NIL and none have
;;; supplied-p vars.  No &key/&rest.
(defun arm642-simple-opt-entry (seg rev-opt-args rev-req-args)
  (let* ((min (length rev-req-args))
         (nopt (length rev-opt-args))
         (max (+ min nopt)))
    (declare (type (unsigned-byte 16) min nopt max))
    (with-arm64-local-vinsn-macros (seg)
      (unless *arm642-reckless*
        (when rev-req-args
          (! check-min-nargs min))
        (! check-max-nargs max))
      (if (= nopt 1)
        (! default-1-arg min)
        (if (= nopt 2)
          (! default-2-args min)
          (! default-3-args min)))
      (arm642-argregs-entry seg (append rev-opt-args rev-req-args)))))

;;; We're responsible for computing the caller's VSP and saving
;;; caller's state.
(defun arm642-lexpr-entry (seg num-fixed)
  (with-arm64-local-vinsn-macros (seg)
    (! save-lexpr-argregs num-fixed)
    (dotimes (i num-fixed)
      (! copy-lexpr-argument))
    (! save-lisp-context-vsp)))

(defun arm642-load-lexpr-address (seg dest)
  (with-arm64-local-vinsn-macros (seg)
    (! load-vframe-address dest *arm642-vstack*)))


(defun arm642-vloc-ea (n &optional vcell-p)
  (setq n (make-memory-spec (dpb memspec-frame-address memspec-type-byte n)))
  (if vcell-p
    (make-vcell-memory-spec n)
    n))


;;; ======================================================================
;;; Chunk 4: Form dispatch, immediate handling, register/stack operations
;;; ======================================================================

(defun arm642-acode-operator-function (form)
  (or (and (acode-p form)
           (svref *arm642-specials* (%ilogand #.operator-id-mask (acode-operator form))))
      (compiler-bug "arm642-form ? ~s" form)))

(defmacro arm64-with-note ((form-var seg-var &rest other-vars) &body body)
  (let* ((note (gensym "NOTE"))
         (code-note (gensym "CODE-NOTE"))
         (source-note (gensym "SOURCE-NOTE"))
         (start (gensym "START"))
         (arm64-with-note-body (gensym "ARM64-WITH-NOTE-BODY")))
    `(flet ((,arm64-with-note-body (,form-var ,seg-var ,@other-vars) ,@body))
       (let ((,note (acode-note ,form-var)))
         (if ,note
           (let* ((,code-note (and ,note (code-note-p ,note) ,note))
                  (,source-note (if ,code-note
                                  (code-note-source-note ,note)
                                  ,note))
                  (,start (and ,source-note
                               (enqueue-vinsn-note ,seg-var :source-location-begin ,source-note))))
             (prog2
                 (when ,code-note
                   (with-arm64-local-vinsn-macros (,seg-var)
                     (arm642-store-immediate ,seg-var ,code-note arm64::temp0)
                     (with-node-temps (arm64::temp0) (zero)
                       (! lri zero 0)
                       (! misc-set-c-node ($ zero) ($ arm64::temp0) 1))))
                 (,arm64-with-note-body ,form-var ,seg-var ,@other-vars)
               (when ,source-note
                 (close-vinsn-note ,seg-var ,start))))
           (,arm64-with-note-body ,form-var ,seg-var ,@other-vars))))))

(defun arm642-toplevel-form (seg vreg xfer form)
  (let* ((code-note (acode-note form))
         (args (if code-note `(,@(acode-operands form) ,code-note) (acode-operands form))))
    (apply (arm642-acode-operator-function form) seg vreg xfer args)))

(defun arm642-form (seg vreg xfer form)
  (arm64-with-note (form seg vreg xfer)
    (if (nx-null form)
      (arm642-nil seg vreg xfer)
      (if (nx-t form)
        (arm642-t seg vreg xfer)
        (let ((fn (arm642-acode-operator-function form))
              (op (acode-operator form)))
          (if (and (null vreg)
                   (%ilogbitp operator-acode-subforms-bit op)
                   (%ilogbitp operator-assignment-free-bit op)
                   (%ilogbitp operator-side-effect-free-bit op))
            (dolist (f (acode-operands form) (arm642-branch seg xfer nil))
              (arm642-form seg nil nil f))
            (apply fn seg vreg xfer (acode-operands form))))))))

;;; dest is a float reg - form is acode
(defun arm642-form-float (seg freg xfer form)
  (declare (ignore xfer))
  (arm64-with-note (form seg freg)
    (when (or (nx-null form)(nx-t form))(compiler-bug "arm642-form to freg ~s" form))
    (when (and (= (get-regspec-mode freg) hard-reg-class-fpr-mode-double)
               (arm642-form-typep form 'double-float))
      ;; Encoding the source type in the dest register spec
      (set-node-regspec-type-modes freg hard-reg-class-fpr-type-double))
    (let* ((fn (arm642-acode-operator-function form)))
      (apply fn seg freg nil (acode-operands form)))))



(defun arm642-form-typep (form type)
  (acode-form-typep form type *arm642-trust-declarations*))

(defun arm642-form-type (form)
  (acode-form-type form *arm642-trust-declarations*))

(defun arm642-use-operator (op seg vreg xfer &rest forms)
  (declare (dynamic-extent forms))
  (apply (svref *arm642-specials* (%ilogand operator-id-mask op)) seg vreg xfer forms))



(defun arm642-nil (seg vreg xfer)
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (if (arm642-for-value-p vreg)
      (ensuring-node-target (target vreg)
        (let* ((regval (hard-regspec-value target))
               (regs (arm642-gprs-containing-constant nil)))
          (unless (logbitp regval regs)
            (! load-nil target)
            (setf *arm642-gpr-constants-valid-mask*
                  (logior *arm642-gpr-constants-valid-mask* (ash 1 regval))
                  (svref *arm642-gpr-constants* regval) nil)))))
    (arm642-branch seg (arm642-cd-false xfer) vreg)))

(defun arm642-t (seg vreg xfer)
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (if (arm642-for-value-p vreg)
      (ensuring-node-target (target vreg)
        (let* ((regval (hard-regspec-value target))
               (regs (arm642-gprs-containing-constant t)))
          (declare (fixnum regval regs))
          (unless (logbitp regval regs)
            (if (zerop regs)
              (! load-t target)
              (let* ((r (1- (integer-length regs))))
                (! copy-node-gpr target r)))
            (setf *arm642-gpr-constants-valid-mask*
                  (logior *arm642-gpr-constants-valid-mask* (ash 1 regval))
                  (svref *arm642-gpr-constants* regval) t)))))
    (arm642-branch seg (arm642-cd-true xfer) vreg)))



(defun arm642-for-value-p (vreg)
  (and vreg (not (backend-crf-p vreg))))

(defun arm642-mvpass (seg form &optional xfer)
  (with-arm64-local-vinsn-macros (seg)
    (arm642-form seg ($ arm64::arg_z) (logior (or xfer 0) $backend-mvpass-mask) form)))

(defun arm642-adjust-vstack (delta)
  (arm642-set-vstack (%i+ *arm642-vstack* delta)))

(defun arm642-set-vstack (new)
  (arm642-regmap-note-vstack-delta new *arm642-vstack*)
  (setq *arm642-vstack* new))



;;; ARM64 has 32 GPRs
(defun arm642-register-for-frame-offset (offset &optional suggested)
  (let* ((mask *arm642-gpr-locations-valid-mask*)
         (info *arm642-gpr-locations*))
    (if (and suggested
             (logbitp suggested mask)
             (memq offset (svref info suggested)))
      suggested
      (dotimes (reg 32)
        (when (and (logbitp reg mask)
                   (memq offset (svref info reg)))
          (return reg))))))

(defun arm642-reg-for-ea (ea)
  (when (and (memory-spec-p ea)
             (eql (memspec-type ea) memspec-frame-address)
             (not (addrspec-vcell-p ea)))
    (let* ((offset (memspec-frame-address-offset ea))
           (mask *arm642-gpr-locations-valid-mask*)
           (info *arm642-gpr-locations*))
      (declare (fixnum mask) (simple-vector info))
      (dotimes (reg 32)
        (when (and (logbitp reg mask)
                   (memq offset (svref info reg)))
          (return reg))))))

(defun arm642-reg-for-form (form hint)
  (let* ((var (arm642-lexical-reference-p form)))
    (cond ((node-reg-p hint)
           (if var
             (arm642-reg-for-ea (var-ea var))
             (multiple-value-bind (value constantp) (acode-constant-p form)
               (when constantp
                 (let* ((regs (arm642-gprs-containing-constant value))
                        (regno (hard-regspec-value hint)))
                   (if (logbitp regno regs)
                     hint
                     (unless (eql 0 regs)
                       (1- (integer-length regs)))))))))
          ((eql (hard-regspec-class hint) hard-reg-class-fpr)
           (if var
             (let* ((ea (var-ea var)))
               (when (register-spec-p ea)
                 (and (eql (hard-regspec-class ea) hard-reg-class-fpr)
                      (eql (get-regspec-mode ea) (get-regspec-mode hint))
                      ea)))
             (let* ((val (acode-constant-p form)))
               (if (and (= (get-regspec-mode hint) hard-reg-class-fpr-mode-single)
                        (eql val 0.0f0))
                 (make-hard-fp-reg (hard-regspec-value arm64::single-float-zero) hard-reg-class-fpr-mode-single)
                 (if (and (= (get-regspec-mode hint) hard-reg-class-fpr-mode-double)
                          (eql val 0.0d0))
                   (make-hard-fp-reg (hard-regspec-value arm64::double-float-zero))))))))))

(defun arm642-stack-to-register (seg memspec reg)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((offset (memspec-frame-address-offset memspec)))
      (if (eql (hard-regspec-class reg) hard-reg-class-fpr)
        (with-node-target () temp
          (arm642-stack-to-register seg memspec temp)
          (arm642-copy-register seg reg temp))
        (let* ((mask *arm642-gpr-locations-valid-mask*)
               (info *arm642-gpr-locations*)
               (regno (%hard-regspec-value reg))
               (other (arm642-register-for-frame-offset offset regno)))
          (unless (eql regno other)
            (cond (other
                   (let* ((vinsn (! copy-node-gpr reg other)))
                     (setq *arm642-gpr-locations-valid-mask*
                           (logior mask (ash 1 regno)))
                     (setf (svref info regno)
                           (copy-list (svref info other)))
                     vinsn))
                  (t
                   (let* ((vinsn (! vframe-load reg offset *arm642-vstack*)))
                     (setq *arm642-gpr-locations-valid-mask*
                           (logior mask (ash 1 regno)))
                     (setf (svref info regno) (list offset))
                     vinsn)))))))))




(defun arm642-register-to-stack (seg reg memspec)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((offset (memspec-frame-address-offset memspec))
           (vinsn (! vframe-store reg offset *arm642-vstack*)))
      (arm642-regmap-note-store (%hard-regspec-value reg) offset)
      vinsn)))


(defun arm642-ea-open (ea)
  (if (and ea (not (typep ea 'lreg)) (addrspec-vcell-p ea))
    (make-memory-spec (memspec-frame-address-offset ea))
    ea))

(defun arm642-set-NARGS (seg n)
  (if (> n call-arguments-limit)
    (compiler-bug "~s exceeded." call-arguments-limit)
    (if (< n 256)
      (with-arm64-local-vinsn-macros (seg)
        (! set-nargs n))
      (arm642-lri seg arm64::nargs (ash n arm64::word-shift)))))

(defun arm642-single-float-bits (the-sf)
  (single-float-bits the-sf))

(defun arm642-double-float-bits (the-df)
  (double-float-bits the-df))

(defun arm642-immediate (seg vreg xfer form)
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (if vreg
      (if (and (= (hard-regspec-class vreg) hard-reg-class-fpr)
               (or (and (typep form 'double-float) (= (get-regspec-mode vreg) hard-reg-class-fpr-mode-double))
                   (and (typep form 'short-float)(= (get-regspec-mode vreg) hard-reg-class-fpr-mode-single))))
        (if (zerop form)
          (if (eql form 0.0d0)
            (! zero-double-float-register vreg)
            (! zero-single-float-register vreg))
          (if (typep form 'short-float)
            (let* ((bits (arm642-single-float-bits form)))
              (! load-single-float-constant-from-data vreg bits))
            (multiple-value-bind (high low) (arm642-double-float-bits form)
              (declare (integer high low))
              (! load-double-float-constant-from-data vreg high low))))
        (if (and (typep form '(unsigned-byte 64))
                 (= (hard-regspec-class vreg) hard-reg-class-gpr)
                 (= (get-regspec-mode vreg)
                    hard-reg-class-gpr-mode-u64))
          (arm642-lri seg vreg form)
          (ensuring-node-target (target vreg)
            (let* ((regno (hard-regspec-value target))
                   (regs (arm642-gprs-containing-constant form)))
              (unless (logbitp regno regs)
                (if (eql 0 regs)
                  (if (characterp form)
                    (! load-character-constant target (char-code form))
                    (arm642-store-immediate seg form target))
                  (let* ((r (1- (integer-length regs))))
                    (! copy-node-gpr target r)))
                (setf *arm642-gpr-constants-valid-mask*
                      (logior *arm642-gpr-constants-valid-mask*
                              (ash 1 regno))
                      (svref *arm642-gpr-constants* regno) form))))))
        (if (and (listp form) *load-time-eval-token* (eq (car form) *load-time-eval-token*))
          (arm642-store-immediate seg form ($ arm64::temp0))))
    (^)))

(defun arm642-register-constant-p (form)
  (and (consp form)
           (or (memq form *arm642-vcells*)
               (memq form *arm642-fcells*))
           (%cdr form)))

;;; On ARM64, misc-data-offset=0, node-size=8.
;;; Constants vector: element 0 = header, element 1 = fn, data starts at element 2.
;;; Byte offset = (idx + 2) * 8.  LDR scaled range: 0..32760 (always sufficient).
(defun arm642-store-immediate (seg imm dest)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((reg (arm642-register-constant-p imm)))
      (if reg
        (arm642-copy-register seg dest reg)
        (let ((idx (backend-immediate-index imm)))
          (if (< (+ arm64::misc-data-offset (ash (+ idx 2) arm64::word-shift)) 32768)
            (! ref-constant dest idx)
            (with-imm-target () (idxreg :s64)
              (arm642-lri seg idxreg (+ arm64::misc-data-offset (ash (+ idx 2) arm64::word-shift)))
              (! ref-indexed-constant dest idxreg)))))
      dest)))


;;; Returns label iff form is (local-go <tag>) and can go without adjusting stack.
(defun arm642-go-label (form)
  (let ((current-stack (arm642-encode-stack)))
    (while (and (acode-p form) (or (eq (acode-operator form) (%nx1-operator progn))
                                   (eq (acode-operator form) (%nx1-operator local-tagbody))))
      (setq form (caar (acode-operands form))))
    (when (acode-p form)
      (let ((op (acode-operator form)))
        (if (and (eq op (%nx1-operator local-go))
                 (arm642-equal-encodings-p (%caddr (car (acode-operands form))) current-stack))
          (%cadr (car (acode-operands form)))
          (if (and (eq op (%nx1-operator local-return-from))
                   (nx-null (cadr (acode-operands form))))
            (let ((tagdata (car (car (acode-operands form)))))
              (and (arm642-equal-encodings-p (cdr tagdata) current-stack)
                   (null (caar tagdata))
                   (< 0 (cdar tagdata) $backend-mvpass)
                   (cdar tagdata)))))))))

(defun arm642-single-valued-form-p (form)
  (setq form (acode-unwrapped-form-value form))
  (or (nx-null form)
      (nx-t form)
      (if (acode-p form)
        (let ((op (acode-operator form)))
          (or (%ilogbitp operator-single-valued-bit op)
              (and (eql op (%nx1-operator values))
                   (let ((values (car (acode-operands form))))
                     (and values (null (cdr values)))))
              nil)))))


;;; On ARM64 with 56-bit fixnums, all s32 values fit in fixnums.
;;; Always use inline boxing (identity since fixnumshift=0).
(defun arm642-box-s32 (seg node-dest s32-src)
  (with-arm64-local-vinsn-macros (seg)
    (! s32->integer node-dest s32-src)))



;;; On ARM64 with 56-bit fixnums, all u32 values fit in fixnums.
;;; Always use inline boxing (identity since fixnumshift=0).
(defun arm642-box-u32 (seg node-dest u32-src)
  (with-arm64-local-vinsn-macros (seg)
    (! u32->integer node-dest u32-src)))


;;; ======================================================================
;;; Chunk 5: Vector ref/set operations (all element types, multi-dim arrays)
;;; ======================================================================

(defun arm642-vref1 (seg vreg xfer type-keyword src unscaled-idx index-known-fixnum)
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (when vreg
      (let* ((arch (backend-target-arch *target-backend*))
             (is-node (member type-keyword (arch::target-gvector-types arch)))
             (is-1-bit (member type-keyword (arch::target-1-bit-ivector-types arch)))
             (is-8-bit (member type-keyword (arch::target-8-bit-ivector-types arch)))
             (is-16-bit (member type-keyword (arch::target-16-bit-ivector-types arch)))
             (is-32-bit (member type-keyword (arch::target-32-bit-ivector-types arch)))
             (is-64-bit (member type-keyword (arch::target-64-bit-ivector-types arch)))
             (is-128-bit (eq type-keyword :complex-double-float-vector))
             (is-signed (member type-keyword '(:signed-8-bit-vector :signed-16-bit-vector :signed-32-bit-vector :signed-64-bit-vector :fixnum-vector)))
             (vreg-class (hard-regspec-class vreg))
             (vreg-mode
              (if (or (eql vreg-class hard-reg-class-gpr)
                      (eql vreg-class hard-reg-class-fpr))
                (get-regspec-mode vreg)
                hard-reg-class-gpr-mode-invalid))
             (temp-is-vreg nil))
        (cond
          (is-node
           (ensuring-node-target (target vreg)
             (if (and index-known-fixnum (<= index-known-fixnum
                                             (arch::target-max-32-bit-constant-index arch)))
               (! misc-ref-c-node target src index-known-fixnum)
               (with-imm-target () (idx-reg :u64)
                 (if index-known-fixnum
                   (arm642-absolute-natural seg idx-reg nil (+ (arch::target-misc-data-offset arch) (ash index-known-fixnum *arm642-target-node-shift*)))
                   (! scale-node-misc-index idx-reg unscaled-idx))
                 (! misc-ref-node target src idx-reg)))))
          (is-32-bit
           (with-imm-target () (temp :u32)
             (with-fp-target () (fp-val :single-float)
               (if (eql vreg-class hard-reg-class-gpr)
                 (if
                   (if is-signed
                     (or (eql vreg-mode hard-reg-class-gpr-mode-s32)
                         (eql vreg-mode hard-reg-class-gpr-mode-s64))
                     (or (eql vreg-mode hard-reg-class-gpr-mode-u32)
                         (eql vreg-mode hard-reg-class-gpr-mode-u64)))
                   (setq temp vreg temp-is-vreg t)
                   (if is-signed
                     (set-regspec-mode temp hard-reg-class-gpr-mode-s32)))
                 (if (and (eql vreg-class hard-reg-class-fpr)
                          (eql vreg-mode hard-reg-class-fpr-mode-single))
                   (setf fp-val vreg temp-is-vreg t)))
               (if (and index-known-fixnum (<= index-known-fixnum
                                               (if (eq type-keyword :single-float-vector)
                                                 255
                                                 (arch::target-max-32-bit-constant-index arch))))
                 (cond ((eq type-keyword :single-float-vector)
                        (! misc-ref-c-single-float fp-val src index-known-fixnum))
                       (t
                        (if is-signed
                          (! misc-ref-c-s32 temp src index-known-fixnum)
                          (! misc-ref-c-u32 temp src index-known-fixnum))))
                 (with-imm-target () idx-reg
                   (if index-known-fixnum
                     (arm642-absolute-natural seg idx-reg nil (+ (arch::target-misc-data-offset arch) (ash index-known-fixnum 2)))
                     (! scale-32bit-misc-index idx-reg unscaled-idx))
                   (cond ((eq type-keyword :single-float-vector)
                          (! misc-ref-single-float fp-val src idx-reg))
                         (t
                          (if is-signed
                            (! misc-ref-s32 temp src idx-reg)
                            (! misc-ref-u32 temp src idx-reg))))))
               (case type-keyword
                 (:single-float-vector
                  (if (eq vreg-class hard-reg-class-fpr)
                    (<- fp-val)
                    (ensuring-node-target (target vreg)
                      (! single->node target fp-val))))
                 (:signed-32-bit-vector
                  (unless temp-is-vreg
                    (ensuring-node-target (target vreg)
                      (arm642-box-s32 seg target temp))))
                 (:fixnum-vector
                  (unless temp-is-vreg
                    (ensuring-node-target (target vreg)
                      (! box-fixnum target temp))))
                 (:simple-string
                  (ensuring-node-target (target vreg)
                    (! u32->char target temp)))
                 (t
                  (unless temp-is-vreg
                    (ensuring-node-target (target vreg)
                      (arm642-box-u32 seg target temp))))))))
          (is-8-bit
           (with-imm-target () (temp :u8)
             (if (and (eql vreg-class hard-reg-class-gpr)
                      (or
                       (and is-signed
                            (or (eql vreg-mode hard-reg-class-gpr-mode-s8)
                                (eql vreg-mode hard-reg-class-gpr-mode-s16)
                                (eql vreg-mode hard-reg-class-gpr-mode-s32)
                                (eql vreg-mode hard-reg-class-gpr-mode-s64)))
                       (and (not is-signed)
                            (or (eql vreg-mode hard-reg-class-gpr-mode-u8)
                                (eql vreg-mode hard-reg-class-gpr-mode-s16)
                                (eql vreg-mode hard-reg-class-gpr-mode-u16)
                                (eql vreg-mode hard-reg-class-gpr-mode-s32)
                                (eql vreg-mode hard-reg-class-gpr-mode-u32)
                                (eql vreg-mode hard-reg-class-gpr-mode-s64)
                                (eql vreg-mode hard-reg-class-gpr-mode-u64)))))
               (setq temp vreg temp-is-vreg t)
               (if is-signed
                 (set-regspec-mode temp hard-reg-class-gpr-mode-s8)))
             (if (and index-known-fixnum (<= index-known-fixnum (arch::target-max-8-bit-constant-index arch)))
               (if is-signed
                 (! misc-ref-c-s8 temp src index-known-fixnum)
                 (! misc-ref-c-u8 temp src index-known-fixnum))
               (with-imm-target () idx-reg
                 (if index-known-fixnum
                   (arm642-absolute-natural seg idx-reg nil (+ (arch::target-misc-data-offset arch) index-known-fixnum))
                   (! scale-8bit-misc-index idx-reg unscaled-idx))
                 (if is-signed
                   (! misc-ref-s8 temp src idx-reg)
                   (! misc-ref-u8 temp src idx-reg))))
             (ecase type-keyword
               (:unsigned-8-bit-vector
                (unless temp-is-vreg
                  (ensuring-node-target (target vreg)
                    (! box-fixnum target temp))))
               (:signed-8-bit-vector
                (unless temp-is-vreg
                  (ensuring-node-target (target vreg)
                    (! box-fixnum target temp))))
               (:simple-string
                (ensuring-node-target (target vreg)
                  (! u32->char target temp))))))
          (is-16-bit
           (ensuring-node-target (target vreg)
             (with-imm-target () temp
               (if (and index-known-fixnum
                        (<= index-known-fixnum (arch::target-max-16-bit-constant-index arch)))
                 (if is-signed
                   (! misc-ref-c-s16 temp src index-known-fixnum)
                   (! misc-ref-c-u16 temp src index-known-fixnum))
                 (with-imm-target () idx-reg
                   (if index-known-fixnum
                     (arm642-absolute-natural seg idx-reg nil (+ (arch::target-misc-data-offset arch) (ash index-known-fixnum 1)))
                     (! scale-16bit-misc-index idx-reg unscaled-idx))
                   (if is-signed
                     (! misc-ref-s16 temp src idx-reg)
                     (! misc-ref-u16 temp src idx-reg))))
               (! box-fixnum target temp))))
          (is-64-bit
           (case type-keyword
             (:double-float-vector
              (with-fp-target () (fp-val :double-float)
                (if (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-double))
                  (setq fp-val vreg))
                (if (and index-known-fixnum (<= index-known-fixnum (arch::target-max-64-bit-constant-index arch)))
                  (! misc-ref-c-double-float fp-val src index-known-fixnum)
                  (with-imm-target () idx-reg
                    (if index-known-fixnum
                      (unless unscaled-idx
                        (setq unscaled-idx idx-reg)
                        (arm642-absolute-natural seg unscaled-idx nil (ash index-known-fixnum arm64::fixnumshift))))
                    (! misc-ref-double-float fp-val src unscaled-idx)))
                (if (eq vreg-class hard-reg-class-fpr)
                  (<- fp-val)
                  (ensuring-node-target (target vreg)
                    (! double->heap target fp-val)))))
             (:complex-single-float-vector
              (with-fp-target () (fp-val :complex-single-float)
                (if (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-complex-single-float))
                  (setq fp-val vreg))
                (if (and index-known-fixnum (<= index-known-fixnum (arch::target-max-64-bit-constant-index arch)))
                  (! misc-ref-c-double-float fp-val src index-known-fixnum)
                  (with-imm-target () idx-reg
                    (if index-known-fixnum
                      (unless unscaled-idx
                        (setq unscaled-idx idx-reg)
                        (arm642-absolute-natural seg unscaled-idx nil (ash index-known-fixnum arm64::fixnumshift))))
                    (! misc-ref-double-float fp-val src unscaled-idx)))
                (if (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-complex-single-float))
                  (<- fp-val)
                  (ensuring-node-target (target vreg)
                    (! complex-single-float->node target fp-val)))))))
          (is-128-bit
              (with-fp-target () (fp-val :complex-double-float)
                (if (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-complex-double-float))
                  (setq fp-val vreg)
                  (with-imm-target () idx-reg
                    (if index-known-fixnum
                      (unless unscaled-idx
                        (setq unscaled-idx idx-reg)
                        (arm642-absolute-natural seg unscaled-idx nil (ash index-known-fixnum arm64::fixnumshift))))
                    (! misc-ref-complex-double-float fp-val src unscaled-idx)))
                (if (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-complex-double-float))
                  (<- fp-val)
                  (ensuring-node-target (target vreg)
                    (! complex-double-float->heap target fp-val)))))
          (t
           (unless is-1-bit
             (nx-error "~& unsupported vector type: ~s"
                       type-keyword))
           (ensuring-node-target (target vreg)
             (if (and index-known-fixnum (<= index-known-fixnum (arch::target-max-1-bit-constant-index arch)))
               (! misc-ref-c-bit-fixnum target src index-known-fixnum)
               (with-imm-temps () (word-index bitnum)
                 (if index-known-fixnum
                   (progn
                     (arm642-lri seg word-index (+ (arch::target-misc-data-offset arch) (ash index-known-fixnum -5)))
                     (arm642-lri seg bitnum (logand index-known-fixnum #x1f)))
                   (! scale-1bit-misc-index word-index bitnum unscaled-idx))
                 (let* ((dest word-index))
                   (! misc-ref-u32 dest src word-index)
                   (! extract-variable-bit-fixnum target dest bitnum)))))))))
    (^)))


;;; safe = T means assume "vector" is miscobj, do bounds check.
;;; safe = fixnum means check that subtag of vector = "safe" and do
;;;        bounds check.
;;; safe = nil means crash&burn.
(defun arm642-vref (seg vreg xfer type-keyword vector index safe)
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (let* ((index-known-fixnum (acode-fixnum-form-p index))
           (unscaled-idx nil)
           (src nil))
      (if (or safe (not index-known-fixnum))
        (multiple-value-setq (src unscaled-idx)
          (arm642-two-untargeted-reg-forms seg vector arm64::arg_y index arm64::arg_z))
        (setq src (arm642-one-untargeted-reg-form seg vector arm64::arg_z)))
      (when safe
        (if (typep safe 'fixnum)
          (! trap-unless-typecode= src safe))
        (unless index-known-fixnum
          (! trap-unless-fixnum unscaled-idx))
        (! check-misc-bound unscaled-idx src))
      (arm642-vref1 seg vreg xfer type-keyword src unscaled-idx index-known-fixnum))))

(defun arm642-1d-vref (seg vreg xfer type-keyword vector index safe)
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (let* ((simple-case (backend-get-next-label))
           (common-case (backend-get-next-label)))
      (multiple-value-bind (src unscaled-idx)
          (arm642-two-untargeted-reg-forms seg vector ($ arm64::arg_y) index ($ arm64::arg_z))
        (with-crf-target () crf
          (! set-z-if-vector-header crf src)
          (arm642-branch seg (arm642-make-compound-cd simple-case 0) crf arm64::arm64-cond-eq nil)
          (when safe
            (! trap-unless-fixnum unscaled-idx)
            (! check-vector-header-bound src unscaled-idx)
            (when (typep safe 'fixnum)
              (! trap-unless-vector-type src safe)))
          (! deref-vector-header src unscaled-idx)
          (-> common-case)
          (@ simple-case)
          (when safe
            (if (typep safe 'fixnum)
              (! trap-unless-simple-1d-array src safe))
            (! trap-unless-fixnum unscaled-idx)
            (! check-misc-bound unscaled-idx src))
          (@ common-case)
          (arm642-vref1 seg vreg xfer type-keyword src unscaled-idx nil))))))


(defun arm642-aset2-via-gvset (seg vreg xfer array i j new safe type-keyword constval &optional (simple t))
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (let* ((i-known-fixnum (acode-fixnum-form-p i))
           (j-known-fixnum (acode-fixnum-form-p j))
           (src ($ arm64::temp0))
           (unscaled-i ($ arm64::arg_x))
           (unscaled-j ($ arm64::arg_y))
           (val-reg ($ arm64::arg_z)))
      (arm642-four-targeted-reg-forms seg
                                    array src
                                    i unscaled-i
                                    j unscaled-j
                                    new val-reg)
      (when safe
        (when (typep safe 'fixnum)
          (with-node-target (src unscaled-i unscaled-j val-reg) expected
            (if simple
              (progn
                (! lri expected
                   (ash (dpb safe target::arrayH.flags-cell-subtag-byte
                             (ash 1 $arh_simple_bit))
                        arm64::fixnumshift))
                (! trap-unless-simple-array-2 src expected))
              (! trap-unless-typed-array-2 src safe))))
        (unless i-known-fixnum
          (! trap-unless-fixnum unscaled-i))
        (unless j-known-fixnum
          (! trap-unless-fixnum unscaled-j)))
      (with-imm-target () dim1
        (let* ((idx-reg ($ arm64::arg_y)))
          (progn
            (if safe
              (! check-2d-bound dim1 unscaled-i unscaled-j src)
              (! 2d-dim1 dim1 src))
            (! 2d-unscaled-index idx-reg dim1 unscaled-i unscaled-j))
          (let* ((v ($ arm64::arg_x)))
            (if simple
              (! array-data-vector-ref v src)
              (progn
                (arm642-copy-register seg v src)
                (! deref-vector-header v idx-reg)))
            (arm642-vset1 seg vreg xfer type-keyword v idx-reg nil val-reg (arm642-unboxed-reg-for-aset seg type-keyword val-reg safe constval) constval t)))))))

(defun arm642-aset2 (seg vreg xfer array i j new safe type-keyword dim0 dim1 &optional (simple t))
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (let* ((i-known-fixnum (acode-fixnum-form-p i))
           (j-known-fixnum (acode-fixnum-form-p j))
           (arch (backend-target-arch *target-backend*))
           (is-node (member type-keyword (arch::target-gvector-types arch)))
           (constval (arm642-constant-value-ok-for-type-keyword type-keyword new))
           (needs-memoization (and is-node (arm642-acode-needs-memoization new))))
      (if needs-memoization
        (arm642-aset2-via-gvset seg vreg xfer array i j new safe type-keyword constval simple)
        (let* ((constidx
                (and *arm642-reckless*
                     dim0 dim1 i-known-fixnum j-known-fixnum
                     (>= i-known-fixnum 0)
                     (>= j-known-fixnum 0)
                     (< i-known-fixnum dim0)
                     (< j-known-fixnum dim1)
                     (+ (* i-known-fixnum dim1) j-known-fixnum)))
               (val-reg (arm642-target-reg-for-aset vreg type-keyword))
               (node-val (if (node-reg-p val-reg) val-reg))
               (imm-val (if (imm-reg-p val-reg) val-reg)))
          (with-node-target (node-val) src
            (with-node-target (node-val src) unscaled-i
              (with-node-target (node-val src unscaled-i) unscaled-j
                (if constidx
                  (multiple-value-setq (src val-reg)
                    (arm642-two-untargeted-reg-forms seg array ($ arm64::temp0) new val-reg))
                  (multiple-value-setq (src unscaled-i unscaled-j val-reg)
                    (arm642-four-untargeted-reg-forms seg
                                                    array src
                                                    i unscaled-i
                                                    j unscaled-j
                                                    new val-reg)))
                (if (node-reg-p val-reg) (setq node-val val-reg))
                (if (imm-reg-p val-reg) (setq imm-val val-reg))
                (let* ((*available-backend-imm-temps* *available-backend-imm-temps*))
                  (when (and (= (hard-regspec-class val-reg) hard-reg-class-gpr)
                             (logbitp (hard-regspec-value val-reg)
                                      *backend-imm-temps*))
                    (use-imm-temp (hard-regspec-value val-reg)))
                  (when safe
                    (when (typep safe 'fixnum)
                      (with-node-target (src node-val unscaled-i unscaled-j) expected
                        (if simple
                          (progn
                            (! lri expected
                               (ash (dpb safe target::arrayH.flags-cell-subtag-byte
                                         (ash 1 $arh_simple_bit))
                                    arm64::fixnumshift))
                            (! trap-unless-simple-array-2 src expected))
                          (! trap-unless-typed-array-2 src safe))))
                    (unless i-known-fixnum
                      (! trap-unless-fixnum unscaled-i))
                    (unless j-known-fixnum
                      (! trap-unless-fixnum unscaled-j)))
                  (with-imm-target (imm-val) dim1
                    (with-node-target (src node-val) idx-reg
                      (unless constidx
                        (if safe
                          (! check-2d-bound dim1 unscaled-i unscaled-j src)
                          (! 2d-dim1 dim1 src))
                        (! 2d-unscaled-index idx-reg dim1 unscaled-i unscaled-j))
                      (with-node-target (idx-reg node-val) v
                        (if simple
                          (! array-data-vector-ref v src)
                          (progn
                            (setq v src)
                            (! deref-vector-header src idx-reg)))
                        (arm642-vset1 seg vreg xfer type-keyword
                                      v idx-reg constidx val-reg (arm642-unboxed-reg-for-aset seg type-keyword val-reg safe constval) constval needs-memoization)))))))))))))


(defun arm642-aset3 (seg vreg xfer array i j k new safe type-keyword dim0 dim1 dim2 &optional (simple t))
  (with-arm64-local-vinsn-macros (seg target)
    (let* ((i-known-fixnum (acode-fixnum-form-p i))
           (j-known-fixnum (acode-fixnum-form-p j))
           (k-known-fixnum (acode-fixnum-form-p k))
           (arch (backend-target-arch *target-backend*))
           (is-node (member type-keyword (arch::target-gvector-types arch)))
           (constval (arm642-constant-value-ok-for-type-keyword type-keyword new))
           (needs-memoization (and is-node (arm642-acode-needs-memoization new)))
           (src)
           (unscaled-i)
           (unscaled-j)
           (unscaled-k)
           (val-reg (arm642-target-reg-for-aset vreg type-keyword))
           (constidx
            (and *arm642-reckless*
                 (not needs-memoization) dim0 dim1 dim2 i-known-fixnum j-known-fixnum k-known-fixnum
                 (>= i-known-fixnum 0)
                 (>= j-known-fixnum 0)
                 (>= k-known-fixnum 0)
                 (< i-known-fixnum dim0)
                 (< j-known-fixnum dim1)
                 (< k-known-fixnum dim2)
                 (+ (* i-known-fixnum dim1 dim2)
                    (* j-known-fixnum dim2)
                    k-known-fixnum))))
      (progn
        (if constidx
          (multiple-value-setq (src val-reg)
            (arm642-two-targeted-reg-forms seg array ($ arm64::temp0) new val-reg))
          (progn
            (setq src ($ arm64::temp1)
                  unscaled-i ($ arm64::temp0)
                  unscaled-j ($ arm64::arg_x)
                  unscaled-k ($ arm64::arg_y))
            (arm642-push-register
             seg
             (arm642-one-untargeted-reg-form seg array ($ arm64::arg_z)))
            (arm642-four-targeted-reg-forms seg
                                          i ($ arm64::temp0)
                                          j ($ arm64::arg_x)
                                          k ($ arm64::arg_y)
                                          new val-reg)
            (arm642-pop-register seg src)))
        (let* ((*available-backend-imm-temps* *available-backend-imm-temps*))
          (when (and (= (hard-regspec-class val-reg) hard-reg-class-gpr)
                     (logbitp (hard-regspec-value val-reg)
                              *backend-imm-temps*))
            (use-imm-temp (hard-regspec-value val-reg)))
          (when safe
            (when (typep safe 'fixnum)
              (if simple
                (let* ((expected (if constidx
                                   (with-node-target (src val-reg) expected
                                     expected)
                                   (with-node-target (src unscaled-i unscaled-j unscaled-k val-reg) expected
                                     expected))))
                  (! lri expected (ash (dpb safe target::arrayH.flags-cell-subtag-byte
                                            (ash 1 $arh_simple_bit))
                                       arm64::fixnumshift))
                  (! trap-unless-simple-array-3 src expected))
                (! trap-unless-typed-array-3 src safe)))
            (unless i-known-fixnum
              (! trap-unless-fixnum unscaled-i))
            (unless j-known-fixnum
              (! trap-unless-fixnum unscaled-j))
            (unless k-known-fixnum
              (! trap-unless-fixnum unscaled-k)))
          (with-imm-target () dim1
            (with-imm-target (dim1) dim2
              (let* ((idx-reg ($ arm64::arg_y)))
                (unless constidx
                  (if safe
                    (! check-3d-bound dim1 dim2 unscaled-i unscaled-j unscaled-k src)
                    (! 3d-dims dim1 dim2 src))
                  (! 3d-unscaled-index idx-reg dim1 dim2 unscaled-i unscaled-j unscaled-k))
                (let* ((v ($ arm64::arg_x)))
                  (if simple
                    (! array-data-vector-ref v src)
                    (progn
                      (arm642-copy-register seg v src)
                      (! deref-vector-header v idx-reg v idx-reg)))
                  (arm642-vset1 seg vreg xfer type-keyword v idx-reg constidx val-reg (arm642-unboxed-reg-for-aset seg type-keyword val-reg safe constval) constval needs-memoization))))))))))

(defun arm642-aref2 (seg vreg xfer array i j safe typekeyword &optional dim0 dim1 (simple t))
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (let* ((i-known-fixnum (acode-fixnum-form-p i))
           (j-known-fixnum (acode-fixnum-form-p j))
           (src)
           (unscaled-i)
           (unscaled-j)
           (constidx
            (and *arm642-reckless*
                 dim0 dim1 i-known-fixnum j-known-fixnum
                 (>= i-known-fixnum 0)
                 (>= j-known-fixnum 0)
                 (< i-known-fixnum dim0)
                 (< j-known-fixnum dim1)
                 (+ (* i-known-fixnum dim1) j-known-fixnum))))
      (if constidx
        (setq src (arm642-one-targeted-reg-form seg array ($ arm64::arg_z)))
        (multiple-value-setq (src unscaled-i unscaled-j)
          (arm642-three-untargeted-reg-forms seg
                                           array arm64::arg_x
                                           i arm64::arg_y
                                           j arm64::arg_z)))
      (when safe
        (when (typep safe 'fixnum)
          (let* ((*available-backend-node-temps* *available-backend-node-temps*))
            (when unscaled-i
              (setq *available-backend-node-temps* (logandc2 *available-backend-node-temps*
                                                             (ash 1 (hard-regspec-value unscaled-i)))))
            (when unscaled-j
              (setq *available-backend-node-temps* (logandc2 *available-backend-node-temps*
                                                             (ash 1 (hard-regspec-value unscaled-j)))))
            (with-node-target (src) expected
              (if simple
                (progn
                  (! lri expected (ash (dpb safe target::arrayH.flags-cell-subtag-byte
                                            (ash 1 $arh_simple_bit))
                                       arm64::fixnumshift))
                  (! trap-unless-simple-array-2 src expected))
                (! trap-unless-typed-array-2 src safe)))))
        (unless i-known-fixnum
          (! trap-unless-fixnum unscaled-i))
        (unless j-known-fixnum
          (! trap-unless-fixnum unscaled-j)))
      (with-node-target (src) idx-reg
        (with-imm-target () dim1
          (unless constidx
            (if safe
              (! check-2d-bound dim1 unscaled-i unscaled-j src)
              (! 2d-dim1 dim1 src))
            (! 2d-unscaled-index idx-reg dim1 unscaled-i unscaled-j))
          (with-node-target (idx-reg src) v
            (if simple
              (! array-data-vector-ref v src)
              (progn
                (setq v src)
                (! deref-vector-header src idx-reg)))
            (arm642-vref1 seg vreg xfer typekeyword v idx-reg constidx)))))))



(defun arm642-aref3 (seg vreg xfer array i j k safe typekeyword dim0 dim1 dim2 &optional (simple t))
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (let* ((i-known-fixnum (acode-fixnum-form-p i))
           (j-known-fixnum (acode-fixnum-form-p j))
           (k-known-fixnum (acode-fixnum-form-p k))
           (src)
           (unscaled-i)
           (unscaled-j)
           (unscaled-k)
           (constidx
            (and *arm642-reckless*
                 dim0 dim1 i-known-fixnum j-known-fixnum k-known-fixnum
                 (>= i-known-fixnum 0)
                 (>= j-known-fixnum 0)
                 (>= k-known-fixnum 0)
                 (< i-known-fixnum dim0)
                 (< j-known-fixnum dim1)
                 (< k-known-fixnum dim2)
                 (+ (* i-known-fixnum dim1 dim2)
                    (* j-known-fixnum dim2)
                    k-known-fixnum))))
      (if constidx
        (setq src (arm642-one-targeted-reg-form seg array ($ arm64::arg_z)))
        (multiple-value-setq (src unscaled-i unscaled-j unscaled-k)
          (arm642-four-untargeted-reg-forms seg
                                           array arm64::temp0
                                           i arm64::arg_x
                                           j arm64::arg_y
                                           k arm64::arg_z)))
      (when safe
        (when (typep safe 'fixnum)
          (if simple
            (let* ((expected (if constidx
                               (with-node-target (src) expected
                                 expected)
                               (with-node-target (src unscaled-i unscaled-j unscaled-k) expected
                                 expected))))
              (! lri expected (ash (dpb safe target::arrayH.flags-cell-subtag-byte
                                        (ash 1 $arh_simple_bit))
                                   arm64::fixnumshift))
              (! trap-unless-simple-array-3 src expected))
            (! trap-unless-typed-array-3 src safe)))
        (unless i-known-fixnum
          (! trap-unless-fixnum unscaled-i))
        (unless j-known-fixnum
          (! trap-unless-fixnum unscaled-j))
        (unless k-known-fixnum
          (! trap-unless-fixnum unscaled-k)))
      (with-node-target (src) idx-reg
        (with-imm-target () dim1
          (with-imm-target (dim1) dim2
            (unless constidx
              (if safe
                (! check-3d-bound dim1 dim2 unscaled-i unscaled-j unscaled-k src)
                (! 3d-dims dim1 dim2 src))
              (! 3d-unscaled-index idx-reg dim1 dim2 unscaled-i unscaled-j unscaled-k))))
        (with-node-target (idx-reg) v
          (if simple
            (! array-data-vector-ref v src)
            (progn
              (arm642-copy-register seg v src)
              (! deref-vector-header v idx-reg)))
          (arm642-vref1 seg vreg xfer typekeyword v idx-reg constidx))))))


(defun arm642-constant-value-ok-for-type-keyword (type-keyword form)
  (if (and (acode-p (setq form (acode-unwrapped-form form)))
           (or (eq (acode-operator form) (%nx1-operator immediate))
               (eq (acode-operator form) (%nx1-operator fixnum))))
    (let* ((val (car (acode-operands form)))
           (typep (cond ((eq type-keyword :signed-32-bit-vector)
                         (typep val '(signed-byte 32)))
                        ((eq type-keyword :single-float-vector)
                         (typep val 'short-float))
                        ((eq type-keyword :double-float-vector)
                         (typep val 'double-float))
                        ((eq type-keyword :simple-string)
                         (typep val 'base-char))
                        ((eq type-keyword :signed-8-bit-vector)
                         (typep val '(signed-byte 8)))
                        ((eq type-keyword :unsigned-8-bit-vector)
                         (typep val '(unsigned-byte 8)))
                        ((eq type-keyword :signed-16-bit-vector)
                         (typep val '(signed-byte 16)))
                        ((eq type-keyword :unsigned-16-bit-vector)
                         (typep val '(unsigned-byte 16)))
                        ((eq type-keyword :bit-vector)
                         (typep val 'bit)))))
      (if typep val))))

(defun arm642-target-reg-for-aset (vreg type-keyword)
  (let* ((arch (backend-target-arch *target-backend*))
         (is-node (member type-keyword (arch::target-gvector-types arch)))
         (is-1-bit (member type-keyword (arch::target-1-bit-ivector-types arch)))
         (is-8-bit (member type-keyword (arch::target-8-bit-ivector-types arch)))
         (is-16-bit (member type-keyword (arch::target-16-bit-ivector-types arch)))
         (is-32-bit (member type-keyword (arch::target-32-bit-ivector-types arch)))
         (is-64-bit (member type-keyword (arch::target-64-bit-ivector-types arch)))
         (is-128-bit (eq type-keyword :complex-double-float-vector))
         (is-signed (member type-keyword '(:signed-8-bit-vector :signed-16-bit-vector :signed-32-bit-vector :signed-64-bit-vector :fixnum-vector)))
         (vreg-class (if vreg (hard-regspec-class vreg)))
         (vreg-mode (if (or (eql vreg-class hard-reg-class-gpr)
                            (eql vreg-class hard-reg-class-fpr))
                      (get-regspec-mode vreg)))
         (next-imm-target (available-imm-temp *available-backend-imm-temps*))
         (acc (make-wired-lreg arm64::arg_z)))
    (cond ((or is-node
               is-1-bit
               (eq type-keyword :simple-string)
               (eq type-keyword :fixnum-vector)
               (and (eql vreg-class hard-reg-class-gpr)
                    (eql vreg-mode hard-reg-class-gpr-mode-node)))
           acc)
          ((null vreg)
           (cond (is-64-bit
                  (ecase type-keyword
                    (:double-float-vector (available-fp-temp *available-backend-fp-temps* :double-float))
                    (:complex-single-float-vector (available-fp-temp *available-backend-fp-temps* :complex-single-float))))
                 (is-128-bit
                  (available-fp-temp *available-backend-fp-temps* :complex-double-float))
                 (is-32-bit
                  (if (eq type-keyword :single-float-vector)
                    (available-fp-temp *available-backend-fp-temps* :single-float)
                    (make-unwired-lreg next-imm-target :mode (if is-signed hard-reg-class-gpr-mode-s32 hard-reg-class-gpr-mode-u32))))
                 (is-16-bit
                  (make-unwired-lreg next-imm-target :mode (if is-signed hard-reg-class-gpr-mode-s16 hard-reg-class-gpr-mode-u16)))
                 (is-8-bit
                  (make-unwired-lreg next-imm-target :mode (if is-signed hard-reg-class-gpr-mode-s8 hard-reg-class-gpr-mode-u8)))
                 (t "Bug: can't determine operand size for ~s" type-keyword)))
          (t
           (let* ((lreg (if vreg-mode
                          (make-unwired-lreg (lreg-value vreg)))))
             (if
               (cond
                 (is-64-bit
                  (if (eq type-keyword :double-float-vector)
                    (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-double))))
                 (is-32-bit
                  (if (eq type-keyword :single-float-vector)
                    (and (eql vreg-class hard-reg-class-fpr)
                         (eql vreg-mode hard-reg-class-fpr-mode-single))
                    (if is-signed
                      (and (eql vreg-class hard-reg-class-gpr)
                           (or (eql vreg-mode hard-reg-class-gpr-mode-s32)
                               (eql vreg-mode hard-reg-class-gpr-mode-s64)))
                      (and (eql vreg-class hard-reg-class-gpr)
                           (or (eql vreg-mode hard-reg-class-gpr-mode-u32)
                               (eql vreg-mode hard-reg-class-gpr-mode-u64)
                               (eql vreg-mode hard-reg-class-gpr-mode-s64))))))
                 (is-16-bit
                  (if is-signed
                    (and (eql vreg-class hard-reg-class-gpr)
                         (or (eql vreg-mode hard-reg-class-gpr-mode-s16)
                             (eql vreg-mode hard-reg-class-gpr-mode-s32)
                             (eql vreg-mode hard-reg-class-gpr-mode-s64)))
                    (and (eql vreg-class hard-reg-class-gpr)
                         (or (eql vreg-mode hard-reg-class-gpr-mode-u16)
                             (eql vreg-mode hard-reg-class-gpr-mode-u32)
                             (eql vreg-mode hard-reg-class-gpr-mode-u64)
                             (eql vreg-mode hard-reg-class-gpr-mode-s32)
                             (eql vreg-mode hard-reg-class-gpr-mode-s64)))))
                 (t
                  (if is-signed
                    (and (eql vreg-class hard-reg-class-gpr)
                         (or (eql vreg-mode hard-reg-class-gpr-mode-s8)
                             (eql vreg-mode hard-reg-class-gpr-mode-s16)
                             (eql vreg-mode hard-reg-class-gpr-mode-s32)
                             (eql vreg-mode hard-reg-class-gpr-mode-s64)))
                    (and (eql vreg-class hard-reg-class-gpr)
                         (or (eql vreg-mode hard-reg-class-gpr-mode-u8)
                             (eql vreg-mode hard-reg-class-gpr-mode-u16)
                             (eql vreg-mode hard-reg-class-gpr-mode-u32)
                             (eql vreg-mode hard-reg-class-gpr-mode-u64)
                             (eql vreg-mode hard-reg-class-gpr-mode-s16)
                             (eql vreg-mode hard-reg-class-gpr-mode-s32)
                             (eql vreg-mode hard-reg-class-gpr-mode-s64))))))
               lreg
               acc))))))



(defun arm642-unboxed-reg-for-aset (seg type-keyword result-reg safe constval)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((arch (backend-target-arch *target-backend*))
           (is-node (member type-keyword (arch::target-gvector-types arch)))
           (is-8-bit (member type-keyword (arch::target-8-bit-ivector-types arch)))
           (is-16-bit (member type-keyword (arch::target-16-bit-ivector-types arch)))
           (is-32-bit (member type-keyword (arch::target-32-bit-ivector-types arch)))
           (is-64-bit (member type-keyword (arch::target-64-bit-ivector-types arch)))
           (is-128-bit (eq type-keyword :complex-double-float-vector))
           (is-signed (member type-keyword '(:signed-8-bit-vector :signed-16-bit-vector :signed-32-bit-vector :signed-64-bit-vector :fixnum-vector)))
           (result-is-node-gpr (and (eql (hard-regspec-class result-reg)
                                         hard-reg-class-gpr)
                                    (eql (get-regspec-mode result-reg)
                                         hard-reg-class-gpr-mode-node)))
           (next-imm-target (available-imm-temp *available-backend-imm-temps*)))
      (if (or is-node (not result-is-node-gpr))
        result-reg
        (cond (is-128-bit
               (let* ((reg (available-fp-temp *available-backend-fp-temps* :complex-double-float)))
                 (when reg
                   (! trap-unless-typecode= result-reg arm64::subtag-complex-double-float))
                 (! get-complex-double-float reg result-reg)
                 reg))
              (is-64-bit
               (case type-keyword
                 (:double-float-vector
                  (let* ((reg (available-fp-temp *available-backend-fp-temps* :double-float)))
                    (if safe
                      (! get-double? reg result-reg)
                      (! get-double reg result-reg))
                    reg))
                 (:complex-single-float-vector
                  (let* ((reg (available-fp-temp *available-backend-fp-temps* :complex-single-float)))
                    (when safe
                      (! trap-unless-typecode= result-reg arm64::subtag-complex-single-float))
                    (! get-complex-single-float reg result-reg)
                    reg))))
              (is-32-bit
               (if is-signed
                 (let* ((reg (make-unwired-lreg next-imm-target :mode hard-reg-class-gpr-mode-s32)))
                   (if (eq type-keyword :fixnum-vector)
                     (progn
                       (when safe
                         (! trap-unless-fixnum result-reg))
                       (! fixnum->signed-natural reg result-reg))
                     (! unbox-s32 reg result-reg))
                   reg)
                 (let* ((reg (make-unwired-lreg next-imm-target :mode hard-reg-class-gpr-mode-u32)))
                   (cond ((eq type-keyword :simple-string)
                          (if (characterp constval)
                            (arm642-lri seg reg (char-code constval))
                            (! unbox-base-char reg result-reg)))
                         ((eq type-keyword :single-float-vector)
                          (if (typep constval 'single-float)
                            (arm642-lri seg reg (single-float-bits constval))
                            (progn
                              (when safe
                                (! trap-unless-single-float result-reg))
                              (! single-float-bits reg result-reg))))
                         (t
                          (if (typep constval '(unsigned-byte 32))
                            (arm642-lri seg reg constval)
                            (! unbox-u32 reg result-reg))))
                   reg)))
              (is-16-bit
               (if is-signed
                 (let* ((reg (make-unwired-lreg next-imm-target :mode hard-reg-class-gpr-mode-s16)))
                   (if (typep constval '(signed-byte 16))
                     (arm642-lri seg reg constval)
                     (! unbox-s16 reg result-reg))
                   reg)
                 (let* ((reg (make-unwired-lreg next-imm-target :mode hard-reg-class-gpr-mode-u16)))
                   (if (typep constval '(unsigned-byte 16))
                     (arm642-lri seg reg constval)
                     (! unbox-u16 reg result-reg))
                   reg)))
              (is-8-bit
               (if is-signed
                 (let* ((reg (make-unwired-lreg next-imm-target :mode hard-reg-class-gpr-mode-s8)))
                   (if (typep constval '(signed-byte 8))
                     (arm642-lri seg reg constval)
                     (! unbox-s8 reg result-reg))
                   reg)
                 (let* ((reg (make-unwired-lreg next-imm-target :mode hard-reg-class-gpr-mode-u8)))
                   (if (typep constval '(unsigned-byte 8))
                     (arm642-lri seg reg constval)
                     (! unbox-u8 reg result-reg))
                   reg)))
              (t
               (let* ((reg (make-unwired-lreg next-imm-target :mode hard-reg-class-gpr-mode-u8)))
                 (unless (typep constval 'bit)
                   (! unbox-bit reg result-reg))
                 reg)))))))


;;; "val-reg" might be boxed, if the vreg requires it to be.
(defun arm642-vset1 (seg vreg xfer type-keyword src unscaled-idx index-known-fixnum val-reg unboxed-val-reg constval &optional (node-value-needs-memoization t))
  (with-arm64-local-vinsn-macros (seg vreg xfer)
    (let* ((arch (backend-target-arch *target-backend*))
           (is-node (member type-keyword (arch::target-gvector-types arch)))
           (is-1-bit (member type-keyword (arch::target-1-bit-ivector-types arch)))
           (is-8-bit (member type-keyword (arch::target-8-bit-ivector-types arch)))
           (is-16-bit (member type-keyword (arch::target-16-bit-ivector-types arch)))
           (is-32-bit (member type-keyword (arch::target-32-bit-ivector-types arch)))
           (is-64-bit (member type-keyword (arch::target-64-bit-ivector-types arch)))
           (is-128-bit (eq type-keyword :complex-double-float-vector))
           (is-signed (member type-keyword '(:signed-8-bit-vector :signed-16-bit-vector :signed-32-bit-vector :signed-64-bit-vector :fixnum-vector))))
      (cond ((and is-node node-value-needs-memoization)
             (unless (and (eql (hard-regspec-value src) arm64::arg_x)
                          (eql (hard-regspec-value unscaled-idx) arm64::arg_y)
                          (eql (hard-regspec-value val-reg) arm64::arg_z))
               (compiler-bug "Bug: invalid register targeting for gvset: ~s" (list src unscaled-idx val-reg)))
             (! call-subprim-3 val-reg (arm64::arm64-subprimitive-offset '.SPgvset) src unscaled-idx val-reg))
            (is-node
             (if (and index-known-fixnum (<= index-known-fixnum
                                             (arch::target-max-32-bit-constant-index arch)))
               (! misc-set-c-node val-reg src index-known-fixnum)
               (with-imm-target () scaled-idx
                 (if index-known-fixnum
                   (arm642-absolute-natural seg scaled-idx nil (+ (arch::target-misc-data-offset arch) (ash index-known-fixnum *arm642-target-node-shift*)))
                   (! scale-node-misc-index scaled-idx unscaled-idx))
                 (! misc-set-node val-reg src scaled-idx))))
            (t
             (cond
               (is-128-bit
                (with-imm-target () scaled-idx
                  (if index-known-fixnum
                    (unless unscaled-idx
                      (setq unscaled-idx scaled-idx)
                      (arm642-absolute-natural seg unscaled-idx nil (ash index-known-fixnum arm64::fixnumshift))))
                  (! misc-set-complex-double-float unboxed-val-reg src unscaled-idx)))
               (is-64-bit
                (with-imm-target (arm64::imm0 arm64::imm1) scaled-idx
                  (if (and index-known-fixnum
                           (<= index-known-fixnum
                               (arch::target-max-64-bit-constant-index arch)))
                    (! misc-set-c-double-float unboxed-val-reg src index-known-fixnum)
                    (progn
                      (if index-known-fixnum
                        (unless unscaled-idx
                          (setq unscaled-idx scaled-idx)
                          (arm642-absolute-natural seg unscaled-idx nil (ash index-known-fixnum arm64::fixnumshift))))
                      (! misc-set-double-float unboxed-val-reg src unscaled-idx)))))
               (t
                (with-imm-target (unboxed-val-reg) scaled-idx
                  (cond
                    (is-32-bit
                     (if (and index-known-fixnum
                              (<= index-known-fixnum
                                  (if (and (eq type-keyword :single-float-vector)
                                           (eq (hard-regspec-class unboxed-val-reg)
                                               hard-reg-class-fpr))
                                    255
                                    (arch::target-max-32-bit-constant-index arch))))
                       (if (eq type-keyword :single-float-vector)
                         (if (eq (hard-regspec-class unboxed-val-reg)
                                 hard-reg-class-fpr)
                           (! misc-set-c-single-float unboxed-val-reg src index-known-fixnum)
                           (! misc-set-c-u32 unboxed-val-reg src index-known-fixnum))
                         (if is-signed
                           (! misc-set-c-s32 unboxed-val-reg src index-known-fixnum)
                           (! misc-set-c-u32 unboxed-val-reg src index-known-fixnum)))
                       (progn
                         (if index-known-fixnum
                           (arm642-absolute-natural seg scaled-idx nil (+ (arch::target-misc-data-offset arch) (ash index-known-fixnum 2)))
                           (! scale-32bit-misc-index scaled-idx unscaled-idx))
                         (if (and (eq type-keyword :single-float-vector)
                                  (eql (hard-regspec-class unboxed-val-reg)
                                       hard-reg-class-fpr))
                           (! misc-set-single-float unboxed-val-reg src scaled-idx)
                           (if is-signed
                             (! misc-set-s32 unboxed-val-reg src scaled-idx)
                             (! misc-set-u32 unboxed-val-reg src scaled-idx))))))
                    (is-16-bit
                     (if (and index-known-fixnum
                              (<= index-known-fixnum
                                  (arch::target-max-16-bit-constant-index arch)))
                       (if is-signed
                         (! misc-set-c-s16 unboxed-val-reg src index-known-fixnum)
                         (! misc-set-c-u16 unboxed-val-reg src index-known-fixnum))
                       (progn
                         (if index-known-fixnum
                           (arm642-absolute-natural seg scaled-idx nil (+ (arch::target-misc-data-offset arch) (ash index-known-fixnum 1)))
                           (! scale-16bit-misc-index scaled-idx unscaled-idx))
                         (if is-signed
                           (! misc-set-s16 unboxed-val-reg src scaled-idx)
                           (! misc-set-u16 unboxed-val-reg src scaled-idx)))))
                    (is-8-bit
                     (if (and index-known-fixnum
                              (<= index-known-fixnum
                                  (arch::target-max-8-bit-constant-index arch)))
                       (if is-signed
                         (! misc-set-c-s8 unboxed-val-reg src index-known-fixnum)
                         (! misc-set-c-u8 unboxed-val-reg src index-known-fixnum))
                       (progn
                         (if index-known-fixnum
                           (arm642-absolute-natural seg scaled-idx nil (+ (arch::target-misc-data-offset arch) index-known-fixnum))
                           (! scale-8bit-misc-index scaled-idx unscaled-idx))
                         (if is-signed
                           (! misc-set-s8 unboxed-val-reg src scaled-idx)
                           (! misc-set-u8 unboxed-val-reg src scaled-idx)))))
                    (t
                     (unless is-1-bit
                       (nx-error "~& unsupported vector type: ~s"
                                 type-keyword))
                     (if (and index-known-fixnum (<= index-known-fixnum (arch::target-max-1-bit-constant-index arch)))
                       (with-imm-target (unboxed-val-reg) word
                         (let* ((word-index (ash index-known-fixnum -5))
                                (bit-number (logand index-known-fixnum #x1f)))
                           (! misc-ref-c-u32 word src word-index)
                           (if constval
                             (if (zerop constval)
                               (! set-constant-bit-to-0 word word bit-number)
                               (! set-constant-bit-to-1 word word bit-number))
                             (! set-constant-bit-to-variable-value word word unboxed-val-reg bit-number))
                           (! misc-set-c-u32 word src word-index)))
                       (with-crf-target () crf
                         (with-imm-temps () (word-index bit-number temp)
                           (unless constval
                             (! compare-immediate crf unboxed-val-reg 0))
                           (! scale-1bit-misc-index word-index bit-number unscaled-idx)
                           (! lri temp 1)
                           (! shift-left-variable-word bit-number temp bit-number)
                           (! misc-ref-u32 temp src word-index)
                           (if constval
                             (if (zerop constval)
                               (! u32logandc2 temp temp bit-number)
                               (! u32logior temp temp bit-number))
                             (progn
                               (! set-or-clear-bit temp temp bit-number crf)))
                           (! misc-set-u32 temp src word-index)))))))))))
      (when (and vreg val-reg) (<- val-reg))
    (^))))

(defun arm642-code-coverage-entry (seg note)
  (let* ((afunc *arm642-cur-afunc*))
    (setf (afunc-bits afunc) (%ilogior (afunc-bits afunc) (ash 1 $fbitccoverage)))
    (with-arm64-local-vinsn-macros (seg)
      (let* ((ccreg ($ arm64::temp0)))
        (arm642-store-immediate seg note ccreg)
        (with-node-temps (ccreg) (zero)
          (! lri zero 0)
          (! misc-set-c-node zero ccreg 1))))))

(defun arm642-vset (seg vreg xfer type-keyword vector index value safe)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((arch (backend-target-arch *target-backend*))
           (is-node (member type-keyword (arch::target-gvector-types arch)))
           (constval (arm642-constant-value-ok-for-type-keyword type-keyword value))
           (needs-memoization (and is-node (arm642-acode-needs-memoization value)))
           (index-known-fixnum (acode-fixnum-form-p index)))
      (let* ((src ($ arm64::arg_x))
             (unscaled-idx ($ arm64::arg_y))
             (result-reg ($ arm64::arg_z)))
        (cond (needs-memoization
               (arm642-three-targeted-reg-forms seg
                                              vector src
                                              index unscaled-idx
                                              value result-reg))
              (t
               (if (and (not safe) index-known-fixnum)
                 (multiple-value-setq (src result-reg unscaled-idx)
                   (arm642-two-untargeted-reg-forms seg
                                                  vector src
                                                  value (arm642-target-reg-for-aset vreg type-keyword)))
                 (multiple-value-setq (src unscaled-idx result-reg)
                   (arm642-three-untargeted-reg-forms seg
                                                    vector src
                                                    index unscaled-idx
                                                    value (arm642-target-reg-for-aset vreg type-keyword))))))
        (when safe
          (let* ((*available-backend-imm-temps* *available-backend-imm-temps*)
                 (value (if (eql (hard-regspec-class result-reg)
                                 hard-reg-class-gpr)
                          (hard-regspec-value result-reg))))
            (when (and value (logbitp value *available-backend-imm-temps*))
              (setq *available-backend-imm-temps* (bitclr value *available-backend-imm-temps*)))
            (if (typep safe 'fixnum)
              (! trap-unless-typecode= src safe))
            (unless index-known-fixnum
              (! trap-unless-fixnum unscaled-idx))
            (! check-misc-bound unscaled-idx src)))
        (arm642-vset1 seg vreg xfer type-keyword src unscaled-idx index-known-fixnum result-reg (arm642-unboxed-reg-for-aset seg type-keyword result-reg safe constval) constval needs-memoization)))))

(defun arm642-1d-vset (seg vreg xfer type-keyword vector index value safe)
  (with-arm64-local-vinsn-macros (seg)
    (let* ((arch (backend-target-arch *target-backend*))
           (simple-case (backend-get-next-label))
           (common-case (backend-get-next-label))
           (is-node (member type-keyword (arch::target-gvector-types arch)))
           (constval (arm642-constant-value-ok-for-type-keyword type-keyword value))
           (needs-memoization (and is-node (arm642-acode-needs-memoization value)))
           (index-known-fixnum (acode-fixnum-form-p index)))
      (let* ((src ($ arm64::arg_x))
             (unscaled-idx ($ arm64::arg_y))
             (result-reg ($ arm64::arg_z)))
        (cond (needs-memoization
               (arm642-three-targeted-reg-forms seg
                                              vector src
                                              index unscaled-idx
                                              value result-reg))
              (t
               (multiple-value-setq (src unscaled-idx result-reg)
                   (arm642-three-untargeted-reg-forms seg
                                                    vector src
                                                    index unscaled-idx
                                                    value (arm642-target-reg-for-aset vreg type-keyword)))))
        (let* ((*available-backend-imm-temps* *available-backend-imm-temps*)
               (value (if (eql (hard-regspec-class result-reg)
                                 hard-reg-class-gpr)
                          (hard-regspec-value result-reg))))
            (when (and value (logbitp value *available-backend-imm-temps*))
              (setq *available-backend-imm-temps* (bitclr value *available-backend-imm-temps*)))
          (with-crf-target () crf
            (! set-z-if-vector-header crf src)
            (arm642-branch seg (arm642-make-compound-cd simple-case 0) crf arm64::arm64-cond-eq nil))
          (when safe
            (! trap-unless-fixnum unscaled-idx)
            (! check-vector-header-bound src unscaled-idx)
            (when (typep safe 'fixnum)
              (! trap-unless-vector-type src safe)))
          (! deref-vector-header src unscaled-idx)
          (-> common-case)
          (@ simple-case)
          (when safe
            (if (typep safe 'fixnum)
              (! trap-unless-simple-1d-array src safe))
            (! trap-unless-fixnum unscaled-idx)
            (! check-misc-bound unscaled-idx src))
          (@ common-case)
          (arm642-vset1 seg vreg xfer type-keyword src unscaled-idx index-known-fixnum result-reg (arm642-unboxed-reg-for-aset seg type-keyword result-reg safe constval) constval needs-memoization))))))
