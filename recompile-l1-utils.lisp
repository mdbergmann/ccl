;;; Recompile just l1-utils.lisp for ARM64 via the cross-compile mechanism
;;; Usage: ./dx86cl64 -l recompile-l1-utils.lisp
(in-package :ccl)

(setq *batch-flag* t)

;;; Step 1: Load systems (adds ARM64 module definitions)
(compile-file "ccl:lib;systems.lisp" :output-file "ccl:bin;systems.dx64fsl" :verbose nil)
(load "ccl:bin;systems.dx64fsl" :verbose nil)

;;; Step 2: Compile and load ARM64 modules
(flet ((cl (src)
         (let* ((fasl (merge-pathnames (make-pathname :type "dx64fsl") src)))
           (compile-file src :output-file fasl :verbose nil :load t))))
  (cl "ccl:compiler;ARM64;arm64-arch.lisp")
  (provide "ARM64-ARCH")
  (cl "ccl:lib;arm64env.lisp")
  (provide "ARM64ENV")
  (cl "ccl:compiler;ARM64;arm64-asm.lisp")
  (provide "ARM64-ASM")
  (cl "ccl:compiler;risc-lap.lisp")
  (cl "ccl:compiler;ARM64;arm64-lap.lisp")
  (provide "ARM64-LAP")
  (cl "ccl:compiler;ARM64;arm64-backend.lisp")
  (provide "ARM64-BACKEND")
  (cl "ccl:lib;ffi-darwinarm64.lisp")
  (provide "FFI-DARWINARM64")
  (provide "ARCH")
  (provide "VINSN")
  (cl "ccl:compiler;ARM64;arm64-vinsns.lisp")
  (provide "ARM64-VINSNS")
  (cl "ccl:compiler;ARM64;arm642.lisp")
  (provide "ARM642"))

;;; Step 2b: Patch NX1-FF-CALL
(let ((orig-fn (gethash '%ff-call *nx1-alphatizers*)))
  (when orig-fn
    (setf (gethash '%ff-call *nx1-alphatizers*)
          (lambda (context whole env)
            (if (member (backend-name *target-backend*) '(:darwinarm64 :linuxarm64))
              (let ((address-expression (cadr whole))
                    (arg-specs-and-result-spec (cddr whole)))
                (nx1-ff-call-internal context address-expression
                                      arg-specs-and-result-spec
                                      (%nx1-operator eabi-ff-call)))
              (funcall orig-fn context whole env))))))

;;; Step 3: Load compile-ccl and macros
(let ((*warn-if-redefine-kernel* nil))
  (compile-file "ccl:lib;compile-ccl.lisp" :output-file "ccl:bin;compile-ccl.dx64fsl" :verbose nil :load t))
(let ((*warn-if-redefine-kernel* nil))
  (compile-file "ccl:lib;macros.lisp" :output-file "ccl:lib;macros.dx64fsl" :verbose nil :load t))

;;; Step 4: Compile l1-utils.lisp targeting ARM64 using cross-compile mechanism
(format t "~%=== Compiling l1-utils.lisp for ARM64 ===~%")
(with-cross-compilation-target (:darwinarm64)
  (let* ((*target-backend* (find-backend :darwinarm64)))
    (target-compile-modules '(l1-utils) :darwinarm64 t)))
(format t "~%=== Done ===~%")
(quit)
