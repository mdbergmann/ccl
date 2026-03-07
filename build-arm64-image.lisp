;;; Build ARM64 boot image from x86-64 host CCL
;;; Usage: ./dx86cl64 --no-init --load build-arm64-image.lisp
(in-package :ccl)

(setq *batch-flag* t)

;;; Step 1: Recompile systems.lisp (adds ARM64 module definitions)
(compile-file "ccl:lib;systems.lisp" :output-file "ccl:bin;systems.dx64fsl" :verbose nil)
(load "ccl:bin;systems.dx64fsl" :verbose nil)

;;; Step 2: Compile and load ARM64 modules in dependency order
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
  (provide "ARM642")
  ;; LAP macros needed by level-0 ARM64 files at compile time
  (cl "ccl:compiler;ARM64;arm64-lapmacros.lisp")
  (provide "ARM64-LAPMACROS"))

;;; Step 2a: Recompile nx1.lisp to pick up arm64-lap-function handler
(let ((*warn-if-redefine-kernel* nil))
  (compile-file "ccl:compiler;nx1.lisp" :output-file "ccl:compiler;nx1.dx64fsl" :verbose nil :load t))

;;; Step 2b: Patch host NX1-FF-CALL for ARM64
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

;;; Step 3: Load compile-ccl support
(let ((*warn-if-redefine-kernel* nil))
  (compile-file "ccl:lib;compile-ccl.lisp" :output-file "ccl:bin;compile-ccl.dx64fsl" :verbose nil :load t))

;;; Step 4: Load xdump modules and build the image
(format t "~%=== Loading xdump modules ===~%")
(let ((*warn-if-redefine-kernel* nil))
  (flet ((cl (src)
           (let* ((fasl (merge-pathnames (make-pathname :type "dx64fsl") src)))
             (compile-file src :output-file fasl :verbose nil :load t))))
    (cl "ccl:xdump;faslenv.lisp")
    (cl "ccl:xdump;hashenv.lisp")
    (cl "ccl:xdump;xfasload.lisp")
    (cl "ccl:xdump;xarm64fasload.lisp")
    (cl "ccl:xdump;heap-image.lisp")))

(format t "~%=== Building ARM64 boot image ===~%")
(cross-xload-level-0 :darwinarm64)
(format t "~%=== Image build COMPLETE ===~%")
(quit)
