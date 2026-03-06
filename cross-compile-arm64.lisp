;;; Bootstrap ARM64 cross-compilation from x86-64 CCL
(in-package :ccl)

;;; Suppress verbose backtraces on error — just print the condition
(setq *batch-flag* t)

;;; Step 1: Recompile systems.lisp (adds ARM64 module definitions)
(compile-file "ccl:lib;systems.lisp" :output-file "ccl:bin;systems.dx64fsl" :verbose nil)
(load "ccl:bin;systems.dx64fsl" :verbose nil)

;;; Step 2: Compile and load ARM64 modules in dependency order
(flet ((cl (src)
         (let* ((fasl (merge-pathnames (make-pathname :type "dx64fsl") src)))
           (compile-file src :output-file fasl :verbose nil :load t))))
  ;; Architecture definitions
  (cl "ccl:compiler;ARM64;arm64-arch.lisp")
  (provide "ARM64-ARCH")
  ;; Environment
  (cl "ccl:lib;arm64env.lisp")
  (provide "ARM64ENV")
  ;; Assembler
  (cl "ccl:compiler;ARM64;arm64-asm.lisp")
  (provide "ARM64-ASM")
  ;; RISC LAP (shared, needed before arm64-lap)
  (cl "ccl:compiler;risc-lap.lisp")
  ;; ARM64 LAP
  (cl "ccl:compiler;ARM64;arm64-lap.lisp")
  (provide "ARM64-LAP")
  ;; Backend (defines %define-arm64-vinsn and *darwinarm64-backend*)
  (cl "ccl:compiler;ARM64;arm64-backend.lisp")
  (provide "ARM64-BACKEND")
  ;; FFI support (defines ARM64-DARWIN::EXPAND-FF-CALL etc.)
  (cl "ccl:lib;ffi-darwinarm64.lisp")
  (provide "FFI-DARWINARM64")
  ;; Prevent ASDF/require from re-loading these
  (provide "ARCH")
  (provide "VINSN")
  ;; Vinsns
  (cl "ccl:compiler;ARM64;arm64-vinsns.lisp")
  (provide "ARM64-VINSNS")
  ;; Main compiler pass (arm642)
  (cl "ccl:compiler;ARM64;arm642.lisp")
  (provide "ARM642"))

;;; Step 2b: Patch host compiler functions that need ARM64 awareness
;;; The host's NX1-FF-CALL doesn't know about :darwinarm64 — patch it
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
(require "COMPILE-CCL")

;;; Step 4: Cross-compile
(format t "~%=== Starting cross-compile ===~%")
(ccl::cross-compile-ccl :darwinarm64)
(format t "~%=== Cross-compile COMPLETE ===~%")
(quit)
