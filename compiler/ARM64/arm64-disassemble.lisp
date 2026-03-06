;;;-*- Mode: Lisp; Package: (ARM64 :use CL) -*-
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

;;; ARM64 disassembler — minimal stub.
;;; A full disassembler will be added in a later phase.

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require "ARM64-ASM"))

(defun arm64-xdisassemble (function &optional (stream *debug-io*))
  "Disassemble an ARM64 function.  (Stub: prints raw instruction words.)"
  (unless (typep function 'function)
    (setq function (fboundp function))
    (unless (typep function 'function)
      (error "Can't find function for ~s" function)))
  (let* ((code-vector (uvref function 1))
         (n (if (typep code-vector 'code-vector)
              (uvref code-vector 0)   ; element count from header
              0)))
    (format stream "~&;;; ARM64 disassembly of ~s (~d instruction~:p)~%"
            function n)
    (dotimes (i n)
      (let* ((instruction (uvref code-vector (1+ i))))
        (format stream "  ~4d: #x~8,'0X~%" (* i 4) instruction)))
    (values)))
