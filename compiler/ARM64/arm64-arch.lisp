;;;-*- Mode: Lisp; Package: (ARM64 :use CL) -*-
;;;
;;; Copyright 2016 Clozure Associates
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

(defpackage "ARM64"
  (:use "CL")
  #+arm64-target
  (:nicknames "TARGET"))

(require "ARCH")

(in-package "ARM64")


;;; Lisp registers.

(eval-when (:compile-toplevel :load-toplevel :execute)
(defvar *arm64-register-names* ())

(defun get-arm64-register (name)
  (let* ((pair (assoc (string name) *arm64-register-names* :test #'string-equal)))
    (if pair
      (cdr pair))))

(defun get-arm64-gpr (name)
  (let* ((value (get-arm64-register name)))
    (and value (< value 32) value)))

(defun get-arm64-dfpr (name)
  (let* ((value (get-arm64-register name)))
    (and value (>= value 32) (< value 64) (- value 32))))

(defun get-arm64-sfpr (name)
  (let* ((value (get-arm64-register name)))
    (and value (>= value 64) (< value 96) (- value 64))))

(defun define-arm64-register (name val)
  (let* ((value (if (typep val 'fixnum) val (get-arm64-register val)))
         (string (string name)))
    (unless value
      (error "invalid ARM64 register value ~d for ~s." val name))
    (let* ((pair (assoc string *arm64-register-names* :test #'string-equal)))
      (if pair
        (progn
          (unless (eql (cdr pair) value)
            (when ccl::*cerror-on-constant-redefinition*
              (cerror "Redefine ARM64 register ~s to have value ~*~d."
                      "ARM64 register ~s currently has value ~d."
                      name (cdr pair) value)
              (setf (cdr pair) value))))
        (push (cons string value) *arm64-register-names*))
        value)))

;;; GPRs x0-x30 (numbered 0-30)
(defmacro defarm64gpr (name val)
  `(defconstant ,name (define-arm64-register ',name ',val)))

(defarm64gpr x0 0)
(defarm64gpr x1 1)
(defarm64gpr x2 2)
(defarm64gpr x3 3)
(defarm64gpr x4 4)
(defarm64gpr x5 5)
(defarm64gpr x6 6)
(defarm64gpr x7 7)
(defarm64gpr x8 8)
(defarm64gpr x9 9)
(defarm64gpr x10 10)
(defarm64gpr x11 11)
(defarm64gpr x12 12)
(defarm64gpr x13 13)
(defarm64gpr x14 14)
(defarm64gpr x15 15)
(defarm64gpr x16 16)
(defarm64gpr x17 17)
(defarm64gpr x18 18)
(defarm64gpr x19 19)
(defarm64gpr x20 20)
(defarm64gpr x21 21)
(defarm64gpr x22 22)
(defarm64gpr x23 23)
(defarm64gpr x24 24)
(defarm64gpr x25 25)
(defarm64gpr x26 26)
(defarm64gpr x27 27)
(defarm64gpr x28 28)
(defarm64gpr x29 29)
(defarm64gpr x30 30)

;;; Lisp role aliases — must match arm64-constants.s exactly
(defarm64gpr imm0 x0)
(defarm64gpr imm1 x1)
(defarm64gpr imm2 x2)
(defarm64gpr imm3 x3)
(defarm64gpr imm4 x4)
(defarm64gpr imm5 x5)
(defarm64gpr nargs x5)
(defarm64gpr rnil x6)
(defarm64gpr rt x7)
(defarm64gpr rclosure-call x8)
(defarm64gpr temp3 x9)
(defarm64gpr fname temp3)
(defarm64gpr temp2 x10)
(defarm64gpr nfn temp2)
(defarm64gpr temp1 x11)
(defarm64gpr temp0 x12)
(defarm64gpr arg_x x13)
(defarm64gpr arg_y x14)
(defarm64gpr arg_z x15)
(defarm64gpr save0 x16)
(defarm64gpr save1 x17)
(defarm64gpr save2 x18)
(defarm64gpr save3 x19)
(defarm64gpr save4 x20)
(defarm64gpr save5 x21)
(defarm64gpr save6 x22)
(defarm64gpr save7 x23)
(defarm64gpr loc-pc x24)
(defarm64gpr vsp x25)
(defarm64gpr allocptr x26)
(defarm64gpr allocbase x27)
(defarm64gpr rcontext x28)
(defarm64gpr fp x29)
(defarm64gpr lr x30)

;;; Double-float registers d0-d31 (numbered 32-63)
(defmacro defarm64dfpr (name val)
  `(defconstant ,name (define-arm64-register ',name ',val)))

(defarm64dfpr d0 32)
(defarm64dfpr d1 33)
(defarm64dfpr d2 34)
(defarm64dfpr d3 35)
(defarm64dfpr d4 36)
(defarm64dfpr d5 37)
(defarm64dfpr d6 38)
(defarm64dfpr d7 39)
(defarm64dfpr d8 40)
(defarm64dfpr d9 41)
(defarm64dfpr d10 42)
(defarm64dfpr d11 43)
(defarm64dfpr d12 44)
(defarm64dfpr d13 45)
(defarm64dfpr d14 46)
(defarm64dfpr d15 47)
(defarm64dfpr d16 48)
(defarm64dfpr d17 49)
(defarm64dfpr d18 50)
(defarm64dfpr d19 51)
(defarm64dfpr d20 52)
(defarm64dfpr d21 53)
(defarm64dfpr d22 54)
(defarm64dfpr d23 55)
(defarm64dfpr d24 56)
(defarm64dfpr d25 57)
(defarm64dfpr d26 58)
(defarm64dfpr d27 59)
(defarm64dfpr d28 60)
(defarm64dfpr d29 61)
(defarm64dfpr d30 62)
(defarm64dfpr d31 63)

(defarm64dfpr vzero d31)

;;; Single-float registers s0-s31 (numbered 64-95)
(defmacro defarm64sfpr (name val)
  `(defconstant ,name (define-arm64-register ',name ',val)))

(defarm64sfpr s0 64)
(defarm64sfpr s1 65)
(defarm64sfpr s2 66)
(defarm64sfpr s3 67)
(defarm64sfpr s4 68)
(defarm64sfpr s5 69)
(defarm64sfpr s6 70)
(defarm64sfpr s7 71)
(defarm64sfpr s8 72)
(defarm64sfpr s9 73)
(defarm64sfpr s10 74)
(defarm64sfpr s11 75)
(defarm64sfpr s12 76)
(defarm64sfpr s13 77)
(defarm64sfpr s14 78)
(defarm64sfpr s15 79)
(defarm64sfpr s16 80)
(defarm64sfpr s17 81)
(defarm64sfpr s18 82)
(defarm64sfpr s19 83)
(defarm64sfpr s20 84)
(defarm64sfpr s21 85)
(defarm64sfpr s22 86)
(defarm64sfpr s23 87)
(defarm64sfpr s24 88)
(defarm64sfpr s25 89)
(defarm64sfpr s26 90)
(defarm64sfpr s27 91)
(defarm64sfpr s28 92)
(defarm64sfpr s29 93)
(defarm64sfpr s30 94)
(defarm64sfpr s31 95)

(defarm64sfpr single-float-zero s31)
)

(defparameter *standard-arm64-register-names* *arm64-register-names*)


;;; Kernel globals are allocated "below" nil.  This list (used to map
;;; symbolic names to rnil-relative offsets) must exactly match the
;;; kernel's notion of where things are.
;;; The order here matches "ccl:lisp-kernel;lisp_globals.h" & the
;;; lisp_globals record in "ccl:lisp-kernel;*constants*.s"
(defparameter *arm64-kernel-globals*
  '(get-tcr                              ; callback to obtain (real) tcr
    tcr-count
    interrupt-signal                      ; used by PROCESS-INTERRUPT
    kernel-imports                        ; some things we need to have imported for us.
    objc-2-personality
    savetoc                               ; used to save TOC on some platforms
    saver13                               ; used to save r13 on some platforms
    subprims-base                         ; start of dynamic subprims jump table
    ret1valaddr                           ; magic multiple-values return address.
    tcr-key                               ; tsd key for thread's tcr
    area-lock                             ; serialize access to gc
    exception-lock                        ; serialize exception handling
    static-conses                         ; when FREEZE is in effect
    default-allocation-quantum            ; log2_heap_segment_size, as a fixnum.
    intflag                               ; interrupt-pending flag
    gc-inhibit-count                      ; for gc locking
    refbits                               ; oldspace refbits
    oldspace-dnode-count                  ; number of dnodes in dynamic space that are older than
                                          ; youngest generation
    float-abi                             ; non-zero if using hard float abi
    fwdnum                                ; fixnum: GC "forwarder" call count.
    gc-count                              ; fixnum: GC call count.
    gcable-pointers                       ; linked-list of weak macptrs.
    heap-start                            ; start of lisp heap
    heap-end                              ; end of lisp heap
    statically-linked                     ; true if the lisp kernel is statically linked
    stack-size                            ; value of --stack-size arg
    objc-2-begin-catch                    ; objc_begin_catch
    kernel-path
    all-areas                             ; doubly-linked area list
    lexpr-return                          ; multiple-value lexpr return address
    lexpr-return1v                        ; single-value lexpr return address
    in-gc                                 ; non-zero when GC-ish thing active
    free-static-conses                    ; fixnum
    objc-2-end-catch                      ; _objc_end_catch
    short-float-zero                      ; low half of 1.0d0
    double-float-one                      ; high half of 1.0d0
    static-cons-area                      ;
    exception-saved-registers             ; saved registers from exception frame
    oldest-ephemeral                      ; doublenode address of oldest ephemeral object or 0
    tenured-area                          ; the tenured_area.
    errno                                 ; address of C lib errno
    argv                                  ; address of C lib argv
    host-platform                         ; 0 on MacOS, 1 on ARM Linux, 2 on VxWorks ...
    batch-flag                            ; non-zero if --batch specified
    unwind-resume                         ; _Unwind_Resume
    weak-gc-method                        ; weak gc algorithm.
    image-name                            ; current image name
    initial-tcr                           ; initial thread's context record
    weakvll                               ; all populations as of last GC
    ))

;;; The order here matches "ccl:lisp-kernel;lisp_globals.h" and the nrs record
;;; in "ccl:lisp-kernel;lisp_globals.s".
(defparameter *arm64-nil-relative-symbols*
  '(t
    nil
    ccl::%err-disp
    ccl::cmain
    eval
    ccl::apply-evaluated-function
    error
    ccl::%defun
    ccl::%defvar
    ccl::%defconstant
    ccl::%macro
    ccl::%kernel-restart
    *package*
    ccl::*total-bytes-freed*
    :allow-other-keys
    ccl::%toplevel-catch%
    ccl::%toplevel-function%
    ccl::%pascal-functions%
    ccl::restore-lisp-pointers
    ccl::*total-gc-microseconds*
    ccl::%builtin-functions%
    ccl::%unbound-function%
    ccl::%init-misc
    ccl::%macro-code%
    ccl::%closure-code%
    ccl::%new-gcable-ptr
    ccl::*gc-event-status-bits*
    ccl::*post-gc-hook*
    ccl::%handlers%
    ccl::%all-packages%
    ccl::*keyword-package*
    ccl::%os-init-function%
    ccl::%foreign-thread-control
    ))

;;; Old (and slightly confusing) name; NIL used to be in a register.
(defparameter *arm64-nilreg-relative-symbols* *arm64-nil-relative-symbols*)

(provide "ARM64-ARCH")
