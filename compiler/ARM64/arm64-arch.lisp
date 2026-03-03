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



(eval-when (:compile-toplevel :load-toplevel :execute)
(defparameter *arm64-subprims-shift* 3)         ; 8-byte entries for 64-bit
(defconstant tcr.sptab 384)
(defparameter *arm64-subprims-base* tcr.sptab)
)
(defvar *arm64-subprims*)


(let* ((origin *arm64-subprims-base*)
       (step (ash 1 *arm64-subprims-shift*)))
  (flet ((define-arm64-subprim (name)
             (ccl::make-subprimitive-info :name (string name)
                                          :offset
                                          (prog1 origin
                                            (incf origin step)))))
    (macrolet ((defarm64subprim (name)
                   `(define-arm64-subprim ',name)))
      (setq *arm64-subprims*
            (vector
             (defarm64subprim .SPfix-nfn-entrypoint) ;must be first
             (defarm64subprim .SPbuiltin-plus)
             (defarm64subprim .SPbuiltin-minus)
             (defarm64subprim .SPbuiltin-times)
             (defarm64subprim .SPbuiltin-div)
             (defarm64subprim .SPbuiltin-eq)
             (defarm64subprim .SPbuiltin-ne)
             (defarm64subprim .SPbuiltin-gt)
             (defarm64subprim .SPbuiltin-ge)
             (defarm64subprim .SPbuiltin-lt)
             (defarm64subprim .SPbuiltin-le)
             (defarm64subprim .SPbuiltin-eql)
             (defarm64subprim .SPbuiltin-length)
             (defarm64subprim .SPbuiltin-seqtype)
             (defarm64subprim .SPbuiltin-assq)
             (defarm64subprim .SPbuiltin-memq)
             (defarm64subprim .SPbuiltin-logbitp)
             (defarm64subprim .SPbuiltin-logior)
             (defarm64subprim .SPbuiltin-logand)
             (defarm64subprim .SPbuiltin-ash)
             (defarm64subprim .SPbuiltin-negate)
             (defarm64subprim .SPbuiltin-logxor)
             (defarm64subprim .SPbuiltin-aref1)
             (defarm64subprim .SPbuiltin-aset1)
             (defarm64subprim .SPfuncall)
             (defarm64subprim .SPmkcatch1v)
             (defarm64subprim .SPmkcatchmv)
             (defarm64subprim .SPmkunwind)
             (defarm64subprim .SPbind)
             (defarm64subprim .SPconslist)
             (defarm64subprim .SPconslist-star)
             (defarm64subprim .SPmakes32)
             (defarm64subprim .SPmakeu32)
             (defarm64subprim .SPfix-overflow)
             (defarm64subprim .SPmakeu64)
             (defarm64subprim .SPmakes64)
             (defarm64subprim .SPmvpass)
             (defarm64subprim .SPvalues)
             (defarm64subprim .SPnvalret)
             (defarm64subprim .SPthrow)
             (defarm64subprim .SPnthrowvalues)
             (defarm64subprim .SPnthrow1value)
             (defarm64subprim .SPbind-self)
             (defarm64subprim .SPbind-nil)
             (defarm64subprim .SPbind-self-boundp-check)
             (defarm64subprim .SPrplaca)
             (defarm64subprim .SPrplacd)
             (defarm64subprim .SPgvset)
             (defarm64subprim .SPset-hash-key)
             (defarm64subprim .SPstore-node-conditional)
             (defarm64subprim .SPset-hash-key-conditional)
             (defarm64subprim .SPstkconslist)
             (defarm64subprim .SPstkconslist-star)
             (defarm64subprim .SPmkstackv)
             (defarm64subprim .SPsetqsym)
             (defarm64subprim .SPprogvsave)
             (defarm64subprim .SPstack-misc-alloc)
             (defarm64subprim .SPgvector)
             (defarm64subprim .SPfitvals)
             (defarm64subprim .SPnthvalue)
             (defarm64subprim .SPdefault-optional-args)
             (defarm64subprim .SPopt-supplied-p)
             (defarm64subprim .SPheap-rest-arg)
             (defarm64subprim .SPreq-heap-rest-arg)
             (defarm64subprim .SPheap-cons-rest-arg)
             (defarm64subprim .SPcheck-fpu-exception)
             (defarm64subprim .SPdiscard_stack_object)
             (defarm64subprim .SPksignalerr)
             (defarm64subprim .SPstack-rest-arg)
             (defarm64subprim .SPreq-stack-rest-arg)
             (defarm64subprim .SPstack-cons-rest-arg)
             (defarm64subprim .SPcall-closure)
             (defarm64subprim .SPspreadargz)
             (defarm64subprim .SPtfuncallgen)
             (defarm64subprim .SPtfuncallslide)
             (defarm64subprim .SPjmpsym)
             (defarm64subprim .SPtcallsymgen)
             (defarm64subprim .SPtcallsymslide)
             (defarm64subprim .SPtcallnfngen)
             (defarm64subprim .SPtcallnfnslide)
             (defarm64subprim .SPmisc-ref)
             (defarm64subprim .SPsubtag-misc-ref)
             (defarm64subprim .SPmakestackblock)
             (defarm64subprim .SPmakestackblock0)
             (defarm64subprim .SPmakestacklist)
             (defarm64subprim .SPstkgvector)
             (defarm64subprim .SPmisc-alloc)
             (defarm64subprim .SPatomic-incf-node)
             (defarm64subprim .SPunused1)
             (defarm64subprim .SPunused2)
             (defarm64subprim .SPrecover-values)
             (defarm64subprim .SPinteger-sign)
             (defarm64subprim .SPsubtag-misc-set)
             (defarm64subprim .SPmisc-set)
             (defarm64subprim .SPspread-lexprz)
             (defarm64subprim .SPreset)
             (defarm64subprim .SPmvslide)
             (defarm64subprim .SPsave-values)
             (defarm64subprim .SPadd-values)
             (defarm64subprim .SPmisc-alloc-init)
             (defarm64subprim .SPstack-misc-alloc-init)
             (defarm64subprim .SPpopj)
             (defarm64subprim .SPudiv64by32)
             (defarm64subprim .SPgetu64)
             (defarm64subprim .SPgets64)
             (defarm64subprim .SPspecref)
             (defarm64subprim .SPspecrefcheck)
             (defarm64subprim .SPspecset)
             (defarm64subprim .SPgets32)
             (defarm64subprim .SPgetu32)
             (defarm64subprim .SPmvpasssym)
             (defarm64subprim .SPunbind)
             (defarm64subprim .SPunbind-n)
             (defarm64subprim .SPunbind-to)
             (defarm64subprim .SPprogvrestore)
             (defarm64subprim .SPbind-interrupt-level-0)
             (defarm64subprim .SPbind-interrupt-level-m1)
             (defarm64subprim .SPbind-interrupt-level)
             (defarm64subprim .SPunbind-interrupt-level)
             (defarm64subprim .SParef2)
             (defarm64subprim .SParef3)
             (defarm64subprim .SPaset2)
             (defarm64subprim .SPaset3)
             (defarm64subprim .SPkeyword-bind)
             (defarm64subprim .SPudiv32)
             (defarm64subprim .SPsdiv32)
             (defarm64subprim .SPaapcs64-ff-call-simple)
             (defarm64subprim .SPdebind)
             (defarm64subprim .SPaapcs64-callback)
             (defarm64subprim .SPaapcs64-ff-callhf)
             )))))

(provide "ARM64-ARCH")
