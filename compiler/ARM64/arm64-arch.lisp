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


;;; Fundamental constants — 64-bit, TBI (Top Byte Ignore) tagging scheme.
;;;
;;; ARM64 uses TBI to place type tags in the high byte (bits 56-63) of
;;; 64-bit pointers/values, leaving the low 56 bits for values/addresses.
;;; This is fundamentally different from x86-64 and ARM32 low-bit tagging:
;;;   - Fixnums are unshifted native integers (fixnumshift = 0, fixnumone = 1)
;;;   - Tag testing examines the top byte, not low bits
;;;   - No fulltagmask/tagmask in the low-bit sense
;;; The tag byte layout is defined in section 8 (Tag Definitions).

(eval-when (:compile-toplevel :load-toplevel :execute)

(defconstant nbits-in-word 64)
(defconstant nbits-in-byte 8)
(defconstant tag-shift 56)                     ; tags occupy bits 56-63

(defconstant num-subtag-bits 8)                ; low byte of uvector header is subtag

(defconstant fixnumshift 0)                    ; fixnums are NOT shifted (tags in high byte)
(defconstant fixnum-shift fixnumshift)

(defconstant ncharcodebits 8)                  ; only low 8 bits used
(defconstant charcode-shift 8)

(defconstant word-shift 3)                     ; log2(8)
(defconstant word-size-in-bytes 8)
(defconstant node-size word-size-in-bytes)
(defconstant dnode-size 16)
(defconstant dnode-align-bits 4)               ; log2(16)
(defconstant dnode-shift dnode-align-bits)
(defconstant bitmap-shift 6)                   ; log2(64) — bits per word for bitmap

(defconstant fixnumone (ash 1 fixnumshift))    ; = 1 (no shift in TBI scheme)
(defconstant fixnum-one fixnumone)
(defconstant fixnum1 fixnumone)

;;; Fixnum range: signed 56-bit integers.
;;; Positive fixnums have top byte = #x00, negative have top byte = #xFF.
;;; Overflow by one bit gives top byte #x01 (positive) or #xFE (negative).
(defconstant target-most-negative-fixnum (- (ash 1 (1- tag-shift))))  ; -2^55
(defconstant target-most-positive-fixnum (1- (ash 1 (1- tag-shift)))) ; 2^55 - 1

)


;;; Tag Definitions — high-byte TBI tags
;;;
;;; In the TBI scheme, the top byte (bits 56-63) of a 64-bit value
;;; encodes its type.  The tag byte space is partitioned as:
;;;
;;;   #x00       : non-negative fixnum (sign extension of bit 55)
;;;   #x01       : overflowed positive fixnum (arithmetic overflow by 1 bit)
;;;   #x02       : NIL
;;;   #x03       : cons
;;;   #x10-#x1F  : immediates (single-float, character, markers)
;;;   #x40-#x5F  : ivector references (bit 6 set, bit 5 clear)
;;;   #x60-#x7F  : gvector references (bit 6 set, bit 5 set)
;;;   #x80-#x9F  : ivector headers  (bit 7 set, bit 5 clear)
;;;   #xA0-#xBF  : gvector headers  (bit 7 set, bit 5 set)
;;;   #xFE       : overflowed negative fixnum
;;;   #xFF       : negative fixnum (sign extension of bit 55)
;;;
;;; Each uvector type gets a unique reference tag (top byte of pointer)
;;; AND a unique header subtag (low byte of header word).  This differs
;;; from ARM32/x86-64 where all misc objects share one pointer tag.

(eval-when (:compile-toplevel :load-toplevel :execute)

;;; Fixnum tags — top byte is sign extension of the 56-bit value.
(defconstant tag-positive-fixnum 0)
(defconstant tag-negative-fixnum #xFF)
(defconstant tag-overflowed-positive-fixnum 1)
(defconstant tag-overflowed-negative-fixnum #xFE)

;;; List tags — bits 58-63 clear, bit 57 set.
(defconstant list-leading-zero-bits 6)
(defconstant tag-nil 2)
(defconstant tag-cons 3)

;;; Immediate tags — bits 61-63 clear, bit 60 set (base = #x10).
(defconstant imm-tag-mask #x10)
(defconstant tag-single-float (logior imm-tag-mask 0))     ; #x10
(defconstant tag-character (logior imm-tag-mask 1))         ; #x11
(defconstant tag-unbound (logior imm-tag-mask 2))           ; #x12
(defconstant tag-slot-unbound (logior imm-tag-mask 3))      ; #x13
(defconstant tag-no-thread-local-binding (logior imm-tag-mask 4))  ; #x14
(defconstant tag-illegal (logior imm-tag-mask 5))           ; #x15
(defconstant tag-stack-alloc (logior imm-tag-mask 6))       ; #x16

;;; Subtag aliases for immediates — other parts of the codebase
;;; reference these under the subtag- naming convention.
(defconstant subtag-single-float tag-single-float)
(defconstant subtag-character tag-character)
(defconstant subtag-unbound tag-unbound)
(defconstant subtag-slot-unbound tag-slot-unbound)
(defconstant subtag-no-thread-local-binding tag-no-thread-local-binding)
(defconstant subtag-illegal tag-illegal)
(defconstant subtag-stack-alloc-marker tag-stack-alloc)

;;; Full marker values — tag byte shifted into the top-byte position.
;;; These are the actual 64-bit bit patterns for marker objects.
(defconstant unbound-marker (ash tag-unbound tag-shift))
(defconstant slot-unbound-marker (ash tag-slot-unbound tag-shift))
(defconstant no-thread-local-binding-marker (ash tag-no-thread-local-binding tag-shift))
(defconstant illegal-marker (ash tag-illegal tag-shift))
(defconstant stack-alloc-marker (ash tag-stack-alloc tag-shift))
(defconstant undefined unbound-marker)

;;; Uvector tag infrastructure
;;;
;;; Uvector references have bit 6 set in the tag byte.
;;; Uvector headers have bit 7 set in the LOW byte of the header word
;;; (not the TBI top byte — headers are data, not tagged pointers).
;;; Gvectors (node-containing) additionally have bit 5 set.
;;; CL-defined ivectors have bit 0 set.
;;; Bits 1-4 encode the specific type within each category.

(defconstant gvector-tag-bit 5)
(defconstant gvector-tag-mask (ash 1 gvector-tag-bit))     ; #x20

(defconstant uvector-ref #x40)
(defconstant uvector-header #x80)
(defconstant uvector-mask (logior uvector-header uvector-ref))  ; #xC0

(defconstant cl-ivector-tag-bit 0)
(defconstant cl-ivector-mask (ash 1 cl-ivector-tag-bit))    ; #x01
(defconstant cl-ivector-ref (logior uvector-ref cl-ivector-mask))  ; #x41
(defconstant cl-ivector-ref-mask (logior uvector-mask gvector-tag-mask cl-ivector-mask))  ; #xE1

;;; Macros for defining uvector subtags (used in section 9).
;;; Each creates two constants:
;;;   SUBTAG-name = header byte value   (uvector-header | type-bits)
;;;   TAG-name    = reference tag value  (uvector-ref | type-bits)

(defmacro define-uvector (name type-bits)
  `(progn
     (defconstant ,(ccl::form-symbol "SUBTAG-" name) (logior uvector-header ,type-bits))
     (defconstant ,(ccl::form-symbol "TAG-" name) (logior uvector-ref ,type-bits))))

(defmacro define-ivector (name n)
  `(define-uvector ,name (ash ,n 1)))

(defmacro define-cl-ivector (name n)
  `(define-uvector ,name (logior (ash ,n 1) cl-ivector-mask)))

(defmacro define-gvector (name n)
  `(define-uvector ,name (logior ,n gvector-tag-mask)))

)


;;; Uvector Subtags
;;;
;;; Each define-ivector/define-cl-ivector/define-gvector call creates
;;; SUBTAG-name (header byte, bit 7 set) and TAG-name (reference tag, bit 6 set).
;;; The order and numbering must exactly match arm64-constants.s and
;;; arm64-constants.h.
;;;
;;; Encoding recap (6 type bits within the tag/subtag byte):
;;;   ivector:    value << 1              (bit 0 = 0)
;;;   cl-ivector: (value << 1) | 1        (bit 0 = 1)
;;;   gvector:    value | #x20            (bit 5 = 1)
;;;
;;; Element-size grouping for ivectors (by value parameter):
;;;   0-4:  32-bit elements
;;;   5-6:  64-bit elements (non-CL only at these values)
;;;   5-9:  64-bit elements (CL ivectors at values 5-9)
;;;   10-11: 8-bit elements
;;;   12-13: 16-bit elements
;;;   14:   128-bit elements (complex-double-float)
;;;   15:   sub-byte (bit-vector)

(eval-when (:compile-toplevel :load-toplevel :execute)

;;; ---------------------------------------------------------------
;;; Ivectors — non-CL internal types (32-bit element group)
;;; ---------------------------------------------------------------
(define-ivector bignum 0)
(define-ivector double-float 1)
(define-ivector complex-single-float 2)
(define-ivector complex-double-float 3)
(define-ivector xcode-vector 4)

;;; CL ivectors — 32-bit element group
(define-cl-ivector s32-vector 0)
(define-cl-ivector u32-vector 1)
(define-cl-ivector single-float-vector 2)
(define-cl-ivector simple-base-string 3)        ; simple_string in assembly

;;; 32-bit element boundary constants
(defconstant min-32-bit-ivector-subtag subtag-bignum)
(defconstant max-32-bit-ivector-subtag subtag-xcode-vector)

;;; ---------------------------------------------------------------
;;; Ivectors — non-CL internal types (64-bit element group)
;;; ---------------------------------------------------------------
(define-ivector macptr 5)
(define-ivector dead-macptr 6)

;;; CL ivectors — 64-bit element group
(define-cl-ivector s64-vector 5)
(define-cl-ivector u64-vector 6)
(define-cl-ivector fixnum-vector 7)
(define-cl-ivector double-float-vector 8)
(define-cl-ivector complex-single-float-vector 9)

;;; 64-bit element boundary constants
(defconstant min-64-bit-ivector-subtag subtag-macptr)
(defconstant max-64-bit-ivector-subtag subtag-complex-single-float-vector)

;;; ---------------------------------------------------------------
;;; CL ivectors — 8-bit element group
;;; ---------------------------------------------------------------
(define-cl-ivector s8-vector 10)
(define-cl-ivector u8-vector 11)

(defconstant min-8-bit-ivector-subtag subtag-s8-vector)
(defconstant max-8-bit-ivector-subtag subtag-u8-vector)

;;; ---------------------------------------------------------------
;;; CL ivectors — 16-bit element group
;;; ---------------------------------------------------------------
(define-cl-ivector s16-vector 12)
(define-cl-ivector u16-vector 13)

(defconstant min-16-bit-ivector-subtag subtag-s16-vector)
(defconstant max-16-bit-ivector-subtag subtag-u16-vector)

;;; ---------------------------------------------------------------
;;; CL ivectors — other element sizes
;;; ---------------------------------------------------------------
(define-cl-ivector complex-double-float-vector 14)  ; 128-bit elements
(define-cl-ivector bit-vector 15)                   ; 1-bit elements

;;; The smallest CL ivector subtag (all CL ivectors have bit 0 set).
(defconstant min-cl-ivector-subtag subtag-s32-vector)

;;; ---------------------------------------------------------------
;;; Gvectors — node-containing heap objects (bit 5 set in type bits)
;;; ---------------------------------------------------------------

;;; Numeric gvectors
(define-gvector ratio 0)
(define-gvector complex 1)

;;; Non-numeric gvectors
(define-gvector function 2)
(define-gvector symbol 3)
(define-gvector catch-frame 4)
(define-gvector basic-stream 5)
(define-gvector lock 6)
(define-gvector hash-vector 7)
(define-gvector pool 8)
(define-gvector weak 9)
(define-gvector package 10)
(define-gvector slot-vector 11)
(define-gvector instance 12)
(define-gvector struct 13)
(define-gvector istruct 14)
(define-gvector value-cell 15)
(define-gvector xfunction 16)                       ; cross-development

;;; Array gvectors (must satisfy arrayH < vectorH < simple-vector)
(define-gvector arrayH 29)
(define-gvector vectorH 30)
(define-gvector simple-vector 31)

(assert (< subtag-arrayH subtag-vectorH subtag-simple-vector))

;;; ---------------------------------------------------------------
;;; Max constant index values (from arm64-constants.s)
;;; ---------------------------------------------------------------
(defconstant max-64-bit-constant-index #x400)
(defconstant max-32-bit-constant-index #x400)
(defconstant max-16-bit-constant-index #x400)
(defconstant max-8-bit-constant-index #x400)
(defconstant max-1-bit-constant-index 0)

)


;;; Storage layout macros — 8-byte steps for 64-bit
(defmacro define-storage-layout (name origin &rest cells)
  `(progn
     (ccl::defenum (:start ,origin :step 8)
       ,@(mapcar #'(lambda (cell) (ccl::form-symbol name "." cell)) cells))
     (defconstant ,(ccl::form-symbol name ".SIZE") ,(* (length cells) 8))))

(defmacro define-lisp-object (name tagname &rest cells)
  `(define-storage-layout ,name ,(- (symbol-value tagname)) ,@cells))

(defmacro define-fixedsized-object (name &rest non-header-cells)
  `(progn
     (define-storage-layout ,name (- node-size) header ,@non-header-cells)
     (ccl::defenum ()
       ,@(mapcar #'(lambda (cell) (ccl::form-symbol name "." cell "-CELL")) non-header-cells))
     (defconstant ,(ccl::form-symbol name ".ELEMENT-COUNT") ,(length non-header-cells))))


;;; Memory Layout Constants
;;;
;;; In the TBI scheme, ALL tagged pointers (cons, uvector/misc, function)
;;; have their low 56 bits pointing one node-size (8 bytes) past the start
;;; of the object in memory.  This uniform bias means:
;;;   - For misc objects: header at offset -8, first data slot at offset 0
;;;   - For cons cells: cdr at offset -8, car at offset 0
;;;   - For functions: header at offset -8, entrypoint at offset 0
;;;
;;; This optimizes for ARM64 unsigned-offset loads (LDR with 12-bit scaled
;;; unsigned immediate) for common element/field access, while header/cdr
;;; access uses signed-offset loads (LDUR with 9-bit signed immediate).
;;;
;;; Bias: the positive offset from the object's memory base address to the
;;; low 56 bits of its tagged pointer.
;;;   tagged_ptr_low56 = object_base_address + bias
;;;
;;; These constants must match arm64-constants.s.

(defconstant misc-bias node-size)                  ; = 8
(defconstant cons-bias misc-bias)
(defconstant function-bias misc-bias)

;;; Offsets from tagged pointer (low 56 bits) to object components.
;;; These are used in load/store instructions: LDR x0, [tagged_ptr, #offset]
;;; TBI causes the hardware to ignore the tag byte in the top 8 bits.

(defconstant misc-header-offset (- node-size))     ; = -8; header word
(defconstant misc-subtag-offset misc-header-offset) ; subtag = low byte of header
(defconstant misc-data-offset 0)                   ; first data element
(defconstant misc-dfloat-offset misc-data-offset)  ; double-float value (8-byte aligned)

;;; Complex-double-float elements require 16-byte alignment.  Objects are
;;; dnode-aligned, so the header is at a 16-byte-aligned address.  The first
;;; data slot (at header + 8) is only 8-byte aligned, so a pad word is
;;; needed before the complex-double-float data to restore 16-byte alignment.
(defconstant misc-complex-dfloat-offset (+ misc-data-offset node-size))  ; = 8


;;; NIL and T Values
;;;
;;; In the TBI scheme, NIL occupies a fixed memory location.  The rnil
;;; register (x6) holds canonical-nil-value at all times: tag-nil in
;;; the top byte, effective address in the low 56 bits.
;;;
;;; Memory layout near NIL:
;;;
;;;   nil-base + 0:              [canonical-nil-value]  CDR of NIL (= NIL)
;;;   nil-base + 8:              [canonical-nil-value]  CAR of NIL (= NIL)
;;;   nil-base + 16:             T symbol header        first nil-relative symbol
;;;   nil-base + 24:             T.pname
;;;   ...
;;;   nil-base + 16 + sym-size:  NIL symbol header      NIL's own symbol struct
;;;   ...  (subsequent nil-relative symbols follow)
;;;
;;; Kernel globals are at negative offsets from nil-base.
;;; Nil-relative symbols are at positive offsets starting at t-offset.
;;;
;;; Access from rnil:
;;;   CDR(NIL): LDUR x0, [rnil, #-8]  → loads from nil-base + 0
;;;   CAR(NIL): LDR  x0, [rnil, #0]   → loads from nil-base + 8
;;;   T.pname:  LDR  x0, [rnil, #t-offset]  → loads from nil-base + 24

(eval-when (:compile-toplevel :load-toplevel :execute)

;;; Base address — arbitrary dnode-aligned address in low memory.
;;; The kernel maps this region during initialization.
(defconstant nil-base-address #x13000)

;;; Canonical NIL value — the full tagged 64-bit representation.
;;; Tag byte (tag-nil = #x02) in bits 56-63, effective address in
;;; bits 0-55.  Effective address = nil-base-address + node-size.
(defconstant canonical-nil-value
  (logior (ash tag-nil tag-shift) (+ nil-base-address node-size)))

(defconstant nil-value canonical-nil-value)

;;; T is the first nil-relative symbol.  Its symbol structure starts
;;; one dnode past nil-base (the dnode at nil-base holds CDR(NIL) and
;;; CAR(NIL), both = NIL).
;;;
;;; t-offset is the memory distance from NIL's effective address to
;;; T's effective address.  Since both effective addresses are biased
;;; by node-size from their respective bases:
;;;   NIL effective = nil-base + node-size
;;;   T effective   = nil-base + dnode-size + node-size
;;;   t-offset      = dnode-size
(defconstant t-offset dnode-size)                  ; = 16

)


(provide "ARM64-ARCH")
