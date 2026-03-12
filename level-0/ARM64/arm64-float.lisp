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

(eval-when (:compile-toplevel :execute)
  (require "NUMBER-MACROS")
  (require :number-case-macro))

;;; ARM64 AArch64 system register encodings for MRS/MSR.
;;; FPCR: op0=3, op1=3, CRn=4, CRm=4, op2=0 → 0x5A20
;;; FPSR: op0=3, op1=3, CRn=4, CRm=4, op2=1 → 0x5A21
;;; Defined in arm64-arch.lisp as arm64::arm64::fpcr-sysreg and arm64::arm64::fpsr-sysreg
;;; so they are available at LAP compile time during cross-compilation.

;;; ARM64: single-float is immediate (tag 0x10, IEEE value in bits 0-31).
;;; Double-float is heap-allocated (8-byte IEEE value at misc-data-offset = 0).

;;; Construct a double-float from fixnum parts.
;;; hi = high 24 bits mantissa (with implied bit), lo = low 28 bits,
;;; exp = biased exponent (11 bits), sign = negative if < 0.
(defarm64lapfunction %make-float-from-fixnums ((float 8) (hi 0) (lo arg_x) (exp arg_y) (sign arg_z))
  ;; fixnumshift=0: fixnums ARE the integers
  (ldr imm0 (:@ vsp (:$ 0)))            ; hi (from stack)
  ;; Build low 32 bits of IEEE double: lo[27:0] | hi[3:0] << 28
  (and imm1 lo (:$ #x0FFFFFFF))         ; lo 28 bits
  (orr imm1 imm1 (:lsl imm0 (:$ 28)))  ; merge hi low 4 bits
  ;; Build high 32 bits: mantissa_high[19:0] | exp[10:0] << 20 | sign
  (lsr imm2 imm0 (:$ 4))               ; hi >> 4 → mantissa bits 19-0
  (and imm2 imm2 (:$ #x000FFFFF))      ; keep only 20 mantissa bits
  (and imm3 exp (:$ #x7FF))            ; mask exponent to 11 bits
  (orr imm2 imm2 (:lsl imm3 (:$ 20))) ; insert exponent
  (cmp sign (:$ 0))
  (b.ge @nosign)
  (orr imm2 imm2 (:$ #x80000000))     ; set sign bit
  @nosign
  ;; Combine into 64-bit IEEE value: high32 << 32 | low32
  (and imm1 imm1 (:$ #xFFFFFFFF))     ; mask low 32 bits
  (orr imm0 imm1 (:lsl imm2 (:$ 32))) ; full 64-bit value
  ;; Store to float object
  (ldr arg_z (:@ vsp (:$ 8)))          ; float (from stack)
  (str imm0 (:@ arg_z (:$ arm64::double-float.value)))
  (add vsp vsp (:$ 16))                ; pop 2 stack args
  (ret))


;;; Construct a single-float from fixnum parts.
;;; ARM64: result is an immediate tagged value (no heap allocation).
(defarm64lapfunction %make-short-float-from-fixnums ((float 0) (sig arg_x) (exp arg_y) (sign arg_z))
  ;; fixnumshift=0: sig, exp, sign are raw integers
  (and imm0 sig (:$ #x7FFFFF))          ; mantissa bits 22-0 (strip implied 1)
  (and imm1 exp (:$ #xFF))              ; exponent 8 bits
  (orr imm0 imm0 (:lsl imm1 (:$ 23)))  ; insert exponent at bit 23
  (cmp sign (:$ 0))
  (b.ge @nosign)
  (orr imm0 imm0 (:$ #x80000000))      ; set sign bit
  @nosign
  ;; Add single-float tag in bits 56-63
  (movk imm0 (:$ (ash arm64::tag-single-float 8)) (:lsl 48))
  (mov arg_z imm0)
  (add vsp vsp (:$ 8))                  ; pop 1 stack arg (float box, unused on ARM64)
  (ret))


;;; Double-float absolute value
(defarm64lapfunction %%double-float-abs! ((n arg_y) (val arg_z))
  (get-double-float d0 n)
  (fabs d1 d0)
  (put-double-float d1 val)
  (ret))

;;; Single-float absolute value: just clear the sign bit (bit 31).
(defarm64lapfunction %%short-float-abs! ((n arg_y) (val arg_z))
  (bic arg_z n (:$ #x80000000))
  (ret))


;;; Double-float negate
(defarm64lapfunction %double-float-negate! ((src arg_y) (res arg_z))
  (get-double-float d0 src)
  (fneg d1 d0)
  (put-double-float d1 res)
  (ret))

;;; Single-float negate: flip sign bit (bit 31).
(defarm64lapfunction %short-float-negate! ((src arg_y) (res arg_z))
  (eor arg_z src (:$ #x80000000))
  (ret))



;;; Decode a double-float into mantissa-hi, mantissa-lo, exponent, sign.
;;; Returns 4 values: hi (25 bits), lo (28 bits), exp (fixnum), sign (±1).
(defarm64lapfunction %integer-decode-double-float ((n arg_z))
  ;; Load full 64-bit IEEE value
  (ldr imm0 (:@ n (:$ arm64::double-float.value)))
  ;; Extract sign
  (mov temp0 (:$ 1))
  (tst imm0 (:$ (ash 1 63)))
  (b.eq @pos)
  (mov temp0 (:$ -1))
  @pos
  ;; Extract exponent (bits 62-52)
  (lsr imm1 imm0 (:$ 52))
  (and temp1 imm1 (:$ #x7FF))           ; 11-bit biased exponent
  ;; Extract mantissa (bits 51-0)
  (lri imm2 #xFFFFFFFFFFFFF)            ; 52-bit mask
  (and imm0 imm0 imm2)
  ;; Add implied 1 if normalized (exp != 0)
  (cbz temp1 @denorm)
  (orr imm0 imm0 (:$ (ash 1 52)))       ; set implied bit at position 52
  @denorm
  ;; Split 53-bit mantissa into hi (25 bits) and lo (28 bits)
  ;; hi = mantissa[52:28], lo = mantissa[27:0]
  (lsr imm1 imm0 (:$ 28))               ; hi = mantissa >> 28 (25 bits)
  (lri imm2 #xFFFFFFF)                  ; 28-bit mask
  (and imm2 imm0 imm2)                  ; lo = mantissa & 0xFFFFFFF
  ;; Return 4 values
  (vpush1 imm1)                          ; hi (25 bits mantissa)
  (vpush1 imm2)                          ; lo (28 bits mantissa)
  (vpush1 temp1)                         ; exp (biased exponent)
  (vpush1 temp0)                         ; sign (±1)
  (set-nargs 4)
  (add temp0 vsp (:$ 32))               ; 4 * node-size
  (spjump .SPvalues))


;;; Store a 53-bit mantissa (hi:25 + lo:28) into a two-digit bignum.
;;; On ARM64, a 64-bit store at the data offset writes both 32-bit digits.
(defarm64lapfunction make-big-53 ((hi arg_x) (lo arg_y) (big arg_z))
  ;; Construct 53-bit value: hi << 28 | lo
  (and imm1 lo (:$ #x0FFFFFFF))         ; lo 28 bits
  (orr imm1 imm1 (:lsl hi (:$ 28)))     ; full 53-bit value
  ;; 64-bit store: low 32 bits = digit 0, high 32 bits = digit 1
  (str imm1 (:@ big (:$ arm64::misc-data-offset)))
  (ret))


;;; Count leading zeros in double-float significand.
(defarm64lapfunction dfloat-significand-zeros ((dfloat arg_z))
  (ldr imm0 (:@ dfloat (:$ arm64::double-float.value)))
  ;; Clear sign and exponent (top 12 bits), shift mantissa to top
  (lsl imm0 imm0 (:$ 12))
  (clz arg_z imm0)
  (ret))

;;; Count leading zeros in single-float significand.
;;; ARM64: single-float is immediate, value in bits 0-31.
(defarm64lapfunction sfloat-significand-zeros ((sfloat arg_z))
  (and imm0 sfloat (:$ #xFFFFFFFF))     ; extract 32-bit float value
  ;; Clear sign and exponent (top 9 bits of 32-bit float)
  (lsl imm0 imm0 (:$ (+ 32 9)))         ; shift to top of 64-bit reg
  (clz arg_z imm0)
  (ret))


;;; Scale a double-float by a power of 2.
;;; Multiplies float by 2^int by constructing a power-of-2 double.
(defarm64lapfunction %%scale-dfloat! ((float arg_x) (int arg_y) (result arg_z))
  (get-double-float d0 float)
  ;; Construct 2^int: IEEE double with exponent = int, mantissa = 0
  ;; Place exponent at bits 52-62 (shift int left by 52)
  (lsl imm0 int (:$ 52))
  (fmov d1 imm0)                        ; d1 = 2^int
  (fmul d0 d1 d0)                       ; d0 = float * 2^int
  (put-double-float d0 result)
  (ret))


;;; Scale a single-float by a power of 2.
(defarm64lapfunction %%scale-sfloat! ((float arg_x) (int arg_y) (result arg_z))
  ;; Get the float value
  (get-single-float s0 float)           ; fmov s0, float
  ;; Construct 2^int as single-float: exponent = int at bits 23-30
  (lsl imm0 int (:$ ieee-single-float-exponent-offset))
  (fmov s2 imm0)                        ; s2 = 2^int
  (fmul s0 s0 s2)
  ;; Reconstruct tagged single-float
  (fmov arg_z s0)
  (movk arg_z (:$ (ash arm64::tag-single-float 8)) (:lsl 48))
  (ret))


;;; Copy double-float value from f1 to f2.
(defarm64lapfunction %copy-double-float ((f1 arg_y) (f2 arg_z))
  (ldr imm0 (:@ f1 (:$ arm64::double-float.value)))
  (str imm0 (:@ f2 (:$ arm64::double-float.value)))
  (ret))

;;; Copy single-float: on ARM64, single-float is immediate, just return f1.
(defarm64lapfunction %copy-short-float ((f1 arg_y) (f2 arg_z))
  (mov arg_z arg_y)
  (ret))


;;; Extract biased exponent from double-float (11 bits).
(defarm64lapfunction %double-float-exp ((n arg_z))
  (ldr imm0 (:@ n (:$ arm64::double-float.value)))
  ;; Shift out sign bit (63), keep exponent (62-52)
  (lsl imm0 imm0 (:$ 1))                ; remove sign
  (lsr arg_z imm0 (:$ 53))              ; right-justify 11-bit exponent
  (ret))


;;; Set the biased exponent of a double-float.
(defarm64lapfunction set-%double-float-exp ((float arg_y) (exp arg_z))
  (ldr imm0 (:@ float (:$ arm64::double-float.value)))
  ;; Clear exponent bits (62-52): construct mask
  (lri imm1 #x800FFFFFFFFFFFFF)         ; sign + mantissa mask (clear exp)
  (and imm0 imm0 imm1)                  ; clear exponent
  ;; Insert new exponent
  (and imm1 exp (:$ #x7FF))             ; mask to 11 bits
  (orr imm0 imm0 (:lsl imm1 (:$ 52)))  ; insert at bits 62-52
  (str imm0 (:@ float (:$ arm64::double-float.value)))
  (ret))


;;; Extract biased exponent from single-float (8 bits).
;;; ARM64: single-float is immediate, value in bits 0-31.
(defarm64lapfunction %short-float-exp ((n arg_z))
  ;; Float value bits 30-23 = exponent
  (lsl imm0 n (:$ 33))                  ; shift out tag+sign, exponent at top
  (lsr arg_z imm0 (:$ 56))              ; right-justify 8-bit exponent
  (ret))


;;; Set the biased exponent of a single-float (immediate).
(defarm64lapfunction set-%short-float-exp ((float arg_y) (exp arg_z))
  ;; Clear exponent bits (30-23) in float
  (lri imm0 #x7F800000)                 ; exponent mask
  (bic imm1 float imm0)                 ; clear exponent bits
  ;; Insert new exponent
  (and imm2 exp (:$ #xFF))              ; mask to 8 bits
  (orr arg_z imm1 (:lsl imm2 (:$ 23))) ; insert at bits 30-23
  (ret))


;;; Convert single-float to double-float.
(defarm64lapfunction %short-float->double-float ((src arg_y) (result arg_z))
  (get-single-float s0 src)
  (fcvt d1 s0)                          ; single → double
  (put-double-float d1 result)
  (ret))


;;; Convert double-float to single-float.
;;; ARM64: result is an immediate tagged single-float.
(defarm64lapfunction %double-float->short-float ((src arg_y) (result arg_z))
  (get-double-float d0 src)
  (fcvt s1 d0)                          ; double → single
  ;; Reconstruct tagged single-float
  (fmov arg_z s1)
  (movk arg_z (:$ (ash arm64::tag-single-float 8)) (:lsl 48))
  (ret))


;;; Convert fixnum to single-float (store in result).
;;; ARM64: result is ignored (was heap-allocated box on ARM32);
;;; we return an immediate tagged single-float.
(defarm64lapfunction %int-to-sfloat! ((int arg_y) (sfloat arg_z))
  ;; fixnumshift=0: int IS the integer
  (scvtf s0 int)                        ; signed int → single float
  (fmov arg_z s0)
  (movk arg_z (:$ (ash arm64::tag-single-float 8)) (:lsl 48))
  (ret))

;;; Convert fixnum to immediate single-float (64-bit path).
;;; Called by %fixnum-sfloat on 64-bit targets.
(defarm64lapfunction %int-to-sfloat ((int arg_z))
  (scvtf s0 int)
  (fmov arg_z s0)
  (movk arg_z (:$ (ash arm64::tag-single-float 8)) (:lsl 48))
  (ret))

;;; Convert fixnum to double-float (store in result).
(defarm64lapfunction %int-to-dfloat ((int arg_y) (dfloat arg_z))
  (scvtf d0 int)                        ; signed int → double float
  (put-double-float d0 dfloat)
  (ret))


;;; Check for floating-point exceptions after FFI call.
;;; Read FPSR status bits, AND with enabled exception mask from tcr.lisp-fpscr.
(defarm64lapfunction %ffi-exception-status ()
  ;; Read FPSR (cumulative exception flags in bits 4-0)
  (mrs imm2 (:$ arm64::fpsr-sysreg))
  (and imm0 imm2 (:$ #x1F))            ; exception status bits (IOC,DZC,OFC,UFC,IXC)
  ;; Read enabled exceptions from TCR
  (ldr imm1 (:@ rcontext (:$ arm64::tcr.lisp-fpscr)))
  (lsr imm1 imm1 (:$ 8))               ; enable bits in high byte
  (and imm1 imm1 (:$ #x1F))            ; mask to 5 enable bits
  ;; Check if any enabled exception occurred
  (ands imm0 imm0 imm1)
  (b.ne @exception)
  (mov arg_z rnil)
  (ret)
  @exception
  ;; Return status as fixnum, clear FPSR exception bits
  (mov arg_z imm0)                       ; fixnumshift=0, already a fixnum
  (bic imm2 imm2 (:$ #x1F))            ; clear exception bits
  (msr (:$ arm64::fpsr-sysreg) imm2)           ; write back cleaned FPSR
  (ret))


;;; Lisp functions for float exception reporting (same as ARM32)
(defun %sf-check-exception-1 (operation op0 fp-status)
  (when fp-status
    (let* ((condition-name (fp-condition-name-from-fpscr-status fp-status)))
      (error (make-instance (or condition-name 'arithmetic-error)
                            :operation operation
                            ;; ARM64: single-float is immediate, no heap copy needed
                            :operands (list op0))))))

(defun %sf-check-exception-2 (operation op0 op1 fp-status)
  (when fp-status
    (let* ((condition-name (fp-condition-name-from-fpscr-status fp-status)))
      (error (make-instance (or condition-name 'arithmetic-error)
                            :operation operation
                            ;; ARM64: single-float is immediate, no heap copy needed
                            :operands (list op0 op1))))))

(defun %df-check-exception-1 (operation op0 fp-status)
  (when fp-status
    (let* ((condition-name (fp-condition-name-from-fpscr-status fp-status)))
      (error (make-instance (or condition-name 'arithmetic-error)
                            :operation operation
                            :operands (list (%copy-double-float op0 (%make-dfloat))))))))

(defun %df-check-exception-2 (operation op0 op1 fp-status)
  (when fp-status
    (let* ((condition-name (fp-condition-name-from-fpscr-status fp-status)))
      (error (make-instance (or condition-name 'arithmetic-error)
                            :operation operation
                            :operands (list (%copy-double-float op0 (%make-dfloat))
                                            (%copy-double-float op1 (%make-dfloat))))))))


(defvar *rounding-mode-alist*
  '((:nearest . 0) (:positive . 1) (:negative . 2) (:zero . 3)))


;;; AArch64 FPCR/FPSR handling.
;;; FPCR (control): rounding mode in bits 23-22, exception trap enables in bits 12-8.
;;; FPSR (status): cumulative exception flags in bits 4-0.
;;; We keep the logical exception enable mask in tcr.lisp-fpscr (same as ARM32).

(defun get-fpu-mode (&optional (mode nil mode-p))
  (let* ((flags (%get-fpscr-control)))
    (declare (fixnum flags))
    (let* ((rounding-mode
            (car (nth (ldb (byte 2 22) flags) *rounding-mode-alist*)))
           (overflow (logbitp arm64::ofe flags))
           (underflow (logbitp arm64::ufe flags))
           (division-by-zero (logbitp arm64::dze flags))
           (invalid (logbitp arm64::ioe flags))
           (inexact (logbitp arm64::ixe flags)))
      (if mode-p
        (ecase mode
          (:rounding-mode rounding-mode)
          (:overflow overflow)
          (:underflow underflow)
          (:division-by-zero division-by-zero)
          (:invalid invalid)
          (:inexact inexact))
        `(:rounding-mode ,rounding-mode
          :overflow ,overflow
          :underflow ,underflow
          :division-by-zero ,division-by-zero
          :invalid ,invalid
          :inexact ,inexact)))))

(defun set-fpu-mode (&key (rounding-mode :nearest rounding-p)
                          (overflow t overflow-p)
                          (underflow t underflow-p)
                          (division-by-zero t zero-p)
                          (invalid t invalid-p)
                          (inexact t inexact-p))
  (let* ((current (%get-fpscr-control))
         (new current))
    (declare (fixnum current new))
    (when rounding-p
      (let* ((rc-bits (or
                       (cdr (assoc rounding-mode *rounding-mode-alist*))
                       (error "Unknown rounding mode: ~s" rounding-mode))))
        (declare (fixnum rc-bits))
        (setq new (dpb rc-bits (byte 2 22) new))))
    (when invalid-p
      (if invalid
        (bitsetf arm64::ioe new)
        (bitclrf arm64::ioe new)))
    (when overflow-p
      (if overflow
        (bitsetf arm64::ofe new)
        (bitclrf arm64::ofe new)))
    (when underflow-p
      (if underflow
        (bitsetf arm64::ufe new)
        (bitclrf arm64::ufe new)))
    (when zero-p
      (if division-by-zero
        (bitsetf arm64::dze new)
        (bitclrf arm64::dze new)))
    (when inexact-p
      (if inexact
        (bitsetf arm64::ixe new)
        (bitclrf arm64::ixe new)))
    (unless (= current new)
      (%set-fpscr-control new))
    (%get-fpscr)))


;;; Get rounding mode from FPCR + exception enable mask from tcr.lisp-fpscr.
(defarm64lapfunction %get-fpscr-control ()
  (mrs imm0 (:$ arm64::fpcr-sysreg))           ; read FPCR
  (and imm0 imm0 (:$ (ash 3 22)))       ; rounding mode (bits 23-22)
  (ldr imm1 (:@ rcontext (:$ arm64::tcr.lisp-fpscr)))
  (and imm1 imm1 (:$ #x1F00))          ; exception enable bits (bits 12-8)
  (orr arg_z imm0 imm1)                 ; combine
  (ret))

;;; Get cumulative exception status from FPSR.
(defarm64lapfunction %get-fpscr-status ()
  (mrs imm0 (:$ arm64::fpsr-sysreg))
  (and arg_z imm0 (:$ #x1F))            ; exception status bits
  (ret))

;;; Set cumulative exception status in FPSR.
(defarm64lapfunction %set-fpscr-status ((new arg_z))
  (mrs imm1 (:$ arm64::fpsr-sysreg))           ; read current FPSR
  (bic imm1 imm1 (:$ #x1F))            ; clear status bits
  (and imm0 new (:$ #x1F))              ; mask new status
  (orr imm0 imm0 imm1)                  ; merge
  (msr (:$ arm64::fpsr-sysreg) imm0)           ; write FPSR
  (ret))

;;; Set rounding mode in FPCR and exception enables in tcr.lisp-fpscr.
(defarm64lapfunction %set-fpscr-control ((new arg_z))
  ;; Store exception enables in TCR
  (and imm0 new (:$ #x1F00))            ; enable bits
  (str imm0 (:@ rcontext (:$ arm64::tcr.lisp-fpscr)))
  ;; Update rounding mode in FPCR
  (mrs imm1 (:$ arm64::fpcr-sysreg))           ; read current FPCR
  (bic imm1 imm1 (:$ (ash 3 22)))       ; clear rounding mode
  (and imm0 new (:$ (ash 3 22)))        ; new rounding mode
  (orr imm0 imm1 imm0)                  ; merge
  (msr (:$ arm64::fpcr-sysreg) imm0)           ; write FPCR
  (ret))

;;; Get combined FPSR status + tcr.lisp-fpscr enables.
(defarm64lapfunction %get-fpscr ()
  (mrs imm0 (:$ arm64::fpsr-sysreg))           ; FPSR (status in low bits)
  (and imm0 imm0 (:$ #x1F))            ; status bits only
  (ldr imm1 (:@ rcontext (:$ arm64::tcr.lisp-fpscr)))
  (and imm1 imm1 (:$ #x1F00))          ; enable bits
  (orr arg_z imm1 imm0)                 ; combine
  ;; Also include rounding mode from FPCR
  (mrs imm0 (:$ arm64::fpcr-sysreg))
  (and imm0 imm0 (:$ (ash 3 22)))
  (orr arg_z arg_z imm0)
  (ret))


(defun fp-condition-name-from-fpscr-status (status)
  (cond
    ((logbitp arm64::ioc status) 'floating-point-invalid-operation)
    ((logbitp arm64::dzc status) 'division-by-zero)
    ((logbitp arm64::ofc status) 'floating-point-overflow)
    ((logbitp arm64::ufc status) 'floating-point-underflow)
    ((logbitp arm64::ixc status) 'floating-point-inexact)))


;;; Load a double-float from a macptr at byte-offset.
(defarm64lapfunction %double-float-from-macptr! ((ptr arg_x) (byte-offset arg_y) (dest arg_z))
  (ldr imm0 (:@ ptr (:$ arm64::macptr.address)))
  (ldr imm1 (:@ imm0 byte-offset))      ; load 64-bit value from ptr+offset
  (str imm1 (:@ dest (:$ arm64::double-float.value)))
  (ret))


;;; Convert single-float at macptr to double-float at another macptr.
(defarm64lapfunction %single-float-ptr->double-float-ptr ((single arg_y) (double arg_z))
  (check-nargs 2)
  (macptr-ptr imm0 single)
  (ldr s0 (:@ imm0 (:$ 0)))
  (fcvt d1 s0)                          ; single → double
  (macptr-ptr imm0 double)
  (str d1 (:@ imm0 (:$ 0)))
  (ret))

;;; Convert double-float at macptr to single-float at another macptr.
(defarm64lapfunction %double-float-ptr->single-float-ptr ((double arg_y) (single arg_z))
  (check-nargs 2)
  (macptr-ptr imm0 double)
  (ldr d0 (:@ imm0 (:$ 0)))
  (macptr-ptr imm0 single)
  (fcvt s2 d0)                          ; double → single
  (str s2 (:@ imm0 (:$ 0)))
  (ret))


(defarm64lapfunction %set-ieee-single-float-from-double ((src arg_y) (macptr arg_z))
  (check-nargs 2)
  (macptr-ptr imm0 macptr)
  (get-double-float d1 src)
  (fcvt s0 d1)                          ; double → single
  (str s0 (:@ imm0 (:$ 0)))
  (ret))


;;; ARM64: single-float is immediate.  These LAP helpers convert between
;;; the tagged immediate representation and raw 32-bit IEEE bit patterns.

(defarm64lapfunction %single-float-bits ((f arg_z))
  ;; Extract raw 32-bit IEEE value from immediate single-float
  (and arg_z f (:$ #xFFFFFFFF))
  (ret))

(defarm64lapfunction %host-single-float-from-u32 ((u32 arg_z))
  ;; Construct immediate single-float from raw 32-bit IEEE value
  (and arg_z u32 (:$ #xFFFFFFFF))       ; mask to 32 bits
  (movk arg_z (:$ (ash arm64::tag-single-float 8)) (:lsl 48))
  (ret))

(defun host-single-float-from-unsigned-byte-32 (u32)
  (%host-single-float-from-u32 u32))

(defun single-float-bits (f)
  (%single-float-bits f))


(defun double-float-bits (f)
  (values (uvref f arm64::double-float.val-high-cell)
          (uvref f arm64::double-float.val-low-cell)))

(defun double-float-from-bits (high low)
  (let* ((f (%make-dfloat)))
    (setf (uvref f arm64::double-float.val-high-cell) high
          (uvref f arm64::double-float.val-low-cell) low)
    f))


;;; Double-float sign: return T if negative, NIL otherwise.
(defarm64lapfunction %double-float-sign ((n arg_z))
  (ldr imm0 (:@ n (:$ arm64::double-float.value)))
  (tst imm0 (:$ (ash 1 63)))            ; test sign bit
  (mov arg_z rnil)
  (b.eq @done)
  (add arg_z arg_z (:$ arm64::t-offset))
  @done
  (ret))

;;; Single-float sign: test bit 31 of immediate value.
(defarm64lapfunction %short-float-sign ((n arg_z))
  (tst n (:$ #x80000000))               ; test sign bit
  (mov arg_z rnil)
  (b.eq @done)
  (add arg_z arg_z (:$ arm64::t-offset))
  @done
  (ret))


;;; Single-float square root with exception check.
(defarm64lapfunction %single-float-sqrt! ((src arg_y) (dest arg_z))
  (build-lisp-frame)
  (get-single-float s0 src)
  ;; Clear FPSR exception bits
  (mrs imm0 (:$ arm64::fpsr-sysreg))
  (bic imm0 imm0 (:$ #x1F))
  (msr (:$ arm64::fpsr-sysreg) imm0)
  (fsqrt s1 s0)
  ;; Check for FPU exceptions
  (spcall .SPcheck-fpu-exception)
  ;; Reconstruct tagged single-float
  (fmov arg_z s1)
  (movk arg_z (:$ (ash arm64::tag-single-float 8)) (:lsl 48))
  (return-lisp-frame))


;;; Double-float square root with exception check.
(defarm64lapfunction %double-float-sqrt! ((src arg_y) (dest arg_z))
  (build-lisp-frame)
  (get-double-float d0 src)
  ;; Clear FPSR exception bits
  (mrs imm0 (:$ arm64::fpsr-sysreg))
  (bic imm0 imm0 (:$ #x1F))
  (msr (:$ arm64::fpsr-sysreg) imm0)
  (fsqrt d1 d0)
  ;; Check for FPU exceptions
  (spcall .SPcheck-fpu-exception)
  (put-double-float d1 dest)
  (return-lisp-frame))


; End of arm64-float.lisp
