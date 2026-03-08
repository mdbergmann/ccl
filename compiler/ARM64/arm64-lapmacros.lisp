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


(eval-when (:compile-toplevel :load-toplevel :execute)
  (require "ARM64-LAP"))


;;; On ARM64, nargs = n * node-size (= n * 8).
(defarm64lapmacro set-nargs (n)
  (check-type n (unsigned-byte 8))
  `(mov nargs (:$ ,(ash n arm64::word-shift))))

;;; ARM64: no conditional execution; use branch-around + UUO.
(defarm64lapmacro check-nargs (min &optional (max min))
  (let* ((ok (gensym)))
    (if (eq max min)
      `(progn
        (cmp nargs (:$ ,(ash min arm64::word-shift)))
        (b.eq ,ok)
        (uuo-error-wrong-nargs)
        ,ok)
      (if (null max)
        (unless (= min 0)
          (let ((ok1 (gensym)))
            `(progn
              (cmp nargs (:$ ,(ash min arm64::word-shift)))
              (b.hs ,ok1)
              (uuo-error-wrong-nargs)
              ,ok1)))
        (if (= min 0)
          `(progn
            (cmp nargs (:$ ,(ash max arm64::word-shift)))
            (b.ls ,ok)
            (uuo-error-wrong-nargs)
            ,ok)
          (let ((ok1 (gensym))
                (ok2 (gensym)))
            `(progn
              (cmp nargs (:$ ,(ash min arm64::word-shift)))
              (b.hs ,ok1)
              (uuo-error-wrong-nargs)
              ,ok1
              (cmp nargs (:$ ,(ash max arm64::word-shift)))
              (b.ls ,ok2)
              (uuo-error-wrong-nargs)
              ,ok2)))))))

;;; ARM64 lisp frame: 2 slots (savevsp + savelr), 16 bytes total.
;;; No marker word, no fn save (unlike ARM32's 4-slot frame).
(defarm64lapmacro build-lisp-frame (&optional (vsp-arg 'vsp))
  `(stp ,vsp-arg lr (:@! sp (:$ (- arm64::lisp-frame.size)))))

(defarm64lapmacro restore-lisp-frame ()
  `(ldp vsp lr (:@+ sp (:$ arm64::lisp-frame.size))))

(defarm64lapmacro return-lisp-frame ()
  `(progn
    (ldp vsp lr (:@+ sp (:$ arm64::lisp-frame.size)))
    (ret)))

(defarm64lapmacro discard-lisp-frame ()
  `(add sp sp (:$ arm64::lisp-frame.size)))


;;; Push/pop using pre-decrement/post-increment on a stack pointer register.
(defarm64lapmacro push1 (src stack)
  `(str ,src (:@! ,stack (:$ (- arm64::node-size)))))

(defarm64lapmacro pop1 (dest stack)
  `(ldr ,dest (:@+ ,stack (:$ arm64::node-size))))


;;; Cons cell access.  TBI: car at offset 0, cdr at -8.
(defarm64lapmacro %car (dest node)
  `(ldr ,dest (:@ ,node (:$ arm64::cons.car))))

(defarm64lapmacro %cdr (dest node)
  `(ldur ,dest (:@ ,node (:$ arm64::cons.cdr))))


;;; Tag extraction.  TBI tags occupy bits 56-63.
(defarm64lapmacro extract-lisptag (dest node)
  `(lsr ,dest ,node (:$ arm64::tag-shift)))

(defarm64lapmacro extract-fulltag (dest node)
  `(lsr ,dest ,node (:$ arm64::tag-shift)))

;;; Subtag: low byte of the header word (at offset -8 from tagged pointer).
(defarm64lapmacro extract-subtag (dest node)
  `(progn
    (ldur ,dest (:@ ,node (:$ arm64::misc-subtag-offset)))
    (and ,dest ,dest (:$ #xff))))

;;; Typecode: for fixnums return tag byte; for uvectors return subtag.
(defarm64lapmacro extract-typecode (dest node)
  (let* ((done (gensym)))
    `(progn
      (lsr ,dest ,node (:$ arm64::tag-shift))
      (tst ,dest (:$ arm64::uvector-ref))
      (b.eq ,done)
      (ldur ,dest (:@ ,node (:$ arm64::misc-subtag-offset)))
      (and ,dest ,dest (:$ #xff))
      ,done)))

;;; Fixnum test: tag byte must be 0x00 (positive) or 0xFF (negative).
;;; After LSR 56, positive fixnum has tag=0, negative has tag=0xFF.
;;; Check: ((tag + 1) AND 0xFE) == 0 ↔ tag is 0 or 0xFF.
(defarm64lapmacro test-fixnum (node &optional (temp 'imm0))
  `(progn
    (lsr ,temp ,node (:$ arm64::tag-shift))
    (add ,temp ,temp (:$ 1))
    (tst ,temp (:$ #xfe))))

(defarm64lapmacro trap-unless-fixnum (node &optional (temp 'imm0))
  (let* ((ok (gensym)))
    `(progn
      (test-fixnum ,node ,temp)
      (b.eq ,ok)
      (uuo-error-reg-not-lisptag ,node (:$ arm64::tag-positive-fixnum))
      ,ok)))

(defarm64lapmacro trap-unless-lisptag= (node tag &optional (immreg 'imm0))
  (let* ((ok (gensym)))
    `(progn
      (extract-lisptag ,immreg ,node)
      (cmp ,immreg (:$ ,tag))
      (b.eq ,ok)
      (uuo-error-reg-not-lisptag ,node (:$ ,tag))
      ,ok)))

(defarm64lapmacro trap-unless-fulltag= (node tag &optional (immreg 'imm0))
  (let* ((ok (gensym)))
    `(progn
      (extract-fulltag ,immreg ,node)
      (cmp ,immreg (:$ ,tag))
      (b.eq ,ok)
      (uuo-error-reg-not-fulltag ,node (:$ ,tag))
      ,ok)))

(defarm64lapmacro trap-unless-xtype= (node tag &optional (immreg 'imm0))
  (let* ((ok (gensym)))
    `(progn
      (extract-typecode ,immreg ,node)
      (cmp ,immreg (:$ ,tag))
      (b.eq ,ok)
      (uuo-error-reg-not-xtype ,node (:$ ,tag))
      ,ok)))


;;; Load a constant from the function's constants vector.
(defarm64lapmacro load-constant (dest constant)
  `(ldr ,dest (:@ fn ',constant)))

;;; Call a named symbol's function.
(defarm64lapmacro call-symbol (function-name)
  `(progn
    (load-constant fname ,function-name)
    (ldr nfn (:@ fname (:$ arm64::symbol.fcell)))
    (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
    (blr lr)))

;;; Call a subprimitive via symbol.
(defarm64lapmacro sp-call-symbol (function-name)
  `(progn
    (load-constant fname ,function-name)
    (ldr nfn (:@ fname (:$ arm64::symbol.fcell)))
    (ldr rt (:@ nfn (:$ arm64::function.entrypoint)))
    (blr rt)))


;;; Vector header access.  Header is at offset -8 from tagged pointer.
(defarm64lapmacro getvheader (dest src)
  `(ldur ,dest (:@ ,src (:$ arm64::misc-header-offset))))

;;; Header size: raw element count from header word.
;;; Header format: (subtag << subtag-shift) | element_count.
;;; Extract bits 0-55 (the element count), discarding the subtag in the high byte.
(defarm64lapmacro header-size (dest vheader)
  `(ubfx ,dest ,vheader (:$ 0) (:$ arm64::subtag-shift)))

;;; Header length: fixnum element count.
;;; With fixnumshift=0, fixnum representation = raw value,
;;; so same as header-size.
(defarm64lapmacro header-length (dest vheader)
  `(ubfx ,dest ,vheader (:$ 0) (:$ arm64::subtag-shift)))

;;; Extract subtag byte from a header word as a fixnum.
;;; Since fixnumshift=0, the subtag byte is already a fixnum.
(defarm64lapmacro header-subtag[fixnum] (dest vheader)
  `(and ,dest ,vheader (:$ arm64::subtag-mask)))

(defarm64lapmacro vector-size (dest v vheader)
  `(progn
    (getvheader ,vheader ,v)
    (header-size ,dest ,vheader)))

(defarm64lapmacro vector-length (dest v vheader)
  `(progn
    (getvheader ,vheader ,v)
    (header-length ,dest ,vheader)))


;;; 32-bit element access at a variable fixnum index.
;;; ARM64: fixnumshift=0, so index is the raw element number.
;;; Scale by 4 (32-bit elements); misc-data-offset is 0.
;;; Uses LDR32/STR32 for proper 32-bit (W-register) loads/stores.
(defarm64lapmacro vref32 (dest miscobj index scaled-idx)
  `(progn
    (lsl ,scaled-idx ,index (:$ 2))
    (ldr32 ,dest (:@ ,miscobj ,scaled-idx))))

(defarm64lapmacro vset32 (src miscobj index scaled-idx)
  `(progn
    (lsl ,scaled-idx ,index (:$ 2))
    (str32 ,src (:@ ,miscobj ,scaled-idx))))

(defarm64lapmacro extract-lowbyte (dest src)
  `(and ,dest ,src (:$ #xff)))

;;; Box/unbox fixnum: identity on ARM64 (fixnumshift=0).
(defarm64lapmacro unbox-fixnum (dest src)
  `(mov ,dest ,src))

(defarm64lapmacro box-fixnum (dest src)
  `(mov ,dest ,src))


;;; Unbox a character: shift right by charcode-shift (8).
(defarm64lapmacro unbox-base-char (dest src &optional check)
  `(progn
    ,@(if check
        `((trap-unless-xtype= ,src arm64::subtag-character ,dest)))
    (lsr ,dest ,src (:$ arm64::charcode-shift))))


;;; Kernel globals are at negative offsets from rnil.
;;; LDUR/STUR have a ±256 byte immediate range.  For larger offsets,
;;; subtract the offset magnitude from rnil into a temp, then load.
(defarm64lapmacro ref-global (reg sym)
  (let* ((offset (arm64::%kernel-global sym)))
    (if (and (>= offset -256) (<= offset 255))
      `(ldur ,reg (:@ rnil (:$ ,offset)))
      `(progn
        (sub ,reg rnil (:$ ,(- offset)))
        (ldr ,reg (:@ ,reg (:$ 0)))))))

(defarm64lapmacro set-global (reg sym &optional (temp 'imm0))
  (let* ((offset (arm64::%kernel-global sym)))
    (if (and (>= offset -256) (<= offset 255))
      `(stur ,reg (:@ rnil (:$ ,offset)))
      `(progn
        (sub ,temp rnil (:$ ,(- offset)))
        (str ,reg (:@ ,temp (:$ 0)))))))

(defarm64lapmacro load-global-address (reg sym)
  (let* ((offset (arm64::%kernel-global sym)))
    (if (< (abs offset) 4096)
      `(sub ,reg rnil (:$ ,(- offset)))
      `(progn
        (lri ,reg ,(- offset))
        (sub ,reg rnil ,reg)))))


;;; Condition → boolean.  ARM64: no conditional add, use branch-around.
(defarm64lapmacro cond->boolean (cc dest rx ry)
  (let* ((done (gensym)))
    `(progn
      (cmp ,rx ,ry)
      (mov ,dest rnil)
      (b (:~ ,cc) ,done)
      (add ,dest rnil (:$ arm64::t-offset))
      ,done)))


(defarm64lapmacro repeat (n inst)
  (let* ((insts ()))
    (dotimes (i n `(progn ,@(nreverse insts)))
      (push inst insts))))


;;; Single-float is an IMMEDIATE on ARM64 (tag #x10), not heap-allocated.
;;; The float value is in bits 0-31 of the tagged word.
(defarm64lapmacro get-single-float (dest node)
  `(fmov ,dest ,node))

;;; Double-float: data at misc-data-offset (0) from tagged pointer.
;;; TBI means the tagged pointer works as an address directly.
(defarm64lapmacro get-double-float (dest node)
  `(ldr ,dest (:@ ,node (:$ arm64::double-float.value))))

;;; Store single-float back into a tagged immediate.
(defarm64lapmacro put-single-float (src dest)
  `(fmov ,dest ,src))

;;; Store double-float value into a heap-allocated double-float.
(defarm64lapmacro put-double-float (src node)
  `(str ,src (:@ ,node (:$ arm64::double-float.value))))


;;; Bignum digit manipulation.
;;; On ARM64 with fixnumshift=0, fixnum values are direct integers.
;;; "digit-h" extracts high 16 bits as a fixnum.
(defarm64lapmacro digit-h (dest src)
  `(progn
    (lsr ,dest ,src (:$ 16))
    (and ,dest ,dest (:$ #xffff))))

;;; "digit-l" extracts low 16 bits as a fixnum.
(defarm64lapmacro digit-l (dest src)
  `(and ,dest ,src (:$ #xffff)))

;;; Compose a 32-bit digit from high and low 16-bit fixnums.
(defarm64lapmacro compose-digit (dest high low)
  `(progn
    (and ,dest ,low (:$ #xffff))
    (orr ,dest ,dest (:lsl ,high (:$ 16)))))


(defarm64lapmacro macptr-ptr (dest macptr)
  `(ldr ,dest (:@ ,macptr (:$ arm64::macptr.address))))

;;; Node-sized element access (8 bytes per slot).
(defarm64lapmacro svref (dest index vector)
  `(ldr ,dest (:@ ,vector (:$ (+ (* 8 ,index) arm64::misc-data-offset)))))

;;; Immediate indices don't account for the entrypoint slot.
(defarm64lapmacro nth-immediate (dest index vector)
  `(svref ,dest (1+ ,index) ,vector))

(defarm64lapmacro svset (new-value index vector)
  `(str ,new-value (:@ ,vector (:$ (+ (* 8 ,index) arm64::misc-data-offset)))))


;;; Push register arguments onto vsp.
;;; ARM64 has 3 arg regs: arg_x (x13), arg_y (x14), arg_z (x15).
;;; nargs = count * 8 (node-size).
(defarm64lapmacro vpush-argregs ()
  (let* ((none (gensym))
         (one (gensym))
         (two (gensym)))
    `(progn
      (cmp nargs (:$ 0))
      (b.eq ,none)
      (cmp nargs (:$ ,(ash 2 arm64::word-shift)))
      (b.lo ,one)
      (b.eq ,two)
      (str arg_x (:@! vsp (:$ (- arm64::node-size))))
      ,two
      (str arg_y (:@! vsp (:$ (- arm64::node-size))))
      ,one
      (str arg_z (:@! vsp (:$ (- arm64::node-size))))
      ,none)))


;;; Set the most significant bit (bit 63) in a 64-bit register.
(defarm64lapmacro load-highbit (dest)
  `(mov ,dest (:$ ,(ash 1 63))))


(defarm64lapmacro u32-ref (dest index vector)
  `(ldr ,dest (:@ ,vector (:$ (+ (* 4 ,index) arm64::misc-data-offset)))))

(defarm64lapmacro u32-set (new-value index vector)
  `(str ,new-value (:@ ,vector (:$ (+ (* 4 ,index) arm64::misc-data-offset)))))


;;; Load a 64-bit immediate into a register.
;;; Try single MOV first (handles small values, logical immediates,
;;; and small negatives).  Otherwise use MOVZ+MOVK sequence.
(defarm64lapmacro lri (reg val)
  (setq val (logand (eval val) #xffffffffffffffff))
  (let* ((signed-val (if (logbitp 63 val) (- val (ash 1 64)) val)))
    ;; Single MOV: small non-negative, small negative, or logical immediate
    (if (or (< val #x10000)
            (and (< signed-val 0) (>= signed-val -65536))
            (and (not (zerop val))
                 (not (= val #xffffffffffffffff))
                 (arm64::encode-logical-immediate val)))
      `(mov ,reg (:$ ,signed-val))
      ;; MOVZ + MOVK sequence: use the first non-zero halfword as MOVZ,
      ;; then MOVK for remaining non-zero halfwords.
      (let* ((hw0 (logand val #xffff))
             (hw1 (logand (ash val -16) #xffff))
             (hw2 (logand (ash val -32) #xffff))
             (hw3 (logand (ash val -48) #xffff))
             (halfwords (list (cons hw0 0) (cons hw1 16)
                              (cons hw2 32) (cons hw3 48)))
             (non-zero (remove-if #'(lambda (p) (zerop (car p))) halfwords)))
        (if (null non-zero)
          `(mov ,reg (:$ 0))
          (collect ((forms))
            ;; First non-zero halfword: MOVZ
            (let* ((first (car non-zero)))
              (if (zerop (cdr first))
                (forms `(movz ,reg (:$ ,(car first))))
                (forms `(movz ,reg (:$ ,(car first)) (:lsl ,(cdr first))))))
            ;; Remaining non-zero halfwords: MOVK
            (dolist (hw (cdr non-zero))
              (if (zerop (cdr hw))
                (forms `(movk ,reg (:$ ,(car hw))))
                (forms `(movk ,reg (:$ ,(car hw)) (:lsl ,(cdr hw))))))
            `(progn ,@(forms))))))))


;;; Push/pop on the value stack (vsp).
;;; ARM64: node-size = 8.  Pre-decrement push, post-increment pop.
(defarm64lapmacro vpush1 (src)
  `(str ,src (:@! vsp (:$ (- arm64::node-size)))))

(defarm64lapmacro vpop1 (dest)
  `(ldr ,dest (:@+ vsp (:$ arm64::node-size))))

;;; Jump to a subprimitive (no return).
;;; Loads the subprim address from the TCR subprim table, then branches.
(defarm64lapmacro spjump (spno)
  (let* ((offset (arm64::arm64-subprimitive-offset spno)))
    `(progn
      (ldr rt (:@ rcontext (:$ ,offset)))
      (br rt))))

;;; Call a subprimitive (returns).
;;; Loads the subprim address from the TCR subprim table, then calls.
(defarm64lapmacro spcall (spno)
  (let* ((offset (arm64::arm64-subprimitive-offset spno)))
    `(progn
      (ldr rt (:@ rcontext (:$ ,offset)))
      (blr rt))))


;;; UUO trap pseudo-instructions.
;;; These expand to HLT instructions with specific 16-bit immediate
;;; encodings recognized by the kernel exception handler.
;;; Format: imm16 low 3 bits = format code; bits 3+ = info/subcode.
;;; Nullary format (format=0): info in bits 3-15.

;;; Allocation trap: triggers GC if allocptr < allocbase.
;;; Nullary format, info=0 → imm16=0.
(defarm64lapmacro uuo-alloc-trap ()
  `(hlt (:$ 0)))

;;; GC trap: request a garbage collection.
;;; Nullary format, info=2 → imm16=16.
;;; Expects gc-trap-function code in imm0.
(defarm64lapmacro uuo-gc-trap ()
  `(hlt (:$ 16)))

;;; Debug trap: breakpoint for debugging.
;;; Nullary format, info=3 → imm16=24.
(defarm64lapmacro uuo-debug-trap ()
  `(hlt (:$ 24)))

;;; Kernel service request.
;;; Nullary format, info=7 → imm16=56.
;;; Service code passed in the immediate argument, loaded into imm0.
(defarm64lapmacro uuo-kernel-service (imm)
  `(progn
     (mov imm0 ,imm)
     (hlt (:$ 56))))


(provide "ARM64-LAPMACROS")

;;; end of arm64-lapmacros.lisp
