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

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require "ARM64-ARCH"))

(in-package "ARM64")

(defun count-trailing-zeros-64 (u64)
  (do* ((i 0 (1+ i)))
       ((or (= i 64) (logbitp i u64))
        i)
    (declare (fixnum i))))

(defun count-leading-zeros-64 (u64)
  (do* ((count 0 (1+ count))
        (i 63 (1- i)))
       ((or (= count 64) (logbitp i u64))
        count)
    (declare (fixnum count i))))

(defun count-leading-zeros-32 (u32)
  (do* ((count 0 (1+ count))
        (i 31 (1- i)))
       ((or (= count 32) (logbitp i u32))
        count)
    (declare (fixnum count i))))

#|
(defun test-ctz ()
  (let* ((n #xffffffffffffffff))
    (loop for i from 0 to 64 do
          (format t "~16,'0x: " n)
          (format t "~d~%" (count-trailing-zeros-64 n))
          (setq n (ldb (byte 64 0) (ash n 1))))))

(defun test-clz ()
  (let* ((all-ones #xffffffffffffffff)
         (n all-ones))
    (loop for i from 0 to 64 do
          (format t "~16,'0x: " n)
          (format t "~2d~%" (count-leading-zeros-64 n))
          (setq n (ldb (byte 64 0) (ash n -1))))))
|#

(defun clear-trailing-ones-64 (u64)
  (ldb (byte 64 0) (logand u64 (1+ u64))))

(defun rotate-right-64 (u64 n)
  (let* ((right (logand n 63))
         (left (logand (- n) 63)))
    (logior (ldb (byte 64 0) (ash u64 (- right)))
            (ldb (byte 64 0) (ash u64 left)))))

;;; Adapted from https://dougallj.wordpress.com/2021/10/30/bit-twiddling-optimising-aarch64-logical-immediate-encoding-and-decoding/

(defun %encode-logical-immediate (u64)
  ;; Consider an ARM64 logical immediate as a pattern of "o" ones preceded
  ;; by "z" more-significant zeroes, repeated to fill a 64-bit integer.
  ;; o > 0, z > 0, and the size (o + z) is a power of two in [2,64]. This
  ;; part of the pattern is encoded in the fields "imms" and "N".
  ;;
  ;; "immr" encodes a further right rotate of the repeated pattern, allowing
  ;; a wide range of useful bitwise constants to be represented.
  ;;
  ;; (The spec describes the "immr" rotate as rotating the "o + z" bit
  ;; pattern before repeating it to fill 64-bits, but, as it's a repeating
  ;; pattern, rotating afterwards is equivalent.)
  ;;
  ;; This encoding is not allowed to represent all-zero or all-one values,
  ;; which must have been excluded prior to calling this function,
  ;;
  ;; To detect an immediate that may be encoded in this scheme, we first
  ;; remove the right-rotate, by rotating such that the least significant
  ;; bit is a one and the most significant bit is a zero.
  ;;
  ;; We do this by clearing any trailing one bits, then counting the
  ;; trailing zeroes. This finds an "edge", where zero goes to one.
  ;; We then rotate the original value right by that amount, moving
  ;; the first one to the least significant bit.
  (let* ((rotation (count-trailing-zeros-64 (clear-trailing-ones-64 u64)))
         (normalized (rotate-right-64 u64 (logand rotation 63)))
         ;; Now we have normalized the value, and determined the
         ;; rotation, we can determine "z" by counting the leading
         ;; zeroes, and "o" by counting the trailing ones. (These will
         ;; both be positive, as we already rejected 0 and ~0, and
         ;; rotated the value to start with a zero and end with a
         ;; one.)
         (zeros (count-leading-zeros-64 normalized))
         (ones (count-trailing-zeros-64 (ldb (byte 64 0) (lognot normalized))))
         (size (+ zeros ones)))
    ;; Detect the repeating pattern (by comparing every repetition to the
    ;; one next to it, using rotate).
    (if (/= (rotate-right-64 u64 (logand size 63)) u64)
      nil
      ;; We do not need to further validate size to ensure it is a
      ;; power of two between 2 and 64. The only "minimal" patterns
      ;; that can repeat to fill a 64-bit value must have a length
      ;; that is a factor of 64 (i.e. it is a power of two in the
      ;; range [1,64]). And our pattern cannot be of length one (as we
      ;; already rejected 0 and ~0).
      ;;
      ;; By "minimal" patterns I refer to patterns which do not
      ;; themselves contain repetitions. For example, '010101' is a
      ;; non-minimal pattern of a non-power-of-two length that can
      ;; pass the above rotational test. It consists of the minimal
      ;; pattern '01'. All our patterns are minimal, as they contain
      ;; only one contiguous run of ones separated by at least one
      ;; zero.
      ;;
      ;; Finally, we encode the values. "rotation" is the amount we
      ;; rotated right by to "undo" the right-rotate encoded in immr,
      ;; so must be negated.
      ;;
      ;; size 2:  N=0 immr=00000r imms=11110s
      ;; size 4:  N=0 immr=0000rr imms=1110ss
      ;; size 8:  N=0 immr=000rrr imms=110sss
      ;; size 16: N=0 immr=00rrrr imms=10ssss
      ;; size 32: N=0 immr=0rrrrr imms=0sssss
      ;; size 64: N=1 immr=rrrrrr imms=ssssss
      (let* ((immr (logand (- rotation) (1- size)))
             (imms (logior (- (ash size 1))
                           (1- ones)))
             (n (ash size (- 6))))
        (logior (ash n 12) (ash immr 6) (ldb (byte 6 0) imms))))))

(defun encode-logical-immediate (n)
  "Return a 13 bit encoding of n, or NIL if it can't be encoded."
  (let* ((u64 (ldb (byte 64 0) n))
         (u64-inverted (ldb (byte 64 0) (lognot u64))))
    (if (or (/= n u64)                  ;n too big
            (zerop u64)                 ;can't encode all zeros...
            (zerop u64-inverted))       ;...or all ones
      nil
      (%encode-logical-immediate u64))))

;;; Form of an encoded logical immediate:
;;;
;;;      1
;;;  2 1 0 9 8 7 6 5 4 3 2 1 0
;;; +-+-+-+-+-+-+-+-+-+-+-+-+-+
;;; |N|   immr    |    imms   |
;;; +-+-+-+-+-+-+-+-+-+-+-+-+-+


(defconstant mask-lookup
  #(#xffffffffffffffff                  ;size = 64
    #x00000000ffffffff                  ;size = 32
    #x0000ffff0000ffff                  ;size = 16
    #x00ff00ff00ff00ff                  ;size = 8
    #x0f0f0f0f0f0f0f0f                  ;size = 4
    #x3333333333333333))                ;size = 2

(defun decode-logical-immediate (imm)
  (let* ((n (ldb (byte 1 12) imm))
         (immr (ldb (byte 6 6) imm))
         (imms (ldb (byte 6 0) imm))
         (pattern (logior (ash n 6) (logand (lognot imms) #x3f))))
    (if (zerop (logand pattern (1- pattern)))
      nil
      (let* ((leading-zeros (count-leading-zeros-32 pattern))
             (imms-mask (ash #x7fffffff (- leading-zeros)))
             (mask (aref mask-lookup (- leading-zeros 25)))
             (s (logand (1+ imms) imms-mask)))
        (rotate-right-64 (logxor mask (ash mask s)) immr)))))

#|
(defun all-logical-immediates ()
  "Return a list of all possible encoded logical immediates."
  ;; https://gist.github.com/dinfuehr/9e1c2f28d0f912eae5e595207cb835c2
  (flet ((encode-imms (size length)
           (logior length (ecase size
                            (2  #b111100)
                            (4  #b111000)
                            (8  #b110000)
                            (16 #b100000)
                            ((32 64) #b000000)))))
    (let ((results nil))
      (dolist (size '(2 4 8 16 32 64))
        (loop for length from 0 below (1- size) do
              (loop for rotation from 0 below size do
                    (let ((n (if (= size 64) 1 0))
                          (immr rotation)
                          (imms (encode-imms size length)))
                      (push (logior (ash n 12)
                                    (ash immr 6)
                                    (ldb (byte 6 0) imms))
                            results)))))
      (nreverse results))))

(defun test-logical-immediate-encode-decode (&optional show-values)
  (let ((values (all-logical-immediates)))
    (assert (= (length values) 5334))
    (dolist (val values t)
      (let ((decoded (decode-logical-immediate val)))
        (assert (not (null decoded)))
        (assert (= val (encode-logical-immediate decoded)))
        (when show-values
          (let ((n (ldb (byte 1 12) val))
                (immr (ldb (byte 6 6) val))
                (imms (ldb (byte 6 0) val)))
            (format t "~&~(~16,'0x~) ~64,'0b N=~b immr=~6,'0b imms=~6,'0b" decoded decoded
                    n immr imms)))))))
|#

(defparameter *arm64-operand-qualifiers*
  '(
    nil
    :w	
    :x
    :wsp	
    :sp	
    :s_b
    :s_h
    :s_s
    :s_d
    :s_q
    :v_8b
    :v_16b
    :v_4h
    :v_8h
    :v_2s
    :v_4s
    :v_1d
    :v_2d
    :v_1q
    :imm_0_7
    :imm_0_15
    :imm_0_31
    :imm_0_63
    :imm_1_32
    :imm_1_64
    :lsl
    :msl
    :w-ext                              ;word reg, maybe extended
    :x-ext                              ;x reg, maybe extended
    :w-shift                            ;word reg, maybe shifted
    :x-shift                            ;x reg, maybe shifted
    :aimm                               ;12-bit constant, maybe shifted left 12 bits
    :retrieve
    ))

(defun %encode-arm64-operand-qualifier (q)
  (or (position q *arm64-operand-qualifiers*)
      (error "Unknown arm64 operand qualifier: ~s" q)))

(defmacro encode-arm64-operand-qualifier (q)
  (%encode-arm64-operand-qualifier q))

(defmacro encode-arm64-operand-qualifiers (list)
  (mapcar #'%encode-arm64-operand-qualifier list))

(defparameter *arm64-condition-names*
  '(("eq" . 0)                          ;equal
    ("ne" . 1)                          ;not equal
    ("cs" . 2) ("hs" . 2)               ;carry set, unsigned higher or same
    ("cc" . 3) ("lo" . 3)               ;carry clear, unsigned lower
    ("mi" . 4)                          ;minus, negative
    ("pl" . 5)                          ;plus, positive or zero
    ("vs" . 6)                          ;overflow
    ("vc" . 7)                          ;no overflow
    ("hi" . 8)                          ;unsigned higher
    ("ls" . 9)                          ;unsigned lower or same
    ("ge" . 10)                         ;signed >=
    ("lt" . 11)                         ;signed <
    ("gt" . 12)                         ;signed >
    ("le" . 13)                         ;signed <=
    ("al" . 14)                         ;always
    ("nv" . 15)))                       ;identical to always

(defun lookup-arm64-condition-name (name)
  (cdr (assoc name *arm64-condition-names* :test #'string-equal)))

(defun lookup-arm64-condition-value (val)
  (car (rassoc val *arm64-condition-names* :test #'eq)))

(defun need-arm64-condition-name (name)
  (or (lookup-arm64-condition-name name)
      (error "Unknown ARM64 condition name ~s." name)))


(defstruct arm64-opcode
  name
  value
  mask
  class
  ??
  features
  operands
  qualifiers
  flags)



'(
  ("adc" #x1a000000 #xffe0fc00 :addsub-carry 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) 0)
  ("adc" #x9a000000 #xffe0fc00 :addsub-carry 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) 0) 
  ("adcs" #x3a000000 #xffe0fc00 :addsub-carry 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w)0)
  ("adcs" #xba000000 #xffe0fc00 :addsub-carry 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x)0) 
  ("sbc" #x5a000000 #xffe0fc00 :addsub-carry 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-HAS-ALIAS)
  ("sbc" #xda000000 #xffe0fc00 :addsub-carry 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-HAS-ALIAS)
  ("ngc" #x5a0003e0 #xffe0ffe0 :addsub-carry 0 :CORE '(:Rd :Rm) '(:w :w) F-ALIAS) 
  ("ngc" #xda0003e0 #xffe0ffe0 :addsub-carry 0 :CORE '(:Rd :Rm) '(:x :x) F-ALIAS)
  ("sbcs" #x7a000000 #xffe0fc00 :addsub-carry 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-HAS-ALIAS)
  ("sbcs" #xfa000000 #xffe0fc00 :addsub-carry 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-HAS-ALIAS)
 
  ("ngcs" #x7a0003e0 #xffe0ffe0 :addsub-carry 0 :CORE '(:Rd :Rm) '(:w :w) F-ALIAS)
  ("ngcs" #xfa0003e0 #xffe0ffe0 :addsub-carry 0 :CORE '(:Rd :Rm) '(:x :x) F-ALIAS) 
  ("add" #x0b200000 #x7fe00000 :addsub-ext 0 :CORE '(:Rd-SP :Rn-SP :Rm-EXT) QL-I3-EXT F-SF) 
  ("adds" #x2b200000 #x7fe00000 :addsub-ext 0 :CORE '(:Rd :Rn-SP :Rm-EXT) QL-I3-EXT (F-HAS-ALIAS  F-SF)) 
  ("cmn" #x2b20001f #x7fe0001f :addsub-ext 0 :CORE '(:Rn-SP :Rm-EXT) QL-I2-EXT (F-ALIAS  F-SF)) 
  ("sub" #x4b200000 #x7fe00000 :addsub-ext 0 :CORE '(:Rd-SP :Rn-SP :Rm-EXT) QL-I3-EXT F-SF) 
  ("subs" #x6b200000 #x7fe00000 :addsub-ext 0 :CORE '(:Rd :Rn-SP :Rm-EXT) QL-I3-EXT (F-HAS-ALIAS  F-SF)) 
  ("cmp" #x6b20001f #x7fe0001f :addsub-ext 0 :CORE '(:Rn-SP :Rm-EXT) QL-I2-EXT (F-ALIAS  F-SF)) 
  ("add" #x11000000 #xff000000 :addsub-imm OP-ADD :CORE '(:Rd-SP :Rn-SP :AIMM) '(:w :w :aimm) F-HAS-ALIAS) 
  ("add" #x91000000 #xff000000 :addsub-imm OP-ADD :CORE '(:Rd-SP :Rn-SP :AIMM) '(:x :x :aimm) F-HAS-ALIAS)
  ("mov" #x11000000 #x7ffffc00 :addsub-imm 0 :CORE '(:Rd-SP :Rn-SP) QL-I2SP (F-ALIAS  F-SF)) 
  ("adds" #x31000000 #xff000000 :addsub-imm 0 :CORE '(:Rd :Rn-SP :AIMM) '(:w :w :aimm) F-HAS-ALIAS) 
  ("adds" #xb1000000 #xff000000 :addsub-imm 0 :CORE '(:Rd :Rn-SP :AIMM) '(:x :x :aimm) F-HAS-ALIAS)
  ("cmn" #x3100001f #x7f00001f :addsub-imm 0 :CORE '(:Rn-SP :AIMM) QL-R1NIL (F-ALIAS  F-SF)) 
  ("sub" #x51000000 #xff000000 :addsub-imm 0 :CORE '(:Rd-SP :Rn-SP :AIMM) '(:w :w :aimm) 0)
  ("sub" #xd1000000 #xff000000 :addsub-imm 0 :CORE '(:Rd-SP :Rn-SP :AIMM) '(:x :x :aimm) 0)  
  ("subs" #x71000000 #xff000000 :addsub-imm 0 :CORE '(:Rd :Rn-SP :AIMM) '(:w :w :aimm) F-HAS-ALIAS)
  ("subs" #xf1000000 #xff000000 :addsub-imm 0 :CORE '(:Rd :Rn-SP :AIMM) '(:x :x :aimm) -HAS-ALIAS)  
  ("cmp" #x7100001f #x7f00001f :addsub-imm 0 :CORE '(:Rn-SP :AIMM) QL-R1NIL (F-ALIAS  F-SF)) 
  ("add" #xb000000 #xff200000 :addsub-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) 0)
  ("add" #x8b000000 #xff200000 :addsub-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) 0) 
  ("adds" #x2b000000 #xff200000 :addsub-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) F-HAS-ALIAS) 
  ("adds" #xab000000 #xff200000 :addsub-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) F-HAS-ALIAS)
  ("cmn" #x2b00001f #x7f20001f :addsub-shift 0 :CORE '(:Rn :Rm-SFT) QL-I2SAME (F-ALIAS  F-SF)) 
  ("sub" #x4b000000 #xff200000 :addsub-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) F-HAS-ALIAS)
  ("sub" #xcb000000 #xff200000 :addsub-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) F-HAS-ALIAS)

  ("neg" #x4b0003e0 #x7f2003e0 :addsub-shift 0 :CORE '(:Rd :Rm-SFT) QL-I2SAME (F-ALIAS  F-SF)) 
  ("subs" #x6b000000 #xff200000 :addsub-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) F-HAS-ALIAS)
  ("subs" #xeb000000 #xff200000 :addsub-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift F-HAS-ALIAS)
   ("cmp" #x6b00001f #x7f20001f :addsub-shift 0 :CORE '(:Rn :Rm-SFT) QL-I2SAME (F-ALIAS  F-SF)) 
   ("negs" #x6b0003e0 #x7f2003e0 :addsub-shift 0 :CORE '(:Rd :Rm-SFT) QL-I2SAME (F-ALIAS  F-SF)) 
   ("saddlv" #xe303800 #xbf3ffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES-L F-SIZEQ) 
   ("smaxv" #xe30a800 #xbf3ffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES F-SIZEQ) 
   ("sminv" #xe31a800 #xbf3ffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES F-SIZEQ) 
   ("addv" #xe31b800 #xbf3ffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES F-SIZEQ) 
   ("uaddlv" #x2e303800 #xbf3ffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES-L F-SIZEQ) 
   ("umaxv" #x2e30a800 #xbf3ffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES F-SIZEQ) 
   ("uminv" #x2e31a800 #xbf3ffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES F-SIZEQ) 
   ("fmaxnmv" #x2e30c800 #xbfbffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES-FP F-SIZEQ) 
   ("fmaxv" #x2e30f800 #xbfbffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES-FP F-SIZEQ) 
   ("fminnmv" #x2eb0c800 #xbfbffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES-FP F-SIZEQ) 
   ("fminv" #x2eb0f800 #xbfbffc00 :asimdall 0 SIMD '(:Fd :Vn) QL-XLANES-FP F-SIZEQ) 
   ("saddl" #x0e200000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("saddl2" #x4e200000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("saddw" #x0e201000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3WIDEBHS F-SIZEQ) 
   ("saddw2" #x4e201000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3WIDEBHS2 F-SIZEQ) 
   ("ssubl" #x0e202000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("ssubl2" #x4e202000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("ssubw" #x0e203000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3WIDEBHS F-SIZEQ) 
   ("ssubw2" #x4e203000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3WIDEBHS2 F-SIZEQ) 
   ("addhn" #x0e204000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3NARRBHS F-SIZEQ) 
   ("addhn2" #x4e204000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3NARRBHS2 F-SIZEQ) 
   ("sabal" #x0e205000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("sabal2" #x4e205000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("subhn" #x0e206000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3NARRBHS F-SIZEQ) 
   ("subhn2" #x4e206000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3NARRBHS2 F-SIZEQ) 
   ("sabdl" #x0e207000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("sabdl2" #x4e207000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("smlal" #x0e208000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("smlal2" #x4e208000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("sqdmlal" #x0e209000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGHS F-SIZEQ) 
   ("sqdmlal2" #x4e209000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGHS2 F-SIZEQ) 
   ("smlsl" #x0e20a000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("smlsl2" #x4e20a000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("sqdmlsl" #x0e20b000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGHS F-SIZEQ) 
   ("sqdmlsl2" #x4e20b000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGHS2 F-SIZEQ) 
   ("smull" #x0e20c000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("smull2" #x4e20c000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("sqdmull" #x0e20d000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGHS F-SIZEQ) 
   ("sqdmull2" #x4e20d000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGHS2 F-SIZEQ) 
   ("pmull" #x0e20e000 #xffe0fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGB 0) 
   ("pmull" #x0ee0e000 #xffe0fc00 :asimddiff 0 :CRYPTO '(:Vd :Vn :Vm) QL-V3LONGD 0) 
   ("pmull2" #x4e20e000 #xffe0fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGB2 0) 
   ("pmull2" #x4ee0e000 #xffe0fc00 :asimddiff 0 :CRYPTO '(:Vd :Vn :Vm) QL-V3LONGD2 0) 
   ("uaddl" #x2e200000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("uaddl2" #x6e200000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("uaddw" #x2e201000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3WIDEBHS F-SIZEQ) 
   ("uaddw2" #x6e201000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3WIDEBHS2 F-SIZEQ) 
   ("usubl" #x2e202000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("usubl2" #x6e202000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("usubw" #x2e203000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3WIDEBHS F-SIZEQ) 
   ("usubw2" #x6e203000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3WIDEBHS2 F-SIZEQ) 
   ("raddhn" #x2e204000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3NARRBHS F-SIZEQ) 
   ("raddhn2" #x6e204000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3NARRBHS2 F-SIZEQ) 
   ("uabal" #x2e205000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("uabal2" #x6e205000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("rsubhn" #x2e206000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3NARRBHS F-SIZEQ) 
   ("rsubhn2" #x6e206000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3NARRBHS2 F-SIZEQ) 
   ("uabdl" #x2e207000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("uabdl2" #x6e207000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("umlal" #x2e208000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("umlal2" #x6e208000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("umlsl" #x2e20a000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("umlsl2" #x6e20a000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("umull" #x2e20c000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS F-SIZEQ) 
   ("umull2" #x6e20c000 #xff20fc00 :asimddiff 0 SIMD '(:Vd :Vn :Vm) QL-V3LONGBHS2 F-SIZEQ) 
   ("smlal" #x0f002000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L F-SIZEQ) 
   ("smlal2" #x4f002000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L2 F-SIZEQ) 
   ("sqdmlal" #x0f003000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L F-SIZEQ) 
   ("sqdmlal2" #x4f003000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L2 F-SIZEQ) 
   ("smlsl" #x0f006000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L F-SIZEQ) 
   ("smlsl2" #x4f006000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L2 F-SIZEQ) 
   ("sqdmlsl" #x0f007000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L F-SIZEQ) 
   ("sqdmlsl2" #x4f007000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L2 F-SIZEQ) 
   ("mul" #xf008000 #xbf00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT F-SIZEQ) 
   ("smull" #x0f00a000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L F-SIZEQ) 
   ("smull2" #x4f00a000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L2 F-SIZEQ) 
   ("sqdmull" #x0f00b000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L F-SIZEQ) 
   ("sqdmull2" #x4f00b000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L2 F-SIZEQ) 
   ("sqdmulh" #xf00c000 #xbf00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT F-SIZEQ) 
   ("sqrdmulh" #xf00d000 #xbf00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT F-SIZEQ) 
   ("fmla" #xf801000 #xbf80f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-FP F-SIZEQ) 
   ("fmls" #xf805000 #xbf80f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-FP F-SIZEQ) 
   ("fmul" #xf809000 #xbf80f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-FP F-SIZEQ) 
   ("mla" #x2f000000 #xbf00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT F-SIZEQ) 
   ("umlal" #x2f002000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L F-SIZEQ) 
   ("umlal2" #x6f002000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L2 F-SIZEQ) 
   ("mls" #x2f004000 #xbf00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT F-SIZEQ) 
   ("umlsl" #x2f006000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L F-SIZEQ) 
   ("umlsl2" #x6f006000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L2 F-SIZEQ) 
   ("umull" #x2f00a000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L F-SIZEQ) 
   ("umull2" #x6f00a000 #xff00f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-L2 F-SIZEQ) 
   ("fmulx" #x2f809000 #xbf80f400 :asimdelem 0 SIMD '(:Vd :Vn :Em) QL-ELEMENT-FP F-SIZEQ) 
   ("ext" #x2e000000 #xbfe0c400 :asimdext 0 SIMD '(:Vd :Vn :Vm :IDX) QL-VEXT F-SIZEQ) 
   ("movi" #xf000400 #xbff89c00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S0W F-SIZEQ) 
   ("orr" #xf001400 #xbff89c00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S0W F-SIZEQ) 
   ("movi" #xf008400 #xbff8dc00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S0H F-SIZEQ) 
   ("orr" #xf009400 #xbff8dc00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S0H F-SIZEQ) 
   ("movi" #xf00c400 #xbff8ec00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S1W F-SIZEQ) 
   ("movi" #xf00e400 #xbff8fc00 :asimdimm OP-V-MOVI-B SIMD '(:Vd :SIMD-IMM) QL-SIMD-IMM-B F-SIZEQ) 
   ("fmov" #xf00f400 #xbff8fc00 :asimdimm 0 SIMD '(:Vd :SIMD-FPIMM) QL-SIMD-IMM-S F-SIZEQ) 
   ("mvni" #x2f000400 #xbff89c00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S0W F-SIZEQ) 
   ("bic" #x2f001400 #xbff89c00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S0W F-SIZEQ) 
   ("mvni" #x2f008400 #xbff8dc00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S0H F-SIZEQ) 
   ("bic" #x2f009400 #xbff8dc00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S0H F-SIZEQ) 
   ("mvni" #x2f00c400 #xbff8ec00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM-SFT) QL-SIMD-IMM-S1W F-SIZEQ) 
   ("movi" #x2f00e400 #xfff8fc00 :asimdimm 0 SIMD '(:Sd :SIMD-IMM) QL-SIMD-IMM-D F-SIZEQ) 
   ("movi" #x6f00e400 #xfff8fc00 :asimdimm 0 SIMD '(:Vd :SIMD-IMM) QL-SIMD-IMM-V2D F-SIZEQ) 
   ("fmov" #x6f00f400 #xfff8fc00 :asimdimm 0 SIMD '(:Vd :SIMD-FPIMM) QL-SIMD-IMM-V2D F-SIZEQ) 
   ("dup" #xe000400 #xbfe0fc00 :asimdins 0 SIMD '(:Vd :En) QL-DUP-VX F-T) 
   ("dup" #xe000c00 #xbfe0fc00 :asimdins 0 SIMD '(:Vd :Rn) QL-DUP-VR F-T) 
   ("smov" #xe002c00 #xbfe0fc00 :asimdins 0 SIMD '(:Rd :En) QL-SMOV F-GPRSIZE-IN-Q) 
   ("umov" #xe003c00 #xbfe0fc00 :asimdins 0 SIMD '(:Rd :En) QL-UMOV (F-HAS-ALIAS  F-GPRSIZE-IN-Q)) 
   ("mov" #xe003c00 #xbfe0fc00 :asimdins 0 SIMD '(:Rd :En) QL-MOV (F-ALIAS  F-GPRSIZE-IN-Q)) 
   ("ins" #x4e001c00 #xffe0fc00 :asimdins 0 SIMD '(:Ed :Rn) QL-INS-XR F-HAS-ALIAS) 
   ("mov" #x4e001c00 #xffe0fc00 :asimdins 0 SIMD '(:Ed :Rn) QL-INS-XR F-ALIAS) 
   ("ins" #x6e000400 #xffe08400 :asimdins 0 SIMD '(:Ed :En) QL-S-2SAME F-HAS-ALIAS) 
   ("mov" #x6e000400 #xffe08400 :asimdins 0 SIMD '(:Ed :En) QL-S-2SAME F-ALIAS) 
   ("rev64" #xe200800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMEBHS F-SIZEQ) 
   ("rev16" #xe201800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMEB F-SIZEQ) 
   ("saddlp" #xe202800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2PAIRWISELONGBHS F-SIZEQ) 
   ("suqadd" #xe203800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAME F-SIZEQ) 
   ("cls" #xe204800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMEBHS F-SIZEQ) 
   ("cnt" #xe205800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMEB F-SIZEQ) 
   ("sadalp" #xe206800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2PAIRWISELONGBHS F-SIZEQ) 
   ("sqabs" #xe207800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAME F-SIZEQ) 
   ("cmgt" #xe208800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAME F-SIZEQ) 
   ("cmeq" #xe209800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAME F-SIZEQ) 
   ("cmlt" #xe20a800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAME F-SIZEQ) 
   ("abs" #xe20b800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAME F-SIZEQ) 
   ("xtn" #xe212800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRBHS F-SIZEQ) 
   ("xtn2" #x4e212800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRBHS2 F-SIZEQ) 
   ("sqxtn" #xe214800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRBHS F-SIZEQ) 
   ("sqxtn2" #x4e214800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRBHS2 F-SIZEQ) 
   ("fcvtn" #xe216800 #xffbffc00 :asimdmisc OP-FCVTN SIMD '(:Vd :Vn) QL-V2NARRHS F-MISC) 
   ("fcvtn2" #x4e216800 #xffbffc00 :asimdmisc OP-FCVTN2 SIMD '(:Vd :Vn) QL-V2NARRHS2 F-MISC) 
   ("fcvtl" #xe217800 #xffbffc00 :asimdmisc OP-FCVTL SIMD '(:Vd :Vn) QL-V2LONGHS F-MISC) 
   ("fcvtl2" #x4e217800 #xffbffc00 :asimdmisc OP-FCVTL2 SIMD '(:Vd :Vn) QL-V2LONGHS2 F-MISC) 
   ("frintn" #xe218800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("frintm" #xe219800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtns" #xe21a800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtms" #xe21b800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtas" #xe21c800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("scvtf" #xe21d800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcmgt" #xea0c800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAMESD F-SIZEQ) 
   ("fcmeq" #xea0d800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAMESD F-SIZEQ) 
   ("fcmlt" #xea0e800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAMESD F-SIZEQ) 
   ("fabs" #xea0f800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("frintp" #xea18800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("frintz" #xea19800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtps" #xea1a800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtzs" #xea1b800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("urecpe" #xea1c800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMES F-SIZEQ) 
   ("frecpe" #xea1d800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("rev32" #x2e200800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMEBH F-SIZEQ) 
   ("uaddlp" #x2e202800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2PAIRWISELONGBHS F-SIZEQ) 
   ("usqadd" #x2e203800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAME F-SIZEQ) 
   ("clz" #x2e204800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMEBHS F-SIZEQ) 
   ("uadalp" #x2e206800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2PAIRWISELONGBHS F-SIZEQ) 
   ("sqneg" #x2e207800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAME F-SIZEQ) 
   ("cmge" #x2e208800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAME F-SIZEQ) 
   ("cmle" #x2e209800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAME F-SIZEQ) 
   ("neg" #x2e20b800 #xbf3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAME F-SIZEQ) 
   ("sqxtun" #x2e212800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRBHS F-SIZEQ) 
   ("sqxtun2" #x6e212800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRBHS2 F-SIZEQ) 
   ("shll" #x2e213800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn :SHLL-IMM) QL-V2LONGBHS F-SIZEQ) 
   ("shll2" #x6e213800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn :SHLL-IMM) QL-V2LONGBHS2 F-SIZEQ) 
   ("uqxtn" #x2e214800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRBHS F-SIZEQ) 
   ("uqxtn2" #x6e214800 #xff3ffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRBHS2 F-SIZEQ) 
   ("fcvtxn" #x2e616800 #xfffffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRS 0) 
   ("fcvtxn2" #x6e616800 #xfffffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2NARRS2 0) 
   ("frinta" #x2e218800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("frintx" #x2e219800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtnu" #x2e21a800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtmu" #x2e21b800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtau" #x2e21c800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("ucvtf" #x2e21d800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("not" #x2e205800 #xbffffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMEB (F-SIZEQ  F-HAS-ALIAS)) 
   ("mvn" #x2e205800 #xbffffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMEB (F-SIZEQ  F-ALIAS)) 
   ("rbit" #x2e605800 #xbffffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMEB F-SIZEQ) 
   ("fcmge" #x2ea0c800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAMESD F-SIZEQ) 
   ("fcmle" #x2ea0d800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn :IMM0) QL-V2SAMESD F-SIZEQ) 
   ("fneg" #x2ea0f800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("frinti" #x2ea19800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtpu" #x2ea1a800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fcvtzu" #x2ea1b800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("ursqrte" #x2ea1c800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMES F-SIZEQ) 
   ("frsqrte" #x2ea1d800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("fsqrt" #x2ea1f800 #xbfbffc00 :asimdmisc 0 SIMD '(:Vd :Vn) QL-V2SAMESD F-SIZEQ) 
   ("uzp1" #xe001800 #xbf20fc00 :asimdperm 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("trn1" #xe002800 #xbf20fc00 :asimdperm 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("zip1" #xe003800 #xbf20fc00 :asimdperm 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("uzp2" #xe005800 #xbf20fc00 :asimdperm 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("trn2" #xe006800 #xbf20fc00 :asimdperm 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("zip2" #xe007800 #xbf20fc00 :asimdperm 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("shadd" #xe200400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("sqadd" #xe200c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("srhadd" #xe201400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("shsub" #xe202400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("sqsub" #xe202c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("cmgt" #xe203400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("cmge" #xe203c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("sshl" #xe204400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("sqshl" #xe204c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("srshl" #xe205400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("sqrshl" #xe205c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("smax" #xe206400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("smin" #xe206c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("sabd" #xe207400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("saba" #xe207c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("add" #xe208400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("cmtst" #xe208c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("mla" #xe209400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("mul" #xe209c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("smaxp" #xe20a400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("sminp" #xe20ac00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("sqdmulh" #xe20b400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEHS F-SIZEQ) 
   ("addp" #xe20bc00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("fmaxnm" #xe20c400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fmla" #xe20cc00 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fadd" #xe20d400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fmulx" #xe20dc00 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fcmeq" #xe20e400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fmax" #xe20f400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("frecps" #xe20fc00 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("and" #xe201c00 #xbfe0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEB F-SIZEQ) 
   ("bic" #xe601c00 #xbfe0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEB F-SIZEQ) 
   ("fminnm" #xea0c400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fmls" #xea0cc00 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fsub" #xea0d400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fmin" #xea0f400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("frsqrts" #xea0fc00 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("orr" #xea01c00 #xbfe0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEB (F-HAS-ALIAS  F-SIZEQ)) 
   ("mov" #xea01c00 #xbfe0fc00 :asimdsame OP-MOV-V SIMD '(:Vd :Vn) QL-V2SAMEB (F-ALIAS  F-CONV)) 
   ("orn" #xee01c00 #xbfe0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEB F-SIZEQ) 
   ("uhadd" #x2e200400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("uqadd" #x2e200c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("urhadd" #x2e201400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("uhsub" #x2e202400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("uqsub" #x2e202c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("cmhi" #x2e203400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("cmhs" #x2e203c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("ushl" #x2e204400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("uqshl" #x2e204c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("urshl" #x2e205400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("uqrshl" #x2e205c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("umax" #x2e206400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("umin" #x2e206c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("uabd" #x2e207400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("uaba" #x2e207c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("sub" #x2e208400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("cmeq" #x2e208c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAME F-SIZEQ) 
   ("mls" #x2e209400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("pmul" #x2e209c00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEB F-SIZEQ) 
   ("umaxp" #x2e20a400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("uminp" #x2e20ac00 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEBHS F-SIZEQ) 
   ("sqrdmulh" #x2e20b400 #xbf20fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEHS F-SIZEQ) 
   ("fmaxnmp" #x2e20c400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("faddp" #x2e20d400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fmul" #x2e20dc00 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fcmge" #x2e20e400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("facge" #x2e20ec00 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fmaxp" #x2e20f400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fdiv" #x2e20fc00 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("eor" #x2e201c00 #xbfe0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEB F-SIZEQ) 
   ("bsl" #x2e601c00 #xbfe0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEB F-SIZEQ) 
   ("fminnmp" #x2ea0c400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fabd" #x2ea0d400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fcmgt" #x2ea0e400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("facgt" #x2ea0ec00 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("fminp" #x2ea0f400 #xbfa0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMESD F-SIZEQ) 
   ("bit" #x2ea01c00 #xbfe0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEB F-SIZEQ) 
   ("bif" #x2ee01c00 #xbfe0fc00 :asimdsame 0 SIMD '(:Vd :Vn :Vm) QL-V3SAMEB F-SIZEQ) 
   ("sshr" #xf000400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT 0) 
   ("ssra" #xf001400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT 0) 
   ("srshr" #xf002400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT 0) 
   ("srsra" #xf003400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT 0) 
   ("shl" #xf005400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSL) QL-VSHIFT 0) 
   ("sqshl" #xf007400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSL) QL-VSHIFT 0) 
   ("shrn" #xf008400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN 0) 
   ("shrn2" #x4f008400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN2 0) 
   ("rshrn" #xf008c00 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN 0) 
   ("rshrn2" #x4f008c00 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN2 0) 
   ("sqshrn" #xf009400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN 0) 
   ("sqshrn2" #x4f009400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN2 0) 
   ("sqrshrn" #xf009c00 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN 0) 
   ("sqrshrn2" #x4f009c00 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN2 0) 
   ("sshll" #xf00a400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSL) QL-VSHIFTL F-HAS-ALIAS) 
   ("sxtl" #xf00a400 #xff87fc00 :asimdshf OP-SXTL SIMD '(:Vd :Vn) QL-V2LONGBHS (F-ALIAS  F-CONV)) 
   ("sshll2" #x4f00a400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSL) QL-VSHIFTL2 F-HAS-ALIAS) 
   ("sxtl2" #x4f00a400 #xff87fc00 :asimdshf OP-SXTL2 SIMD '(:Vd :Vn) QL-V2LONGBHS2 (F-ALIAS  F-CONV)) 
   ("scvtf" #xf00e400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT-SD 0) 
   ("fcvtzs" #xf00fc00 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT-SD 0) 
   ("ushr" #x2f000400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT 0) 
   ("usra" #x2f001400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT 0) 
   ("urshr" #x2f002400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT 0) 
   ("ursra" #x2f003400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT 0) 
   ("sri" #x2f004400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT 0) 
   ("sli" #x2f005400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSL) QL-VSHIFT 0) 
   ("sqshlu" #x2f006400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSL) QL-VSHIFT 0) 
   ("uqshl" #x2f007400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSL) QL-VSHIFT 0) 
   ("sqshrun" #x2f008400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN 0) 
   ("sqshrun2" #x6f008400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN2 0) 
   ("sqrshrun" #x2f008c00 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN 0) 
   ("sqrshrun2" #x6f008c00 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN2 0) 
   ("uqshrn" #x2f009400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN 0) 
   ("uqshrn2" #x6f009400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN2 0) 
   ("uqrshrn" #x2f009c00 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN 0) 
   ("uqrshrn2" #x6f009c00 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFTN2 0) 
   ("ushll" #x2f00a400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSL) QL-VSHIFTL F-HAS-ALIAS) 
   ("uxtl" #x2f00a400 #xff87fc00 :asimdshf OP-UXTL SIMD '(:Vd :Vn) QL-V2LONGBHS (F-ALIAS  F-CONV)) 
   ("ushll2" #x6f00a400 #xff80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSL) QL-VSHIFTL2 F-HAS-ALIAS) 
   ("uxtl2" #x6f00a400 #xff87fc00 :asimdshf OP-UXTL2 SIMD '(:Vd :Vn) QL-V2LONGBHS2 (F-ALIAS  F-CONV)) 
   ("ucvtf" #x2f00e400 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT-SD 0) 
   ("fcvtzu" #x2f00fc00 #xbf80fc00 :asimdshf 0 SIMD '(:Vd :Vn :IMM-VLSR) QL-VSHIFT-SD 0) 
   ("tbl" #xe000000 #xbfe09c00 :asimdtbl 0 SIMD '(:Vd :LVn :Vm) QL-TABLE F-SIZEQ) 
   ("tbx" #xe001000 #xbfe09c00 :asimdtbl 0 SIMD '(:Vd :LVn :Vm) QL-TABLE F-SIZEQ) 
   ("sqdmlal" #x5e209000 #xff20fc00 :asisddiff 0 SIMD '(:Sd :Sn :Sm) QL-SISDL-HS F-SSIZE) 
   ("sqdmlsl" #x5e20b000 #xff20fc00 :asisddiff 0 SIMD '(:Sd :Sn :Sm) QL-SISDL-HS F-SSIZE) 
   ("sqdmull" #x5e20d000 #xff20fc00 :asisddiff 0 SIMD '(:Sd :Sn :Sm) QL-SISDL-HS F-SSIZE) 
   ("sqdmlal" #x5f003000 #xff00f400 :asisdelem 0 SIMD '(:Sd :Sn :Em) QL-SISDL-HS F-SSIZE) 
   ("sqdmlsl" #x5f007000 #xff00f400 :asisdelem 0 SIMD '(:Sd :Sn :Em) QL-SISDL-HS F-SSIZE) 
   ("sqdmull" #x5f00b000 #xff00f400 :asisdelem 0 SIMD '(:Sd :Sn :Em) QL-SISDL-HS F-SSIZE) 
   ("sqdmulh" #x5f00c000 #xff00f400 :asisdelem 0 SIMD '(:Sd :Sn :Em) QL-SISD-HS F-SSIZE) 
   ("sqrdmulh" #x5f00d000 #xff00f400 :asisdelem 0 SIMD '(:Sd :Sn :Em) QL-SISD-HS F-SSIZE) 
   ("fmla" #x5f801000 #xff80f400 :asisdelem 0 SIMD '(:Sd :Sn :Em) QL-FP3 F-SSIZE) 
   ("fmls" #x5f805000 #xff80f400 :asisdelem 0 SIMD '(:Sd :Sn :Em) QL-FP3 F-SSIZE) 
   ("fmul" #x5f809000 #xff80f400 :asisdelem 0 SIMD '(:Sd :Sn :Em) QL-FP3 F-SSIZE) 
   ("fmulx" #x7f809000 #xff80f400 :asisdelem 0 SIMD '(:Sd :Sn :Em) QL-FP3 F-SSIZE) 
   ("st4" #xc000000 #xbfff0000 :asisdlse 0 SIMD '(:LVt :SIMD-ADDR-SIMPLE) QL-SIMD-LDST (F-SIZEQ  F-OD)(4)) 
   ("st1" #xc000000 #xbfff0000 :asisdlse 0 SIMD '(:LVt :SIMD-ADDR-SIMPLE) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(1)) 
   ("st2" #xc000000 #xbfff0000 :asisdlse 0 SIMD '(:LVt :SIMD-ADDR-SIMPLE) QL-SIMD-LDST (F-SIZEQ  F-OD)(2)) 
   ("st3" #xc000000 #xbfff0000 :asisdlse 0 SIMD '(:LVt :SIMD-ADDR-SIMPLE) QL-SIMD-LDST (F-SIZEQ  F-OD)(3)) 
   ("ld4" #xc400000 #xbfff0000 :asisdlse 0 SIMD '(:LVt :SIMD-ADDR-SIMPLE) QL-SIMD-LDST (F-SIZEQ  F-OD)(4)) 
   ("ld1" #xc400000 #xbfff0000 :asisdlse 0 SIMD '(:LVt :SIMD-ADDR-SIMPLE) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(1)) 
   ("ld2" #xc400000 #xbfff0000 :asisdlse 0 SIMD '(:LVt :SIMD-ADDR-SIMPLE) QL-SIMD-LDST (F-SIZEQ  F-OD)(2)) 
   ("ld3" #xc400000 #xbfff0000 :asisdlse 0 SIMD '(:LVt :SIMD-ADDR-SIMPLE) QL-SIMD-LDST (F-SIZEQ  F-OD)(3)) 
   ("st4" #xc800000 #xbfe00000 :asisdlsep 0 SIMD '(:LVt :SIMD-ADDR-POST) QL-SIMD-LDST (F-SIZEQ  F-OD)(4)) 
   ("st1" #xc800000 #xbfe00000 :asisdlsep 0 SIMD '(:LVt :SIMD-ADDR-POST) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(1)) 
   ("st2" #xc800000 #xbfe00000 :asisdlsep 0 SIMD '(:LVt :SIMD-ADDR-POST) QL-SIMD-LDST (F-SIZEQ  F-OD)(2)) 
   ("st3" #xc800000 #xbfe00000 :asisdlsep 0 SIMD '(:LVt :SIMD-ADDR-POST) QL-SIMD-LDST (F-SIZEQ  F-OD)(3)) 
   ("ld4" #xcc00000 #xbfe00000 :asisdlsep 0 SIMD '(:LVt :SIMD-ADDR-POST) QL-SIMD-LDST (F-SIZEQ  F-OD)(4)) 
   ("ld1" #xcc00000 #xbfe00000 :asisdlsep 0 SIMD '(:LVt :SIMD-ADDR-POST) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(1)) 
   ("ld2" #xcc00000 #xbfe00000 :asisdlsep 0 SIMD '(:LVt :SIMD-ADDR-POST) QL-SIMD-LDST (F-SIZEQ  F-OD)(2)) 
   ("ld3" #xcc00000 #xbfe00000 :asisdlsep 0 SIMD '(:LVt :SIMD-ADDR-POST) QL-SIMD-LDST (F-SIZEQ  F-OD)(3)) 
   ("st1" #xd000000 #xbfff2000 :asisdlso 0 SIMD '(:LEt :SIMD-ADDR-SIMPLE) QL-SIMD-LDSTONE F-OD(1)) 
   ("st3" #xd002000 #xbfff2000 :asisdlso 0 SIMD '(:LEt :SIMD-ADDR-SIMPLE) QL-SIMD-LDSTONE F-OD(3)) 
   ("st2" #xd200000 #xbfff2000 :asisdlso 0 SIMD '(:LEt :SIMD-ADDR-SIMPLE) QL-SIMD-LDSTONE F-OD(2)) 
   ("st4" #xd202000 #xbfff2000 :asisdlso 0 SIMD '(:LEt :SIMD-ADDR-SIMPLE) QL-SIMD-LDSTONE F-OD(4)) 
   ("ld1" #xd400000 #xbfff2000 :asisdlso 0 SIMD '(:LEt :SIMD-ADDR-SIMPLE) QL-SIMD-LDSTONE F-OD(1)) 
   ("ld3" #xd402000 #xbfff2000 :asisdlso 0 SIMD '(:LEt :SIMD-ADDR-SIMPLE) QL-SIMD-LDSTONE F-OD(3)) 
   ("ld1r" #xd40c000 #xbfffe000 :asisdlso 0 SIMD '(:LVt-AL :SIMD-ADDR-SIMPLE) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(1)) 
   ("ld3r" #xd40e000 #xbfffe000 :asisdlso 0 SIMD '(:LVt-AL :SIMD-ADDR-SIMPLE) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(3)) 
   ("ld2" #xd600000 #xbfff2000 :asisdlso 0 SIMD '(:LEt :SIMD-ADDR-SIMPLE) QL-SIMD-LDSTONE F-OD(2)) 
   ("ld4" #xd602000 #xbfff2000 :asisdlso 0 SIMD '(:LEt :SIMD-ADDR-SIMPLE) QL-SIMD-LDSTONE F-OD(4)) 
   ("ld2r" #xd60c000 #xbfffe000 :asisdlso 0 SIMD '(:LVt-AL :SIMD-ADDR-SIMPLE) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(2)) 
   ("ld4r" #xd60e000 #xbfffe000 :asisdlso 0 SIMD '(:LVt-AL :SIMD-ADDR-SIMPLE) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(4)) 
   ("st1" #xd800000 #xbfe02000 :asisdlsop 0 SIMD '(:LEt :SIMD-ADDR-POST) QL-SIMD-LDSTONE F-OD(1)) 
   ("st3" #xd802000 #xbfe02000 :asisdlsop 0 SIMD '(:LEt :SIMD-ADDR-POST) QL-SIMD-LDSTONE F-OD(3)) 
   ("st2" #xda00000 #xbfe02000 :asisdlsop 0 SIMD '(:LEt :SIMD-ADDR-POST) QL-SIMD-LDSTONE F-OD(2)) 
   ("st4" #xda02000 #xbfe02000 :asisdlsop 0 SIMD '(:LEt :SIMD-ADDR-POST) QL-SIMD-LDSTONE F-OD(4)) 
   ("ld1" #xdc00000 #xbfe02000 :asisdlsop 0 SIMD '(:LEt :SIMD-ADDR-POST) QL-SIMD-LDSTONE F-OD(1)) 
   ("ld3" #xdc02000 #xbfe02000 :asisdlsop 0 SIMD '(:LEt :SIMD-ADDR-POST) QL-SIMD-LDSTONE F-OD(3)) 
   ("ld1r" #xdc0c000 #xbfe0e000 :asisdlsop 0 SIMD '(:LVt-AL :SIMD-ADDR-POST) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(1)) 
   ("ld3r" #xdc0e000 #xbfe0e000 :asisdlsop 0 SIMD '(:LVt-AL :SIMD-ADDR-POST) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(3)) 
   ("ld2" #xde00000 #xbfe02000 :asisdlsop 0 SIMD '(:LEt :SIMD-ADDR-POST) QL-SIMD-LDSTONE F-OD(2)) 
   ("ld4" #xde02000 #xbfe02000 :asisdlsop 0 SIMD '(:LEt :SIMD-ADDR-POST) QL-SIMD-LDSTONE F-OD(4)) 
   ("ld2r" #xde0c000 #xbfe0e000 :asisdlsop 0 SIMD '(:LVt-AL :SIMD-ADDR-POST) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(2)) 
   ("ld4r" #xde0e000 #xbfe0e000 :asisdlsop 0 SIMD '(:LVt-AL :SIMD-ADDR-POST) QL-SIMD-LDST-ANY (F-SIZEQ  F-OD)(4)) 
   ("suqadd" #x5e203800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAME F-SSIZE) 
   ("sqabs" #x5e207800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAME F-SSIZE) 
   ("cmgt" #x5e208800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-CMP-0 F-SSIZE) 
   ("cmeq" #x5e209800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-CMP-0 F-SSIZE) 
   ("cmlt" #x5e20a800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-CMP-0 F-SSIZE) 
   ("abs" #x5e20b800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-2SAMED F-SSIZE) 
   ("sqxtn" #x5e214800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-SISD-NARROW F-SSIZE) 
   ("fcvtns" #x5e21a800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("fcvtms" #x5e21b800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("fcvtas" #x5e21c800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("scvtf" #x5e21d800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("fcmgt" #x5ea0c800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-FCMP-0 F-SSIZE) 
   ("fcmeq" #x5ea0d800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-FCMP-0 F-SSIZE) 
   ("fcmlt" #x5ea0e800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-FCMP-0 F-SSIZE) 
   ("fcvtps" #x5ea1a800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("fcvtzs" #x5ea1b800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("frecpe" #x5ea1d800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("frecpx" #x5ea1f800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("usqadd" #x7e203800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAME F-SSIZE) 
   ("sqneg" #x7e207800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAME F-SSIZE) 
   ("cmge" #x7e208800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-CMP-0 F-SSIZE) 
   ("cmle" #x7e209800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-CMP-0 F-SSIZE) 
   ("neg" #x7e20b800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-2SAMED F-SSIZE) 
   ("sqxtun" #x7e212800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-SISD-NARROW F-SSIZE) 
   ("uqxtn" #x7e214800 #xff3ffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-SISD-NARROW F-SSIZE) 
   ("fcvtxn" #x7e216800 #xffbffc00 :asisdmisc OP-FCVTXN-S SIMD '(:Sd :Sn) QL-SISD-NARROW-S F-MISC) 
   ("fcvtnu" #x7e21a800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("fcvtmu" #x7e21b800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("fcvtau" #x7e21c800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("ucvtf" #x7e21d800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("fcmge" #x7ea0c800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-FCMP-0 F-SSIZE) 
   ("fcmle" #x7ea0d800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn :IMM0) QL-SISD-FCMP-0 F-SSIZE) 
   ("fcvtpu" #x7ea1a800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("fcvtzu" #x7ea1b800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("frsqrte" #x7ea1d800 #xffbffc00 :asisdmisc 0 SIMD '(:Sd :Sn) QL-S-2SAMESD F-SSIZE) 
   ("dup" #x5e000400 #xffe0fc00 :asisdone 0 SIMD '(:Sd :En) QL-S-2SAME F-HAS-ALIAS) 
   ("mov" #x5e000400 #xffe0fc00 :asisdone 0 SIMD '(:Sd :En) QL-S-2SAME F-ALIAS) 
   ("addp" #x5e31b800 #xff3ffc00 :asisdpair 0 SIMD '(:Sd :Vn) QL-SISD-PAIR-D F-SIZEQ) 
   ("fmaxnmp" #x7e30c800 #xffbffc00 :asisdpair 0 SIMD '(:Sd :Vn) QL-SISD-PAIR F-SIZEQ) 
   ("faddp" #x7e30d800 #xffbffc00 :asisdpair 0 SIMD '(:Sd :Vn) QL-SISD-PAIR F-SIZEQ) 
   ("fmaxp" #x7e30f800 #xffbffc00 :asisdpair 0 SIMD '(:Sd :Vn) QL-SISD-PAIR F-SIZEQ) 
   ("fminnmp" #x7eb0c800 #xffbffc00 :asisdpair 0 SIMD '(:Sd :Vn) QL-SISD-PAIR F-SIZEQ) 
   ("fminp" #x7eb0f800 #xffbffc00 :asisdpair 0 SIMD '(:Sd :Vn) QL-SISD-PAIR F-SIZEQ) 
   ("sqadd" #x5e200c00 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAME F-SSIZE) 
   ("sqsub" #x5e202c00 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAME F-SSIZE) 
   ("sqshl" #x5e204c00 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAME F-SSIZE) 
   ("sqrshl" #x5e205c00 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAME F-SSIZE) 
   ("sqdmulh" #x5e20b400 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-SISD-HS F-SSIZE) 
   ("fmulx" #x5e20dc00 #xffa0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-FP3 F-SSIZE) 
   ("fcmeq" #x5e20e400 #xffa0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-FP3 F-SSIZE) 
   ("frecps" #x5e20fc00 #xffa0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-FP3 F-SSIZE) 
   ("frsqrts" #x5ea0fc00 #xffa0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-FP3 F-SSIZE) 
   ("cmgt" #x5ee03400 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("cmge" #x5ee03c00 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("sshl" #x5ee04400 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("srshl" #x5ee05400 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("add" #x5ee08400 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("cmtst" #x5ee08c00 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("uqadd" #x7e200c00 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAME F-SSIZE) 
   ("uqsub" #x7e202c00 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAME F-SSIZE) 
   ("uqshl" #x7e204c00 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAME F-SSIZE) 
   ("uqrshl" #x7e205c00 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAME F-SSIZE) 
   ("sqrdmulh" #x7e20b400 #xff20fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-SISD-HS F-SSIZE) 
   ("fcmge" #x7e20e400 #xffa0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-FP3 F-SSIZE) 
   ("facge" #x7e20ec00 #xffa0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-FP3 F-SSIZE) 
   ("fabd" #x7ea0d400 #xffa0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-FP3 F-SSIZE) 
   ("fcmgt" #x7ea0e400 #xffa0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-FP3 F-SSIZE) 
   ("facgt" #x7ea0ec00 #xffa0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-FP3 F-SSIZE) 
   ("cmhi" #x7ee03400 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("cmhs" #x7ee03c00 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("ushl" #x7ee04400 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("urshl" #x7ee05400 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("sub" #x7ee08400 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("cmeq" #x7ee08c00 #xffe0fc00 :asisdsame 0 SIMD '(:Sd :Sn :Sm) QL-S-3SAMED F-SSIZE) 
   ("sshr" #x5f000400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-D 0) 
   ("ssra" #x5f001400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-D 0) 
   ("srshr" #x5f002400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-D 0) 
   ("srsra" #x5f003400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-D 0) 
   ("shl" #x5f005400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSL) QL-SSHIFT-D 0) 
   ("sqshl" #x5f007400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSL) QL-SSHIFT 0) 
   ("sqshrn" #x5f009400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFTN 0) 
   ("sqrshrn" #x5f009c00 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFTN 0) 
   ("scvtf" #x5f00e400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-SD 0) 
   ("fcvtzs" #x5f00fc00 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-SD 0) 
   ("ushr" #x7f000400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-D 0) 
   ("usra" #x7f001400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-D 0) 
   ("urshr" #x7f002400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-D 0) 
   ("ursra" #x7f003400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-D 0) 
   ("sri" #x7f004400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-D 0) 
   ("sli" #x7f005400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSL) QL-SSHIFT-D 0) 
   ("sqshlu" #x7f006400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSL) QL-SSHIFT 0) 
   ("uqshl" #x7f007400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSL) QL-SSHIFT 0) 
   ("sqshrun" #x7f008400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFTN 0) 
   ("sqrshrun" #x7f008c00 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFTN 0) 
   ("uqshrn" #x7f009400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFTN 0) 
   ("uqrshrn" #x7f009c00 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFTN 0) 
   ("ucvtf" #x7f00e400 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-SD 0) 
   ("fcvtzu" #x7f00fc00 #xff80fc00 :asisdshf 0 SIMD '(:Sd :Sn :IMM-VLSR) QL-SSHIFT-SD 0) 
   ("sbfm" #x13000000 #x7f800000 :bitfield 0 :CORE '(:Rd :Rn :IMMR :IMMS) QL-BF ((F-HAS-ALIAS  F-SF)  F-N)) 
   ("sbfiz" #x13000000 #x7f800000 :bitfield OP-SBFIZ :CORE '(:Rd :Rn :IMM :WIDTH) QL-BF2 ((F-ALIAS  F-P1)  F-CONV)) 
   ("sbfx" #x13000000 #x7f800000 :bitfield OP-SBFX :CORE '(:Rd :Rn :IMM :WIDTH) QL-BF2 ((F-ALIAS  F-P1)  F-CONV)) 
   ("sxtb" #x13001c00 #x7fbffc00 :bitfield 0 :CORE '(:Rd :Rn) QL-EXT (((F-ALIAS  F-P3)  F-SF)  F-N)) 
   ("sxth" #x13003c00 #x7fbffc00 :bitfield 0 :CORE '(:Rd :Rn) QL-EXT (((F-ALIAS  F-P3)  F-SF)  F-N)) 
   ("sxtw" #x93407c00 #xfffffc00 :bitfield 0 :CORE '(:Rd :Rn) QL-EXT-W (F-ALIAS  F-P3)) 
   ("asr" #x13000000 #x7f800000 :bitfield OP-ASR-IMM :CORE '(:Rd :Rn :IMM) QL-SHIFT ((F-ALIAS  F-P2)  F-CONV)) 
   ("bfm" #x33000000 #x7f800000 :bitfield 0 :CORE '(:Rd :Rn :IMMR :IMMS) QL-BF ((F-HAS-ALIAS  F-SF)  F-N)) 
   ("bfi" #x33000000 #x7f800000 :bitfield OP-BFI :CORE '(:Rd :Rn :IMM :WIDTH) QL-BF2 ((F-ALIAS  F-P1)  F-CONV)) 
   ("bfxil" #x33000000 #x7f800000 :bitfield OP-BFXIL :CORE '(:Rd :Rn :IMM :WIDTH) QL-BF2 ((F-ALIAS  F-P1)  F-CONV)) 
   ("ubfm" #x53000000 #x7f800000 :bitfield 0 :CORE '(:Rd :Rn :IMMR :IMMS) QL-BF ((F-HAS-ALIAS  F-SF)  F-N)) 
   ("ubfiz" #x53000000 #x7f800000 :bitfield OP-UBFIZ :CORE '(:Rd :Rn :IMM :WIDTH) QL-BF2 ((F-ALIAS  F-P1)  F-CONV)) 
   ("ubfx" #x53000000 #x7f800000 :bitfield OP-UBFX :CORE '(:Rd :Rn :IMM :WIDTH) QL-BF2 ((F-ALIAS  F-P1)  F-CONV)) 
   ("uxtb" #x53001c00 #xfffffc00 :bitfield OP-UXTB :CORE '(:Rd :Rn) QL-I2SAMEW (F-ALIAS  F-P3)) 
   ("uxth" #x53003c00 #xfffffc00 :bitfield OP-UXTH :CORE '(:Rd :Rn) QL-I2SAMEW (F-ALIAS  F-P3)) 
   ("lsl" #x53000000 #x7f800000 :bitfield OP-LSL-IMM :CORE '(:Rd :Rn :IMM) QL-SHIFT ((F-ALIAS  F-P2)  F-CONV)) 
   ("lsr" #x53000000 #x7f800000 :bitfield OP-LSR-IMM :CORE '(:Rd :Rn :IMM) QL-SHIFT ((F-ALIAS  F-P2)  F-CONV)) 
   ("b" #x14000000 #xfc000000 :branch-imm OP-B :CORE '(:ADDR-PCREL26) QL-PCREL-26 0) 
   ("bl" #x94000000 #xfc000000 :branch-imm OP-BL :CORE '(:ADDR-PCREL26) QL-PCREL-26 0) 
   ("br" #xd61f0000 #xfffffc1f :branch-reg 0 :CORE '(:Rn) QL-I1X 0) 
   ("blr" #xd63f0000 #xfffffc1f :branch-reg 0 :CORE '(:Rn) QL-I1X 0) 
   ("ret" #xd65f0000 #xfffffc1f :branch-reg 0 :CORE '(:Rn) QL-I1X (F-OPD0-OPT  F-DEFAULT) (30)) 
   ("eret" #xd69f03e0 #xffffffff :branch-reg 0 :CORE '() () 0) 
   ("drps" #xd6bf03e0 #xffffffff :branch-reg 0 :CORE '() () 0) 
   ("cbz" #x34000000 #x7f000000 :compbranch 0 :CORE '(:Rt :ADDR-PCREL19) QL-R-PCREL F-SF) 
   ("cbnz" #x35000000 #x7f000000 :compbranch 0 :CORE '(:Rt :ADDR-PCREL19) QL-R-PCREL F-SF) 
   ("b.c" #x54000000 #xff000010 :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL F-COND) 
   ("ccmn" #x3a400800 #x7fe00c10 :condcmp-imm 0 :CORE '(:Rn :CCMP-IMM :NZCV :COND) QL-CCMP-IMM F-SF) 
   ("ccmp" #x7a400800 #x7fe00c10 :condcmp-imm 0 :CORE '(:Rn :CCMP-IMM :NZCV :COND) QL-CCMP-IMM F-SF) 
   ("ccmn" #x3a400000 #x7fe00c10 :condcmp-reg 0 :CORE '(:Rn :Rm :NZCV :COND) QL-CCMP F-SF) 
   ("ccmp" #x7a400000 #x7fe00c10 :condcmp-reg 0 :CORE '(:Rn :Rm :NZCV :COND) QL-CCMP F-SF) 
   ("csel" #x1a800000 #x7fe00c00 :condsel 0 :CORE '(:Rd :Rn :Rm :COND) QL-CSEL F-SF) 
   ("csinc" #x1a800400 #x7fe00c00 :condsel 0 :CORE '(:Rd :Rn :Rm :COND) QL-CSEL (F-HAS-ALIAS  F-SF)) 
   ("cinc" #x1a800400 #x7fe00c00 :condsel OP-CINC :CORE '(:Rd :Rn :COND) QL-CSEL ((F-ALIAS  F-SF)  F-CONV)) 
   ("cset" #x1a9f07e0 #x7fff0fe0 :condsel OP-CSET :CORE '(:Rd :COND) QL-DST-R (((F-ALIAS  F-P1)  F-SF)  F-CONV)) 
   ("csinv" #x5a800000 #x7fe00c00 :condsel 0 :CORE '(:Rd :Rn :Rm :COND) QL-CSEL (F-HAS-ALIAS  F-SF)) 
   ("cinv" #x5a800000 #x7fe00c00 :condsel OP-CINV :CORE '(:Rd :Rn :COND) QL-CSEL ((F-ALIAS  F-SF)  F-CONV)) 
   ("csetm" #x5a9f03e0 #x7fff0fe0 :condsel OP-CSETM :CORE '(:Rd :COND) QL-DST-R (((F-ALIAS  F-P1)  F-SF)  F-CONV)) 
   ("csneg" #x5a800400 #x7fe00c00 :condsel 0 :CORE '(:Rd :Rn :Rm :COND) QL-CSEL (F-HAS-ALIAS  F-SF)) 
   ("cneg" #x5a800400 #x7fe00c00 :condsel OP-CNEG :CORE '(:Rd :Rn :COND) QL-CSEL ((F-ALIAS  F-SF)  F-CONV)) 
   ("aese" #x4e284800 #xfffffc00 :cryptoaes 0 :CRYPTO '(:Vd :Vn) QL-V2SAME16B 0) 
   ("aesd" #x4e285800 #xfffffc00 :cryptoaes 0 :CRYPTO '(:Vd :Vn) QL-V2SAME16B 0) 
   ("aesmc" #x4e286800 #xfffffc00 :cryptoaes 0 :CRYPTO '(:Vd :Vn) QL-V2SAME16B 0) 
   ("aesimc" #x4e287800 #xfffffc00 :cryptoaes 0 :CRYPTO '(:Vd :Vn) QL-V2SAME16B 0) 
   ("sha1h" #x5e280800 #xfffffc00 :cryptosha2 0 :CRYPTO '(:Fd :Fn) QL-2SAMES 0) 
   ("sha1su1" #x5e281800 #xfffffc00 :cryptosha2 0 :CRYPTO '(:Vd :Vn) QL-V2SAME4S 0) 
   ("sha256su0" #x5e282800 #xfffffc00 :cryptosha2 0 :CRYPTO '(:Vd :Vn) QL-V2SAME4S 0) 
   ("sha1c" #x5e000000 #xffe0fc00 :cryptosha3 0 :CRYPTO '(:Fd :Fn :Vm) QL-SHAUPT 0) 
   ("sha1p" #x5e001000 #xffe0fc00 :cryptosha3 0 :CRYPTO '(:Fd :Fn :Vm) QL-SHAUPT 0)
 
   ("sha1m" #x5e002000 #xffe0fc00 :cryptosha3 0 :CRYPTO '(:Fd :Fn :Vm) QL-SHAUPT 0) 
   ("sha1su0" #x5e003000 #xffe0fc00 :cryptosha3 0 :CRYPTO '(:Vd :Vn :Vm) QL-V3SAME4S 0) 
   ("sha256h" #x5e004000 #xffe0fc00 :cryptosha3 0 :CRYPTO '(:Fd :Fn :Vm) QL-SHA256UPT 0) 
   ("sha256h2" #x5e005000 #xffe0fc00 :cryptosha3 0 :CRYPTO '(:Fd :Fn :Vm) QL-SHA256UPT 0) 
   ("sha256su1" #x5e006000 #xffe0fc00 :cryptosha3 0 :CRYPTO '(:Vd :Vn :Vm) QL-V3SAME4S 0) 
   ("rbit" #x5ac00000 #x7ffffc00 :dp-1src 0 :CORE '(:Rd :Rn) QL-I2SAME F-SF) 
   ("rev16" #x5ac00400 #x7ffffc00 :dp-1src 0 :CORE '(:Rd :Rn) QL-I2SAME F-SF) 
   ("rev" #x5ac00800 #xfffffc00 :dp-1src 0 :CORE '(:Rd :Rn) QL-I2SAMEW 0) 
   ("rev" #xdac00c00 #x7ffffc00 :dp-1src 0 :CORE '(:Rd :Rn) QL-I2SAMEX 0) 
   ("clz" #x5ac01000 #x7ffffc00 :dp-1src 0 :CORE '(:Rd :Rn) QL-I2SAME F-SF) 
   ("cls" #x5ac01400 #x7ffffc00 :dp-1src 0 :CORE '(:Rd :Rn) QL-I2SAME F-SF) 
   ("rev32" #xdac00800 #xfffffc00 :dp-1src 0 :CORE '(:Rd :Rn) QL-I2SAMEX 0) 

   ("udiv" #x1ac00800 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) 0)
   ("udiv" #x9ac00800 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) 0) 
   ("sdiv" #x1ac00c00 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) 0) 
   ("sdiv" #x9ac00c00 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) 0) 

   ("lslv" #x1ac02000 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-HAS-ALIAS)
   ("lslv" #x9ac02000 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-HAS-ALIAS) 
   ("lsl" #x1ac02000 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-ALIAS)
   ("lsl" #x9ac02000 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-ALIAS) 
   ("lsrv" #x1ac02400 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-HAS-ALIAS) 
   ("lsrv" #x9ac02400 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-HAS-ALIAS))
  ("lsr" #x1ac02400 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-ALIAS) 
  ("lsr" #x9ac02400 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-ALIAS)
  ("asrv" #x1ac02800 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-HAS-ALIAS)
  ("asrv" #x9ac02800 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-HAS-ALIAS)
  ("asr" #x1ac02800 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-ALIAS)
  ("asr" #x9ac02800 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-ALIAS)
  ("rorv" #x1ac02c00 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-HAS-ALIAS)
  ("rorv" #x9ac02c00 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-HAS-ALIAS)
  ("ror" #x1ac02c00 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-ALIAS)
  ("ror" #x9ac02c00 #xffe0fc00 :dp-2src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-ALIAS)

  ("madd" #x1b000000 #x7fe08000 :dp-3src 0 :CORE '(:Rd :Rn :Rm :Ra) QL-I4SAMER (F-HAS-ALIAS  F-SF)) 
  ("mul" #x1b007c00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-ALIAS) 
  ("mul" #x9b007c00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-ALIAS) 
  ("msub" #x1b008000 #x7fe08000 :dp-3src 0 :CORE '(:Rd :Rn :Rm :Ra) QL-I4SAMER (F-HAS-ALIAS  F-SF)) 
  ("mneg" #x1b00fc00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:w :w :w) F-ALIAS) 
  ("mneg" #x9b00fc00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:x :x :x) F-ALIAS)
  ("smaddl" #x9b200000 #xffe08000 :dp-3src 0 :CORE '(:Rd :Rn :Rm :Ra) '(:x :w :w :x) F-HAS-ALIAS) 
  ("smull" #x9b207c00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:X :W :W) F-ALIAS) 
  ("smsubl" #x9b208000 #xffe08000 :dp-3src 0 :CORE '(:Rd :Rn :Rm :Ra) '(:X :W :W :X) F-HAS-ALIAS) 
  ("smnegl" #x9b20fc00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:X :W :W) F-ALIAS) 
  ("smulh" #x9b407c00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:X :X :X) 0) 
  ("umaddl" #x9ba00000 #xffe08000 :dp-3src 0 :CORE '(:Rd :Rn :Rm :Ra) '(:X :W :W :X) F-HAS-ALIAS) 
  ("umull" #x9ba07c00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:X :W :W) F-ALIAS) 
  ("umsubl" #x9ba08000 #xffe08000 :dp-3src 0 :CORE '(:Rd :Rn :Rm :Ra) '(:X :W :W :X) F-HAS-ALIAS) 
  ("umnegl" #x9ba0fc00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:X :W :W) F-ALIAS) 
  ("umulh" #x9bc07c00 #xffe0fc00 :dp-3src 0 :CORE '(:Rd :Rn :Rm) '(:X :X :X) 0) 
  ("svc" #xd4000001 #xffe0001f :exception 0 :CORE '(:EXCEPTION) () 0) 
  ("hvc" #xd4000002 #xffe0001f :exception 0 :CORE '(:EXCEPTION) () 0) 
  ("smc" #xd4000003 #xffe0001f :exception 0 :CORE '(:EXCEPTION) () 0) 
  ("brk" #xd4200000 #xffe0001f :exception 0 :CORE '(:EXCEPTION) () 0) 
  ("hlt" #xd4400000 #xffe0001f :exception 0 :CORE '(:EXCEPTION) () 0) 
  ("dcps1" #xd4a00001 #xffe0001f :exception 0 :CORE '(:EXCEPTION) () (F-OPD0-OPT  F-DEFAULT) (0)) 
  ("dcps2" #xd4a00002 #xffe0001f :exception 0 :CORE '(:EXCEPTION) () (F-OPD0-OPT  F-DEFAULT) (0)) 
  ("dcps3" #xd4a00003 #xffe0001f :exception 0 :CORE '(:EXCEPTION) () (F-OPD0-OPT  F-DEFAULT) (0)) 
  ("extr" #x13800000 #x7fa00000 :extract 0 :CORE '(:Rd :Rn :Rm :IMMS) QL-EXTR ((F-HAS-ALIAS  F-SF)  F-N)) 
  ("ror" #x13800000 #x7fa00000 :extract OP-ROR-IMM :CORE '(:Rd :Rm :IMMS) QL-SHIFT (F-ALIAS  F-CONV)) 
  ("scvtf" #x1e020000 #x7f3f0000 :float2fix 0 FP '(:Fd :Rn :FBITS) QL-FIX2FP (F-FPTYPE  F-SF)) 
  ("ucvtf" #x1e030000 #x7f3f0000 :float2fix 0 FP '(:Fd :Rn :FBITS) QL-FIX2FP (F-FPTYPE  F-SF)) 
  ("fcvtzs" #x1e180000 #x7f3f0000 :float2fix 0 FP '(:Rd :Fn :FBITS) QL-FP2FIX (F-FPTYPE  F-SF)) 
  ("fcvtzu" #x1e190000 #x7f3f0000 :float2fix 0 FP '(:Rd :Fn :FBITS) QL-FP2FIX (F-FPTYPE  F-SF)) 
  ("fcvtns" #x1e200000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fcvtnu" #x1e210000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("scvtf" #x1e220000 #x7f3ffc00 :float2int 0 FP '(:Fd :Rn) QL-INT2FP (F-FPTYPE  F-SF)) 
  ("ucvtf" #x1e230000 #x7f3ffc00 :float2int 0 FP '(:Fd :Rn) QL-INT2FP (F-FPTYPE  F-SF)) 
  ("fcvtas" #x1e240000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fcvtau" #x1e250000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fmov" #x1e260000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fmov" #x1e270000 #x7f3ffc00 :float2int 0 FP '(:Fd :Rn) QL-INT2FP (F-FPTYPE  F-SF)) 
  ("fcvtps" #x1e280000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fcvtpu" #x1e290000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fcvtms" #x1e300000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fcvtmu" #x1e310000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fcvtzs" #x1e380000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fcvtzu" #x1e390000 #x7f3ffc00 :float2int 0 FP '(:Rd :Fn) QL-FP2INT (F-FPTYPE  F-SF)) 
  ("fmov" #x9eae0000 #xfffffc00 :float2int 0 FP '(:Rd :VnD1) QL-XVD1 0) 
  ("fmov" #x9eaf0000 #xfffffc00 :float2int 0 FP '(:VdD1 :Rn) QL-VD1X 0) 
  ("fccmp" #x1e200400 #xff200c10 :floatccmp 0 FP '(:Fn :Fm :NZCV :COND) QL-FCCMP F-FPTYPE) 
  ("fccmpe" #x1e200410 #xff200c10 :floatccmp 0 FP '(:Fn :Fm :NZCV :COND) QL-FCCMP F-FPTYPE) 
  ("fcmp" #x1e202000 #xff20fc1f :floatcmp 0 FP '(:Fn :Fm) QL-FP2 F-FPTYPE) 
  ("fcmpe" #x1e202010 #xff20fc1f :floatcmp 0 FP '(:Fn :Fm) QL-FP2 F-FPTYPE) 
  ("fcmp" #x1e202008 #xff20fc1f :floatcmp 0 FP '(:Fn :FPIMM0) QL-DST-SD F-FPTYPE) 
  ("fcmpe" #x1e202018 #xff20fc1f :floatcmp 0 FP '(:Fn :FPIMM0) QL-DST-SD F-FPTYPE) 
  ("fmov" #x1e204000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("fabs" #x1e20c000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("fneg" #x1e214000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("fsqrt" #x1e21c000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("fcvt" #x1e224000 #xff3e7c00 :floatdp1 OP-FCVT FP '(:Fd :Fn) QL-FCVT (F-FPTYPE  F-MISC)) 
  ("frintn" #x1e244000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("frintp" #x1e24c000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("frintm" #x1e254000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("frintz" #x1e25c000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("frinta" #x1e264000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("frintx" #x1e274000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("frinti" #x1e27c000 #xff3ffc00 :floatdp1 0 FP '(:Fd :Fn) QL-FP2 F-FPTYPE) 
  ("fmul" #x1e200800 #xff20fc00 :floatdp2 0 FP '(:Fd :Fn :Fm) QL-FP3 F-FPTYPE) 
  ("fdiv" #x1e201800 #xff20fc00 :floatdp2 0 FP '(:Fd :Fn :Fm) QL-FP3 F-FPTYPE) 
  ("fadd" #x1e202800 #xff20fc00 :floatdp2 0 FP '(:Fd :Fn :Fm) QL-FP3 F-FPTYPE) 
  ("fsub" #x1e203800 #xff20fc00 :floatdp2 0 FP '(:Fd :Fn :Fm) QL-FP3 F-FPTYPE) 
  ("fmax" #x1e204800 #xff20fc00 :floatdp2 0 FP '(:Fd :Fn :Fm) QL-FP3 F-FPTYPE) 
  ("fmin" #x1e205800 #xff20fc00 :floatdp2 0 FP '(:Fd :Fn :Fm) QL-FP3 F-FPTYPE) 
  ("fmaxnm" #x1e206800 #xff20fc00 :floatdp2 0 FP '(:Fd :Fn :Fm) QL-FP3 F-FPTYPE) 
  ("fminnm" #x1e207800 #xff20fc00 :floatdp2 0 FP '(:Fd :Fn :Fm) QL-FP3 F-FPTYPE) 
  ("fnmul" #x1e208800 #xff20fc00 :floatdp2 0 FP '(:Fd :Fn :Fm) QL-FP3 F-FPTYPE) 
  ("fmadd" #x1f000000 #xff208000 :floatdp3 0 FP '(:Fd :Fn :Fm :Fa) QL-FP4 F-FPTYPE) 
  ("fmsub" #x1f008000 #xff208000 :floatdp3 0 FP '(:Fd :Fn :Fm :Fa) QL-FP4 F-FPTYPE) 
  ("fnmadd" #x1f200000 #xff208000 :floatdp3 0 FP '(:Fd :Fn :Fm :Fa) QL-FP4 F-FPTYPE) 
  ("fnmsub" #x1f208000 #xff208000 :floatdp3 0 FP '(:Fd :Fn :Fm :Fa) QL-FP4 F-FPTYPE) 
  ("fmov" #x1e201000 #xff201fe0 :floatimm 0 FP '(:Fd :FPIMM) QL-DST-SD F-FPTYPE) 
  ("fcsel" #x1e200c00 #xff200c00 :floatsel 0 FP '(:Fd :Fn :Fm :COND) QL-FP-COND F-FPTYPE) 
  ("strb" #x38000400 #xffe00400 :ldst-imm9 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W8 0) 
  ("ldrb" #x38400400 #xffe00400 :ldst-imm9 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W8 0) 
  ("ldrsb" #x38800400 #xffa00400 :ldst-imm9 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R8 F-LDS-SIZE) 
  ("str" #x3c000400 #x3f600400 :ldst-imm9 0 :CORE '(:Ft :ADDR-SIMM9) QL-LDST-FP 0) 
  ("ldr" #x3c400400 #x3f600400 :ldst-imm9 0 :CORE '(:Ft :ADDR-SIMM9) QL-LDST-FP 0) 
  ("strh" #x78000400 #xffe00400 :ldst-imm9 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W16 0) 
  ("ldrh" #x78400400 #xffe00400 :ldst-imm9 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W16 0) 
  ("ldrsh" #x78800400 #xffa00400 :ldst-imm9 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R16 F-LDS-SIZE) 
  ("str" #xb8000400 #xbfe00400 :ldst-imm9 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R F-GPRSIZE-IN-Q) 
  ("ldr" #xb8400400 #xbfe00400 :ldst-imm9 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R F-GPRSIZE-IN-Q) 
  ("ldrsw" #xb8800400 #xffe00400 :ldst-imm9 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-X32 0) 
  ("strb" #x39000000 #xffc00000 :ldst-pos OP-STRB-POS :CORE '(:Rt :ADDR-UIMM12) QL-LDST-W8 0) 
  ("ldrb" #x39400000 #xffc00000 :ldst-pos OP-LDRB-POS :CORE '(:Rt :ADDR-UIMM12) QL-LDST-W8 0) 
  ("ldrsb" #x39800000 #xff800000 :ldst-pos OP-LDRSB-POS :CORE '(:Rt :ADDR-UIMM12) QL-LDST-R8 F-LDS-SIZE) 
  ("str" #x3d000000 #x3f400000 :ldst-pos OP-STRF-POS :CORE '(:Ft :ADDR-UIMM12) QL-LDST-FP 0) 
  ("ldr" #x3d400000 #x3f400000 :ldst-pos OP-LDRF-POS :CORE '(:Ft :ADDR-UIMM12) QL-LDST-FP 0) 
  ("strh" #x79000000 #xffc00000 :ldst-pos OP-STRH-POS :CORE '(:Rt :ADDR-UIMM12) QL-LDST-W16 0) 
  ("ldrh" #x79400000 #xffc00000 :ldst-pos OP-LDRH-POS :CORE '(:Rt :ADDR-UIMM12) QL-LDST-W16 0) 
  ("ldrsh" #x79800000 #xff800000 :ldst-pos OP-LDRSH-POS :CORE '(:Rt :ADDR-UIMM12) QL-LDST-R16 F-LDS-SIZE) 
  ("str" #xb9000000 #xbfc00000 :ldst-pos OP-STR-POS :CORE '(:Rt :ADDR-UIMM12) QL-LDST-R F-GPRSIZE-IN-Q) 
  ("ldr" #xb9400000 #xbfc00000 :ldst-pos OP-LDR-POS :CORE '(:Rt :ADDR-UIMM12) QL-LDST-R F-GPRSIZE-IN-Q) 
  ("ldrsw" #xb9800000 #xffc00000 :ldst-pos OP-LDRSW-POS :CORE '(:Rt :ADDR-UIMM12) QL-LDST-X32 0) 
  ("prfm" #xf9800000 #xffc00000 :ldst-pos OP-PRFM-POS :CORE '(:PRFOP :ADDR-UIMM12) QL-LDST-PRFM 0) 
  ("strb" #x38200800 #xffe00c00 :ldst-regoff 0 :CORE '(:Rt :ADDR-REGOFF) QL-LDST-W8 0) 
  ("ldrb" #x38600800 #xffe00c00 :ldst-regoff 0 :CORE '(:Rt :ADDR-REGOFF) QL-LDST-W8 0) 
  ("ldrsb" #x38a00800 #xffa00c00 :ldst-regoff 0 :CORE '(:Rt :ADDR-REGOFF) QL-LDST-R8 F-LDS-SIZE) 
  ("str" #x3c200800 #x3f600c00 :ldst-regoff 0 :CORE '(:Ft :ADDR-REGOFF) QL-LDST-FP 0) 
  ("ldr" #x3c600800 #x3f600c00 :ldst-regoff 0 :CORE '(:Ft :ADDR-REGOFF) QL-LDST-FP 0) 
  ("strh" #x78200800 #xffe00c00 :ldst-regoff 0 :CORE '(:Rt :ADDR-REGOFF) QL-LDST-W16 0) 
  ("ldrh" #x78600800 #xffe00c00 :ldst-regoff 0 :CORE '(:Rt :ADDR-REGOFF) QL-LDST-W16 0) 
  ("ldrsh" #x78a00800 #xffa00c00 :ldst-regoff 0 :CORE '(:Rt :ADDR-REGOFF) QL-LDST-R16 F-LDS-SIZE) 
  ("str" #xb8200800 #xbfe00c00 :ldst-regoff 0 :CORE '(:Rt :ADDR-REGOFF) QL-LDST-R F-GPRSIZE-IN-Q) 
  ("ldr" #xb8600800 #xbfe00c00 :ldst-regoff 0 :CORE '(:Rt :ADDR-REGOFF) QL-LDST-R F-GPRSIZE-IN-Q) 
  ("ldrsw" #xb8a00800 #xffe00c00 :ldst-regoff 0 :CORE '(:Rt :ADDR-REGOFF) QL-LDST-X32 0) 
  ("prfm" #xf8a00800 #xffe00c00 :ldst-regoff 0 :CORE '(:PRFOP :ADDR-REGOFF) QL-LDST-PRFM 0) 
  ("sttrb" #x38000800 #xffe00c00 :ldst-unpriv 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W8 0) 
  ("ldtrb" #x38400800 #xffe00c00 :ldst-unpriv 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W8 0) 
  ("ldtrsb" #x38800800 #xffa00c00 :ldst-unpriv 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R8 F-LDS-SIZE) 
  ("sttrh" #x78000800 #xffe00c00 :ldst-unpriv 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W16 0) 
  ("ldtrh" #x78400800 #xffe00c00 :ldst-unpriv 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W16 0) 
  ("ldtrsh" #x78800800 #xffa00c00 :ldst-unpriv 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R16 F-LDS-SIZE) 
  ("sttr" #xb8000800 #xbfe00c00 :ldst-unpriv 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R F-GPRSIZE-IN-Q) 
  ("ldtr" #xb8400800 #xbfe00c00 :ldst-unpriv 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R F-GPRSIZE-IN-Q) 
  ("ldtrsw" #xb8800800 #xffe00c00 :ldst-unpriv 0 :CORE '(:Rt :ADDR-SIMM9) QL-LDST-X32 0) 
  ("sturb" #x38000000 #xffe00c00 :ldst-unscaled OP-STURB :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W8 F-HAS-ALIAS) 
  ("ldurb" #x38400000 #xffe00c00 :ldst-unscaled OP-LDURB :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W8 F-HAS-ALIAS) 
  ("strb" #x38000000 #xffe00c00 :ldst-unscaled 0 :CORE '(:Rt :ADDR-SIMM9-2) QL-LDST-W8 F-ALIAS) 
  ("ldrb" #x38400000 #xffe00c00 :ldst-unscaled 0 :CORE '(:Rt :ADDR-SIMM9-2) QL-LDST-W8 F-ALIAS) 
  ("ldursb" #x38800000 #xffa00c00 :ldst-unscaled OP-LDURSB :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R8 (F-HAS-ALIAS  F-LDS-SIZE)) 
  ("ldrsb" #x38800000 #xffa00c00 :ldst-unscaled 0 :CORE '(:Rt :ADDR-SIMM9-2) QL-LDST-R8 (F-ALIAS  F-LDS-SIZE)) 
  ("stur" #x3c000000 #x3f600c00 :ldst-unscaled OP-STURV :CORE '(:Ft :ADDR-SIMM9) QL-LDST-FP F-HAS-ALIAS) 
  ("ldur" #x3c400000 #x3f600c00 :ldst-unscaled OP-LDURV :CORE '(:Ft :ADDR-SIMM9) QL-LDST-FP F-HAS-ALIAS) 
  ("str" #x3c000000 #x3f600c00 :ldst-unscaled 0 :CORE '(:Ft :ADDR-SIMM9-2) QL-LDST-FP F-ALIAS) 
  ("ldr" #x3c400000 #x3f600c00 :ldst-unscaled 0 :CORE '(:Ft :ADDR-SIMM9-2) QL-LDST-FP F-ALIAS) 
  ("sturh" #x78000000 #xffe00c00 :ldst-unscaled OP-STURH :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W16 F-HAS-ALIAS) 
  ("ldurh" #x78400000 #xffe00c00 :ldst-unscaled OP-LDURH :CORE '(:Rt :ADDR-SIMM9) QL-LDST-W16 F-HAS-ALIAS) 
  ("strh" #x78000000 #xffe00c00 :ldst-unscaled 0 :CORE '(:Rt :ADDR-SIMM9-2) QL-LDST-W16 F-ALIAS) 
  ("ldrh" #x78400000 #xffe00c00 :ldst-unscaled 0 :CORE '(:Rt :ADDR-SIMM9-2) QL-LDST-W16 F-ALIAS) 
  ("ldursh" #x78800000 #xffa00c00 :ldst-unscaled OP-LDURSH :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R16 (F-HAS-ALIAS  F-LDS-SIZE)) 
  ("ldrsh" #x78800000 #xffa00c00 :ldst-unscaled 0 :CORE '(:Rt :ADDR-SIMM9-2) QL-LDST-R16 (F-ALIAS  F-LDS-SIZE)) 
  ("stur" #xb8000000 #xbfe00c00 :ldst-unscaled OP-STUR :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R (F-HAS-ALIAS  F-GPRSIZE-IN-Q)) 
  ("ldur" #xb8400000 #xbfe00c00 :ldst-unscaled OP-LDUR :CORE '(:Rt :ADDR-SIMM9) QL-LDST-R (F-HAS-ALIAS  F-GPRSIZE-IN-Q)) 
  ("str" #xb8000000 #xbfe00c00 :ldst-unscaled 0 :CORE '(:Rt :ADDR-SIMM9-2) QL-LDST-R (F-ALIAS  F-GPRSIZE-IN-Q)) 
  ("ldr" #xb8400000 #xbfe00c00 :ldst-unscaled 0 :CORE '(:Rt :ADDR-SIMM9-2) QL-LDST-R (F-ALIAS  F-GPRSIZE-IN-Q)) 
  ("ldursw" #xb8800000 #xffe00c00 :ldst-unscaled OP-LDURSW :CORE '(:Rt :ADDR-SIMM9) QL-LDST-X32 F-HAS-ALIAS) 
  ("ldrsw" #xb8800000 #xffe00c00 :ldst-unscaled 0 :CORE '(:Rt :ADDR-SIMM9-2) QL-LDST-X32 F-ALIAS) 
  ("prfum" #xf8800000 #xffe00c00 :ldst-unscaled OP-PRFUM :CORE '(:PRFOP :ADDR-SIMM9) QL-LDST-PRFM F-HAS-ALIAS) 
  ("prfm" #xf8800000 #xffe00c00 :ldst-unscaled 0 :CORE '(:PRFOP :ADDR-SIMM9-2) QL-LDST-PRFM F-ALIAS) 
  ("stxrb" #x8007c00 #xffe0fc00 :ldstexcl 0 :CORE '(:Rs :Rt :ADDR-SIMPLE) QL-W2-LDST-EXC 0) 
  ("stlxrb" #x800fc00 #xffe0fc00 :ldstexcl 0 :CORE '(:Rs :Rt :ADDR-SIMPLE) QL-W2-LDST-EXC 0) 
  ("ldxrb" #x85f7c00 #xfffffc00 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-W1-LDST-EXC 0) 
  ("ldaxrb" #x85ffc00 #xfffffc00 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-W1-LDST-EXC 0) 
  ("stlrb" #x89ffc00 #xfffffc00 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-W1-LDST-EXC 0) 
  ("ldarb" #x8dffc00 #xfffffc00 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-W1-LDST-EXC 0) 
  ("stxrh" #x48007c00 #xfffffc00 :ldstexcl 0 :CORE '(:Rs :Rt :ADDR-SIMPLE) QL-W2-LDST-EXC 0) 
  ("stlxrh" #x4800fc00 #xfffffc00 :ldstexcl 0 :CORE '(:Rs :Rt :ADDR-SIMPLE) QL-W2-LDST-EXC 0) 
  ("ldxrh" #x485f7c00 #xfffffc00 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-W1-LDST-EXC 0) 
  ("ldaxrh" #x485ffc00 #xfffffc00 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-W1-LDST-EXC 0) 
  ("stlrh" #x489ffc00 #xfffffc00 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-W1-LDST-EXC 0) 
  ("ldarh" #x48dffc00 #xfffffc00 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-W1-LDST-EXC 0) 
  ("stxr" #x88007c00 #xbfe0fc00 :ldstexcl 0 :CORE '(:Rs :Rt :ADDR-SIMPLE) QL-R2-LDST-EXC F-GPRSIZE-IN-Q) 
  ("stlxr" #x8800fc00 #xbfe0fc00 :ldstexcl 0 :CORE '(:Rs :Rt :ADDR-SIMPLE) QL-R2-LDST-EXC F-GPRSIZE-IN-Q) 
  ("stxp" #x88200000 #xbfe0fc00 :ldstexcl 0 :CORE '(:Rs :Rt :Rt2 :ADDR-SIMPLE) QL-R3-LDST-EXC F-GPRSIZE-IN-Q) 
  ("stlxp" #x88208000 #xbfe08000 :ldstexcl 0 :CORE '(:Rs :Rt :Rt2 :ADDR-SIMPLE) QL-R3-LDST-EXC F-GPRSIZE-IN-Q) 
  ("ldxr" #x885f7c00 #xbfe08000 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-R1NIL F-GPRSIZE-IN-Q) 
  ("ldaxr" #x885ffc00 #xbfe0fc00 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-R1NIL F-GPRSIZE-IN-Q) 
  ("ldxp" #x887f0000 #xbfe08000 :ldstexcl 0 :CORE '(:Rt :Rt2 :ADDR-SIMPLE) QL-R2NIL F-GPRSIZE-IN-Q) 
  ("ldaxp" #x887f8000 #xbfe08000 :ldstexcl 0 :CORE '(:Rt :Rt2 :ADDR-SIMPLE) QL-R2NIL F-GPRSIZE-IN-Q) 
  ("stlr" #x889ffc00 #xbfe08000 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-R1NIL F-GPRSIZE-IN-Q) 
  ("ldar" #x88dffc00 #xbfe08000 :ldstexcl 0 :CORE '(:Rt :ADDR-SIMPLE) QL-R1NIL F-GPRSIZE-IN-Q) 
  ("stnp" #x28000000 #x7fc00000 :ldstnapair-offs 0 :CORE '(:Rt :Rt2 :ADDR-SIMM7) QL-LDST-PAIR-R F-SF) 
  ("ldnp" #x28400000 #x7fc00000 :ldstnapair-offs 0 :CORE '(:Rt :Rt2 :ADDR-SIMM7) QL-LDST-PAIR-R F-SF) 
  ("stnp" #x2c000000 #x3fc00000 :ldstnapair-offs 0 :CORE '(:Ft :Ft2 :ADDR-SIMM7) QL-LDST-PAIR-FP 0) 
  ("ldnp" #x2c400000 #x3fc00000 :ldstnapair-offs 0 :CORE '(:Ft :Ft2 :ADDR-SIMM7) QL-LDST-PAIR-FP 0) 
  ("stp" #x29000000 #x7ec00000 :ldstpair-off 0 :CORE '(:Rt :Rt2 :ADDR-SIMM7) QL-LDST-PAIR-R F-SF) 
  ("ldp" #x29400000 #x7ec00000 :ldstpair-off 0 :CORE '(:Rt :Rt2 :ADDR-SIMM7) QL-LDST-PAIR-R F-SF) 
  ("stp" #x2d000000 #x3fc00000 :ldstpair-off 0 :CORE '(:Ft :Ft2 :ADDR-SIMM7) QL-LDST-PAIR-FP 0) 
  ("ldp" #x2d400000 #x3fc00000 :ldstpair-off 0 :CORE '(:Ft :Ft2 :ADDR-SIMM7) QL-LDST-PAIR-FP 0) 
  ("ldpsw" #x69400000 #xffc00000 :ldstpair-off 0 :CORE '(:Rt :Rt2 :ADDR-SIMM7) QL-LDST-PAIR-X32 0) 
  ("stp" #x28800000 #x7ec00000 :ldstpair-indexed 0 :CORE '(:Rt :Rt2 :ADDR-SIMM7) QL-LDST-PAIR-R F-SF) 
  ("ldp" #x28c00000 #x7ec00000 :ldstpair-indexed 0 :CORE '(:Rt :Rt2 :ADDR-SIMM7) QL-LDST-PAIR-R F-SF) 
  ("stp" #x2c800000 #x3ec00000 :ldstpair-indexed 0 :CORE '(:Ft :Ft2 :ADDR-SIMM7) QL-LDST-PAIR-FP 0) 
  ("ldp" #x2cc00000 #x3ec00000 :ldstpair-indexed 0 :CORE '(:Ft :Ft2 :ADDR-SIMM7) QL-LDST-PAIR-FP 0) 
  ("ldpsw" #x68c00000 #xfec00000 :ldstpair-indexed 0 :CORE '(:Rt :Rt2 :ADDR-SIMM7) QL-LDST-PAIR-X32 0) 
  ("ldr" #x18000000 #xbf000000 :loadlit OP-LDR-LIT :CORE '(:Rt :ADDR-PCREL19) QL-R-PCREL F-GPRSIZE-IN-Q) 
  ("ldr" #x1c000000 #x3f000000 :loadlit OP-LDRV-LIT :CORE '(:Ft :ADDR-PCREL19) QL-FP-PCREL 0) 
  ("ldrsw" #x98000000 #xff000000 :loadlit OP-LDRSW-LIT :CORE '(:Rt :ADDR-PCREL19) QL-X-PCREL 0) 
  ("prfm" #xd8000000 #xff000000 :loadlit OP-PRFM-LIT :CORE '(:PRFOP :ADDR-PCREL19) QL-PRFM-PCREL 0) 
  ("and" #x12000000 #x7f800000 :log-imm 0 :CORE '(:Rd-SP :Rn :LIMM) QL-R2NIL (F-HAS-ALIAS  F-SF)) 
  ("bic" #x12000000 #x7f800000 :log-imm OP-BIC :CORE '(:Rd-SP :Rn :LIMM) QL-R2NIL ((F-ALIAS  F-PSEUDO)  F-SF)) 
  ("orr" #x32000000 #x7f800000 :log-imm 0 :CORE '(:Rd-SP :Rn :LIMM) QL-R2NIL (F-HAS-ALIAS  F-SF)) 
  ("mov" #x320003e0 #x7f8003e0 :log-imm OP-MOV-IMM-LOG :CORE '(:Rd-SP :IMM-MOV) QL-R1NIL (((F-ALIAS  F-P1)  F-SF)  F-CONV)) 
  ("eor" #x52000000 #x7f800000 :log-imm 0 :CORE '(:Rd-SP :Rn :LIMM) QL-R2NIL F-SF) 
  ("ands" #x72000000 #x7f800000 :log-imm 0 :CORE '(:Rd :Rn :LIMM) QL-R2NIL (F-HAS-ALIAS  F-SF)) 
  ("tst" #x7200001f #x7f80001f :log-imm 0 :CORE '(:Rn :LIMM) QL-R1NIL (F-ALIAS  F-SF)) 
  ("and" #xa000000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) 0)
  ("and" #x8a000000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) 0)
  ("bic" #xa200000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) 0)
  ("bic" #x8a200000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) 0)
  ("orr" #x2a000000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) F-HAS-ALIAS)
  ("orr" #xaa000000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) F-HAS-ALIAS) 

  ("mov" #x2a0003e0 #xff2003e0 :log-shift 0 :CORE '(:Rd :Rm) '(:w :w) F-ALIAS)
  ("mov" #xaa0003e0 #xff2003e0 :log-shift 0 :CORE '(:Rd :Rm) '(:x :x) F-ALIAS)
  ("uxtw" #x2a0003e0 #x7f2003e0 :log-shift OP-UXTW :CORE '(:Rd :Rm) QL-I2SAMEW (F-ALIAS  F-PSEUDO)) 
  ("orn" #x2a200000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) F-HAS-ALIAS) 
  ("orn" #xaa200000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) F-HAS-ALIAS)
 
  ("mvn" #x2a2003e0 #x7f2003e0 :log-shift 0 :CORE '(:Rd :Rm-SFT) QL-I2SAMER (F-ALIAS  F-SF)) 
  ("eor" #x4a000000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) 0)
  ("eor" #xca000000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) 0)
  ("eon" #x4a200000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) 0)
  ("eon" #xca200000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT)
   (:x :x :x-shift) 0) 
  ("ands" #x6a000000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) F-HAS-ALIAS) 
  ("ands" #xea000000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) F-HAS-ALIAS)
 
  ("tst" #x6a00001f #x7f20001f :log-shift 0 :CORE '(:Rn :Rm-SFT) QL-I2SAMER (F-ALIAS  F-SF)) 
  ("bics" #x6a200000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:w :w :w-shift) 0) 
  ("bics" #xea200000 #xff200000 :log-shift 0 :CORE '(:Rd :Rn :Rm-SFT) '(:x :x :x-shift) 0) 
  ("movn" #x12800000 #x7f800000 :movewide OP-MOVN :CORE '(:Rd :HALF) QL-DST-R (F-SF  F-HAS-ALIAS)) 
  ("mov" #x12800000 #x7f800000 :movewide OP-MOV-IMM-WIDEN :CORE '(:Rd :IMM-MOV) QL-DST-R ((F-SF  F-ALIAS)  F-CONV)) 
  ("movz" #x52800000 #x7f800000 :movewide OP-MOVZ :CORE '(:Rd :HALF) QL-DST-R (F-SF  F-HAS-ALIAS)) 
  ("mov" #x52800000 #x7f800000 :movewide OP-MOV-IMM-WIDE :CORE '(:Rd :IMM-MOV) QL-DST-R ((F-SF  F-ALIAS)  F-CONV)) 
  ("movk" #x72800000 #x7f800000 :movewide OP-MOVK :CORE '(:Rd :HALF) QL-DST-R F-SF) 
  ("adr" #x10000000 #x9f000000 :pcreladdr 0 :CORE '(:Rd :ADDR-PCREL21) QL-ADRP 0) 
  ("adrp" #x90000000 #x9f000000 :pcreladdr 0 :CORE '(:Rd :ADDR-ADRP) QL-ADRP 0) 
  ("msr" #xd500401f #xfff8f01f :ic-system 0 :CORE '(:PSTATEFIELD :UIMM4) () 0) 
  ("hint" #xd503201f #xfffff01f :ic-system 0 :CORE '(:UIMM7) () F-HAS-ALIAS) 
  ("nop" #xd503201f #xffffffff :ic-system 0 :CORE '() () F-ALIAS) 
  ("yield" #xd503203f #xffffffff :ic-system 0 :CORE '() () F-ALIAS) 
  ("wfe" #xd503205f #xffffffff :ic-system 0 :CORE '() () F-ALIAS) 
  ("wfi" #xd503207f #xffffffff :ic-system 0 :CORE '() () F-ALIAS) 
  ("sev" #xd503209f #xffffffff :ic-system 0 :CORE '() () F-ALIAS) 
  ("sevl" #xd50320bf #xffffffff :ic-system 0 :CORE '() () F-ALIAS) 
  ("clrex" #xd503305f #xfffff0ff :ic-system 0 :CORE '(:UIMM4) () (F-OPD0-OPT  F-DEFAULT) (#xF)) 
  ("dsb" #xd503309f #xfffff0ff :ic-system 0 :CORE '(:BARRIER) () 0) 
  ("dmb" #xd50330bf #xfffff0ff :ic-system 0 :CORE '(:BARRIER) () 0) 
  ("isb" #xd50330df #xfffff0ff :ic-system 0 :CORE '(:BARRIER-ISB) () (F-OPD0-OPT  F-DEFAULT) (#xF)) 
  ("sys" #xd5080000 #xfff80000 :ic-system 0 :CORE OP5 (UIMM3-OP1 :Cn Cm UIMM3-OP2 Rt) QL-SYS ((F-HAS-ALIAS  F-OPD4-OPT)  F-DEFAULT) (#x1F)) 
  ("at" #xd5080000 #xfff80000 :ic-system 0 :CORE '(:SYSREG-AT :Rt) QL-SRC-X F-ALIAS) 
  ("dc" #xd5080000 #xfff80000 :ic-system 0 :CORE '(:SYSREG-DC :Rt) QL-SRC-X F-ALIAS) 
  ("ic" #xd5080000 #xfff80000 :ic-system 0 :CORE '(:SYSREG-IC :Rt-SYS) QL-SRC-X ((F-ALIAS  F-OPD1-OPT)  F-DEFAULT) (#x1F)) 
  ("tlbi" #xd5080000 #xfff80000 :ic-system 0 :CORE '(:SYSREG-TLBI :Rt-SYS) QL-SRC-X ((F-ALIAS  F-OPD1-OPT)  F-DEFAULT) (#x1F)) 
  ("msr" #xd5100000 #xfff00000 :ic-system 0 :CORE '(:SYSREG :Rt) QL-SRC-X 0) 
  ("sysl" #xd5280000 #xfff80000 :ic-system 0 :CORE '(:Rt :UIMM3-OP1 :Cn :Cm :UIMM3-OP2) QL-SYSL 0) 
  ("mrs" #xd5300000 #xfff00000 :ic-system 0 :CORE '(:Rt :SYSREG) QL-DST-X 0) 
  ("tbz" #x36000000 #x7f000000 :testbranch 0 :CORE '(:Rt :BIT-NUM :ADDR-PCREL14) QL-PCREL-14 0) 
  ("tbnz" #x37000000 #x7f000000 :testbranch 0 :CORE '(:Rt :BIT-NUM :ADDR-PCREL14) QL-PCREL-14 0) 
  ("beq" #x54000000 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bne" #x54000001 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bcs" #x54000002 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bhs" #x54000002 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bcc" #x54000003 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("blo" #x54000003 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bmi" #x54000004 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bpl" #x54000005 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bvs" #x54000006 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bvc" #x54000007 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bhi" #x54000008 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bls" #x54000009 #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bge" #x5400000a #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("blt" #x5400000b #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("bgt" #x5400000c #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO)) 
  ("ble" #x5400000d #xff00001f :condbranch 0 :CORE '(:ADDR-PCREL19) QL-PCREL-NIL (F-ALIAS  F-PSEUDO))
 

  )

;;;=========================================================================
;;; LAP infrastructure for ARM64
;;; Structs, freelists, core DLL-based functions, instruction encoder,
;;; and arm64-finalize.
;;;=========================================================================

;;; ---- Structs ----

(defstruct (instruction-element (:include ccl::dll-node))
  address
  (size 0))

(defstruct (lap-instruction (:include instruction-element (size 4))
                            (:constructor %make-lap-instruction (source)))
  source
  (opcode 0))

(defstruct (lap-label (:include instruction-element)
                      (:constructor %%make-lap-label (name)))
  name
  refs)

;;; ---- Special variables & freelists ----

(defvar *lap-labels* nil)
(defvar *lap-instruction-freelist* nil)
(defvar *lap-label-freelist* nil)
(defvar *arm64-constants* nil)

;;; ---- Core DLL-based functions ----

(defun make-lap-instruction (form)
  (let* ((insn (ccl::alloc-dll-node *lap-instruction-freelist*)))
    (if (typep insn 'lap-instruction)
      (progn
        (setf (lap-instruction-source insn) form
              (lap-instruction-address insn) nil
              (lap-instruction-opcode insn) 0)
        insn)
      (%make-lap-instruction form))))

(defun emit-lap-instruction-element (insn seg)
  (ccl::append-dll-node insn seg)
  (let* ((addr (let* ((prev (ccl::dll-node-pred insn)))
                 (if (eq prev seg)
                   0
                   (the fixnum (+ (the fixnum (instruction-element-address prev))
                                  (the fixnum (instruction-element-size prev))))))))
    (setf (instruction-element-address insn) addr))
  insn)

(defun %make-lap-label (name)
  (let* ((lab (ccl::alloc-dll-node *lap-label-freelist*)))
    (if lab
      (progn
        (setf (lap-label-address lab) nil
              (lap-label-refs lab) nil
              (lap-label-name lab) name)
        lab)
      (%%make-lap-label name))))

(defun make-lap-label (name)
  (let* ((lab (%make-lap-label name)))
    (if (typep *lap-labels* 'hash-table)
      (setf (gethash name *lap-labels*) lab)
      (progn
        (push lab *lap-labels*)
        (if (> (length *lap-labels*) 255)
          (let* ((hash (make-hash-table :size 512 :test #'eq)))
            (dolist (l *lap-labels* (setq *lap-labels* hash))
              (setf (gethash (lap-label-name l) hash) l))))))
    lab))

(defun find-lap-label (name)
  (if (typep *lap-labels* 'hash-table)
    (gethash name *lap-labels*)
    (car (member name *lap-labels* :test #'eq :key #'lap-label-name))))

(defun lap-note-label-reference (labx insn type)
  (let* ((lab (or (find-lap-label labx)
                  (make-lap-label labx))))
    (push (cons insn type) (lap-label-refs lab))
    lab))

(defun emit-lap-label (seg name)
  (let* ((lab (find-lap-label name)))
    (if lab
      (when (lap-label-emitted-p lab)
        (error "Label ~s: multiply defined." name))
      (setq lab (make-lap-label name)))
    (emit-lap-instruction-element lab seg)))

(defun lap-label-emitted-p (lab)
  (not (null (lap-label-pred lab))))

(defun lap-label-address (lab)
  (instruction-element-address lab))

(defmacro do-lap-labels ((lab &optional result) &body body)
  (let* ((thunk-name (gensym))
         (k (gensym))
         (xlab (gensym)))
    `(flet ((,thunk-name (,lab) ,@body))
       (if (listp *lap-labels*)
         (dolist (,xlab *lap-labels*)
           (,thunk-name ,xlab))
         (maphash #'(lambda (,k ,xlab)
                      (declare (ignore ,k))
                      (,thunk-name ,xlab))
                  *lap-labels*))
       ,result)))

(defun section-size (seg)
  (let* ((last (ccl::dll-node-pred seg)))
    (if (eq last seg)
      0
      (the fixnum
        (+ (the fixnum (instruction-element-address last))
           (the fixnum (instruction-element-size last)))))))

(defun set-element-addresses (start seg)
  (ccl::do-dll-nodes (element seg start)
    (setf (instruction-element-address element) start)
    (incf start (instruction-element-size element))))

(defun set-field-value (insn bytespec val)
  (setf (lap-instruction-opcode insn)
        (dpb val bytespec (lap-instruction-opcode insn))))

(defun get-field-value (insn bytespec)
  (ldb bytespec (lap-instruction-opcode insn)))

;;; ---- Instruction encoder helpers ----

(defun need-arm64-gpr-encoding (x)
  "Return hardware GPR number 0-31.  Accepts integer 0-30, or symbol SP → 31."
  (cond ((and (typep x 'fixnum) (<= 0 x 30)) x)
        ((eq x 31) 31)
        ((and (symbolp x)
              (or (string-equal x "SP") (string-equal x "ZR")))
         31)
        (t (error "Not a valid ARM64 GPR encoding: ~s" x))))

(defun need-arm64-dfpr-encoding (x)
  "Double-float register: internal number 32-63 → hardware 0-31."
  (cond ((and (typep x 'fixnum) (<= 32 x 63)) (- x 32))
        ((and (typep x 'fixnum) (<= 0 x 31)) x)
        (t (error "Not a valid ARM64 double-float register: ~s" x))))

(defun need-arm64-sfpr-encoding (x)
  "Single-float register: internal number 64-95 → hardware 0-31."
  (cond ((and (typep x 'fixnum) (<= 64 x 95)) (- x 64))
        ((and (typep x 'fixnum) (<= 0 x 31)) x)
        (t (error "Not a valid ARM64 single-float register: ~s" x))))

(defun need-arm64-fpr-encoding (x)
  "Any FP register: 32-63 (double) or 64-95 (single) → hardware 0-31."
  (cond ((and (typep x 'fixnum) (<= 32 x 63)) (- x 32))
        ((and (typep x 'fixnum) (<= 64 x 95)) (- x 64))
        ((and (typep x 'fixnum) (<= 0 x 31)) x)
        (t (error "Not a valid ARM64 FPR encoding: ~s" x))))

(defun arm64-gpr-p (x)
  "True if x is a GPR number (0-30) or sp symbol."
  (or (and (typep x 'fixnum) (<= 0 x 30))
      (eql x 31)
      (and (symbolp x)
           (or (string-equal x "SP") (string-equal x "ZR")))))

(defun arm64-dfpr-p (x)
  (and (typep x 'fixnum) (<= 32 x 63)))

(defun arm64-sfpr-p (x)
  (and (typep x 'fixnum) (<= 64 x 95)))

(defun arm64-fpr-p (x)
  (and (typep x 'fixnum) (<= 32 x 95)))

(defun encode-cond-keyword (kw)
  "Map condition keyword (:eq :ne :hs :lo :mi :pl :vs :vc :hi :ls :ge :lt :gt :le) to 4-bit code."
  (case kw
    (:eq 0) (:ne 1)
    (:cs 2) (:hs 2) (:cc 3) (:lo 3)
    (:mi 4) (:pl 5) (:vs 6) (:vc 7)
    (:hi 8) (:ls 9) (:ge 10) (:lt 11)
    (:gt 12) (:le 13) (:al 14) (:nv 15)
    (t (error "Unknown condition keyword: ~s" kw))))

(defun parse-mnemonic-condition (mnemonic)
  "If MNEMONIC is like B.EQ, return (values :B cond-code).  Otherwise NIL."
  (let* ((name (string mnemonic))
         (dot (position #\. name)))
    (when dot
      (let* ((base (subseq name 0 dot))
             (cond-str (subseq name (1+ dot)))
             (cond-val (lookup-arm64-condition-name cond-str)))
        (when cond-val
          (values (intern base (symbol-package mnemonic)) cond-val))))))

;;; ---- Main instruction encoder ----

(defun arm64-encode-instruction (form)
  "Encode a resolved S-expression instruction FORM into a 32-bit opcode.
   Returns (values opcode label-ref-type) where label-ref-type is
   :B, :B-COND, :CBZ, :CBNZ, or NIL."
  (when (null form) (return-from arm64-encode-instruction 0))
  (let* ((mnemonic (car form))
         (ops (cdr form)))
    ;; Check for conditional branch: b.eq, b.ne, etc.
    (multiple-value-bind (base-mnem cond-code)
        (parse-mnemonic-condition mnemonic)
      (when (and base-mnem (string-equal base-mnem "B"))
        ;; Conditional branch: b.cond label
        ;; Encoding: 0101 0100 [imm19] 0 [cond:4]
        (return-from arm64-encode-instruction
          (values (logior #x54000000 (logand cond-code #xf))
                  :b-cond))))
    (let* ((name (string mnemonic)))
      (flet ((op (n) (nth n ops))
             (gpr (x) (need-arm64-gpr-encoding x))
             (dfpr (x) (need-arm64-dfpr-encoding x))
             (sfpr (x) (need-arm64-sfpr-encoding x))
             (fpr (x) (need-arm64-fpr-encoding x))
             (imm-val (x)
               (if (and (consp x) (eq (car x) :$))
                 (cadr x)
                 (error "Expected (:$ val), got ~s" x))))
        (declare (inline op gpr dfpr sfpr fpr))
        (macrolet ((is-imm (x) `(and (consp ,x) (eq (car ,x) :$)))
                   (is-addr (x) `(and (consp ,x) (eq (car ,x) :@)))
                   (is-pre (x) `(and (consp ,x) (eq (car ,x) :@!)))
                   (is-post (x) `(and (consp ,x) (eq (car ,x) :@+)))
                   (is-shift (x k) `(and (consp ,x) (eq (car ,x) ,k)))
                   (is-reg-pair-next (x) `(and (consp ,x) (eq (car ,x) :+))))
          (cond
            ;;=== NOP ===
            ((string-equal name "NOP")
             #xd503201f)

            ;;=== HLT ===
            ((string-equal name "HLT")
             (let ((imm16 (imm-val (op 0))))
               (logior #xd4400000 (ash (logand imm16 #xffff) 5))))

            ;;=== RET ===
            ((string-equal name "RET")
             (if ops
               (logior #xd65f0000 (ash (gpr (op 0)) 5))
               #xd65f03c0))  ; ret x30

            ;;=== BR / BLR ===
            ((string-equal name "BR")
             (logior #xd61f0000 (ash (gpr (op 0)) 5)))
            ((string-equal name "BLR")
             (logior #xd63f0000 (ash (gpr (op 0)) 5)))

            ;;=== B (unconditional) ===
            ((string-equal name "B")
             ;; B label — offset filled in by finalize
             ;; Check for conditional: (b (:? cond) label) or (b (:~ cond) label)
             (if (and (consp (op 0))
                      (or (eq (car (op 0)) :?)
                          (eq (car (op 0)) :~)))
               ;; Conditional branch
               (let* ((cond-form (op 0))
                      (cond-key (car cond-form))
                      (cond-name (cadr cond-form))
                      (cc (need-arm64-condition-name cond-name)))
                 (when (eq cond-key :~)
                   (setq cc (logxor cc 1)))
                 (values (logior #x54000000 (logand cc #xf))
                         :b-cond))
               (values #x14000000 :b)))

            ;;=== BL ===
            ((string-equal name "BL")
             (values #x94000000 :b))

            ;;=== CBZ / CBNZ ===
            ((string-equal name "CBZ")
             (let ((dest (gpr (op 0))))
               (values (logior #xb4000000 dest) :cbz)))
            ((string-equal name "CBNZ")
             (let ((dest (gpr (op 0))))
               (values (logior #xb5000000 dest) :cbnz)))

            ;;=== ADR ===
            ((string-equal name "ADR")
             (let ((rd (gpr (op 0))))
               (values (logior #x10000000 rd) :adr)))

            ;;=== MOV ===
            ((string-equal name "MOV")
             (let ((dst (op 0))
                   (src (op 1)))
               (cond
                 ;; mov rd, (:$ imm) — try movz for small non-negative
                 ((is-imm src)
                  (let ((val (imm-val src)))
                    (cond
                      ;; Try logical immediate encoding (for mov = ORR Xd, XZR, #imm)
                      ((and (not (zerop val))
                            (not (= (ldb (byte 64 0) val) #xffffffffffffffff))
                            (encode-logical-immediate val))
                       (let ((enc (encode-logical-immediate val)))
                         (logior #xb2000000
                                 (ash (ldb (byte 1 12) enc) 22)  ; N
                                 (ash (ldb (byte 6 6) enc) 16)   ; immr
                                 (ash (ldb (byte 6 0) enc) 10)   ; imms
                                 (ash 31 5)                       ; Rn = XZR
                                 (gpr dst))))
                      ;; Small non-negative: use movz
                      ((and (>= val 0) (< val #x10000))
                       (logior #xd2800000 (ash (logand val #xffff) 5) (gpr dst)))
                      ;; Small negative: use movn
                      ((and (< val 0) (>= val -65536))
                       (logior #x92800000
                               (ash (logand (lognot val) #xffff) 5)
                               (gpr dst)))
                      (t (error "MOV immediate ~s too large for single instruction" val)))))
                 ;; mov rd, rn — ORR Xd, XZR, Xn
                 ((arm64-gpr-p src)
                  (logior #xaa0003e0 (ash (gpr src) 16) (gpr dst)))
                 (t (error "Invalid MOV operands: ~s" form)))))

            ;;=== MOVZ ===
            ((string-equal name "MOVZ")
             (let* ((rd (gpr (op 0)))
                    (imm-form (op 1))
                    (val (imm-val imm-form))
                    (shift 0))
               ;; Optional shift: (:lsl 16), (:lsl 32), (:lsl 48)
               (when (op 2)
                 (let ((s (op 2)))
                   (cond ((is-shift s :lsl)
                          (setq shift (truncate (cadr s) 16)))
                         ((and (typep s 'fixnum) (member s '(0 16 32 48)))
                          (setq shift (truncate s 16)))
                         (t (error "Invalid MOVZ shift: ~s" s)))))
               (logior #xd2800000
                       (ash (logand shift 3) 21)
                       (ash (logand val #xffff) 5)
                       rd)))

            ;;=== MOVK ===
            ((string-equal name "MOVK")
             (let* ((rd (gpr (op 0)))
                    (imm-form (op 1))
                    (val (imm-val imm-form))
                    (shift 0))
               (when (op 2)
                 (let ((s (op 2)))
                   (cond ((is-shift s :lsl)
                          (setq shift (truncate (cadr s) 16)))
                         ((and (typep s 'fixnum) (member s '(0 16 32 48)))
                          (setq shift (truncate s 16)))
                         (t (error "Invalid MOVK shift: ~s" s)))))
               (logior #xf2800000
                       (ash (logand shift 3) 21)
                       (ash (logand val #xffff) 5)
                       rd)))

            ;;=== ADD / SUB / ADDS / SUBS / CMN / CMP / NEG / NEGS ===
            ((or (string-equal name "ADD") (string-equal name "SUB")
                 (string-equal name "ADDS") (string-equal name "SUBS")
                 (string-equal name "CMN") (string-equal name "CMP")
                 (string-equal name "NEG") (string-equal name "NEGS"))
             (let* ((is-sub (or (string-equal name "SUB")
                                (string-equal name "SUBS")
                                (string-equal name "CMP")
                                (string-equal name "NEG")
                                (string-equal name "NEGS")))
                    (sets-flags (or (string-equal name "ADDS")
                                    (string-equal name "SUBS")
                                    (string-equal name "CMP")
                                    (string-equal name "CMN")
                                    (string-equal name "NEGS")))
                    (is-cmp-cmn (or (string-equal name "CMP")
                                     (string-equal name "CMN")))
                    (is-neg (or (string-equal name "NEG")
                                (string-equal name "NEGS"))))
               (cond
                 ;; CMP rn, (:$ imm) or CMP rn, rm
                 (is-cmp-cmn
                  (let ((rn (op 0))
                        (src (op 1)))
                    (if (is-imm src)
                      ;; CMP/CMN rn, #imm — addsub-imm with rd=xzr
                      (let ((imm (imm-val src)))
                        (logior (if is-sub #xf1000000 #xb1000000)
                                (ash (logand imm #xfff) 10)
                                (ash (gpr rn) 5)
                                31))  ; Rd = XZR(31)
                      ;; CMP/CMN rn, rm — addsub-shift with rd=xzr
                      (logior (if is-sub #xeb000000 #xab000000)
                              (ash (gpr src) 16)
                              (ash (gpr rn) 5)
                              31))))
                 ;; NEG/NEGS rd, rm  = SUB/SUBS rd, xzr, rm
                 (is-neg
                  (let ((rd (op 0))
                        (rm (op 1)))
                    (logior (if sets-flags #xeb000000 #xcb000000)
                            (ash (gpr rm) 16)
                            (ash 31 5)  ; Rn = XZR
                            (gpr rd))))
                 ;; ADD/SUB/ADDS/SUBS rd, rn, (:$ imm)  or  rd, rn, rm [shift]
                 (t
                  (let ((rd (op 0))
                        (rn (op 1))
                        (src2 (op 2)))
                    (cond
                      ;; Immediate form
                      ((is-imm src2)
                       (let ((imm (imm-val src2)))
                         (logior (cond ((and is-sub sets-flags) #xf1000000)
                                       (is-sub                  #xd1000000)
                                       (sets-flags              #xb1000000)
                                       (t                       #x91000000))
                                 (ash (logand imm #xfff) 10)
                                 (ash (gpr rn) 5)
                                 (gpr rd))))
                      ;; Register with optional shift: rm or (:lsl rm (:$ amt))
                      ((is-shift src2 :lsl)
                       (let ((rm (cadr src2))
                             (amt (imm-val (caddr src2))))
                         (logior (cond ((and is-sub sets-flags) #xeb000000)
                                       (is-sub                  #xcb000000)
                                       (sets-flags              #xab000000)
                                       (t                       #x8b000000))
                                 (ash (gpr rm) 16)
                                 (ash (logand amt #x3f) 10)
                                 (ash (gpr rn) 5)
                                 (gpr rd))))
                      ;; Plain register
                      (t
                       (logior (cond ((and is-sub sets-flags) #xeb000000)
                                      (is-sub                  #xcb000000)
                                      (sets-flags              #xab000000)
                                      (t                       #x8b000000))
                               (ash (gpr src2) 16)
                               (ash (gpr rn) 5)
                               (gpr rd)))))))))

            ;;=== AND / ORR / EOR / TST / BIC / ORN / MVN / ANDS / BICS ===
            ((or (string-equal name "AND") (string-equal name "ORR")
                 (string-equal name "EOR") (string-equal name "TST")
                 (string-equal name "BIC") (string-equal name "ORN")
                 (string-equal name "MVN") (string-equal name "ANDS")
                 (string-equal name "BICS") (string-equal name "EON"))
             (let* ((is-tst (string-equal name "TST"))
                    (is-mvn (string-equal name "MVN")))
               (cond
                 ;; MVN rd, rm  = ORN rd, xzr, rm
                 (is-mvn
                  (let ((rd (op 0))
                        (rm (op 1)))
                    (logior #xaa200000
                            (ash (gpr rm) 16)
                            (ash 31 5)
                            (gpr rd))))
                 ;; TST rn, (:$ imm) or TST rn, rm
                 (is-tst
                  (let ((rn (op 0))
                        (src (op 1)))
                    (if (is-imm src)
                      ;; TST = ANDS xzr, rn, #imm
                      (let* ((imm (imm-val src))
                             (enc (encode-logical-immediate imm)))
                        (unless enc
                          (error "Cannot encode TST immediate ~s" imm))
                        (logior #xea000000
                                (ash (ldb (byte 1 12) enc) 22)
                                (ash (ldb (byte 6 6) enc) 16)
                                (ash (ldb (byte 6 0) enc) 10)
                                (ash (gpr rn) 5)
                                31))
                      ;; TST rn, rm  = ANDS xzr, rn, rm
                      (logior #xea000000
                              (ash (gpr src) 16)
                              (ash (gpr rn) 5)
                              31))))
                 ;; Regular: AND/ORR/EOR/BIC/ORN/ANDS/BICS/EON rd, rn, src
                 (t
                  (let ((rd (op 0))
                        (rn (op 1))
                        (src2 (op 2)))
                    (if (is-imm src2)
                      ;; Logical immediate
                      (let* ((imm (imm-val src2))
                             (enc (encode-logical-immediate imm))
                             (base (cond ((string-equal name "AND")  #x92000000)
                                         ((string-equal name "ORR")  #xb2000000)
                                         ((string-equal name "EOR")  #xd2000000)
                                         ((string-equal name "ANDS") #xf2000000)
                                         (t (error "~s does not support logical immediate" name)))))
                        (unless enc
                          (error "Cannot encode logical immediate ~s for ~s" imm name))
                        (logior base
                                (ash (ldb (byte 1 12) enc) 22)
                                (ash (ldb (byte 6 6) enc) 16)
                                (ash (ldb (byte 6 0) enc) 10)
                                (ash (gpr rn) 5)
                                (gpr rd)))
                      ;; Logical shifted register
                      (let* ((rm-enc 0)
                             (shift-amt 0)
                             (shift-type 0))  ; 0=LSL, 1=LSR, 2=ASR
                        (cond
                          ((is-shift src2 :lsl)
                           (setq rm-enc (gpr (cadr src2))
                                 shift-amt (imm-val (caddr src2))
                                 shift-type 0))
                          ((is-shift src2 :lsr)
                           (setq rm-enc (gpr (cadr src2))
                                 shift-amt (imm-val (caddr src2))
                                 shift-type 1))
                          ((is-shift src2 :asr)
                           (setq rm-enc (gpr (cadr src2))
                                 shift-amt (imm-val (caddr src2))
                                 shift-type 2))
                          (t
                           (setq rm-enc (gpr src2))))
                        (let ((base (cond ((string-equal name "AND")  #x8a000000)
                                          ((string-equal name "ORR")  #xaa000000)
                                          ((string-equal name "EOR")  #xca000000)
                                          ((string-equal name "BIC")  #x8a200000)
                                          ((string-equal name "ORN")  #xaa200000)
                                          ((string-equal name "EON")  #xca200000)
                                          ((string-equal name "ANDS") #xea000000)
                                          ((string-equal name "BICS") #xea200000)
                                          (t (error "Unknown logical op ~s" name)))))
                          (logior base
                                  (ash shift-type 22)
                                  (ash rm-enc 16)
                                  (ash (logand shift-amt #x3f) 10)
                                  (ash (gpr rn) 5)
                                  (gpr rd))))))))))

            ;;=== MUL / MADD / SMULH / UMULH ===
            ((string-equal name "MUL")
             ;; MUL rd, rn, rm  = MADD rd, rn, rm, xzr
             (logior #x9b007c00
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "MADD")
             ;; MADD rd, rn, rm, ra
             (logior #x9b000000
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 3)) 10)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "MSUB")
             ;; MSUB rd, rn, rm, ra:  rd = ra - rn*rm
             (logior #x9b008000
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 3)) 10)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "MNEG")
             ;; MNEG rd, rn, rm = MSUB rd, rn, rm, xzr
             (logior #x9b00fc00
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "SMULH")
             (logior #x9b407c00
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "UMULH")
             ;; UMULH Xd, Xn, Xm: 1001 1011 110 Rm 0 11111 Rn Rd
             (logior #x9bc07c00
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))

            ;;=== ADC / ADCS / SBC / SBCS (add/subtract with carry) ===
            ((string-equal name "ADC")
             ;; ADC Xd, Xn, Xm: 1 00 11010000 Rm 000000 Rn Rd
             (logior #x9a000000
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "ADCS")
             ;; ADCS Xd, Xn, Xm: 1 01 11010000 Rm 000000 Rn Rd
             (logior #xba000000
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "SBC")
             ;; SBC Xd, Xn, Xm: 1 10 11010000 Rm 000000 Rn Rd
             (logior #xda000000
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "SBCS")
             ;; SBCS Xd, Xn, Xm: 1 11 11010000 Rm 000000 Rn Rd
             (logior #xfa000000
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))

            ;;=== SDIV / UDIV ===
            ((string-equal name "SDIV")
             (logior #x9ac00c00
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "UDIV")
             (logior #x9ac00800
                     (ash (gpr (op 2)) 16)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))

            ;;=== LSL / LSR / ASR (immediate and register) ===
            ((or (string-equal name "LSL") (string-equal name "LSR")
                 (string-equal name "ASR"))
             (let ((rd (op 0))
                   (rn (op 1))
                   (src (op 2)))
               (if (is-imm src)
                 ;; Immediate: alias for UBFM/SBFM
                 (let ((amt (imm-val src)))
                   (cond
                     ((string-equal name "LSL")
                      ;; LSL rd, rn, #amt = UBFM rd, rn, #(64-amt), #(63-amt)
                      (let ((immr (logand (- 64 amt) 63))
                            (imms (- 63 amt)))
                        (logior #xd3400000
                                (ash immr 16)
                                (ash (logand imms #x3f) 10)
                                (ash (gpr rn) 5)
                                (gpr rd))))
                     ((string-equal name "LSR")
                      ;; LSR rd, rn, #amt = UBFM rd, rn, #amt, #63
                      (logior #xd340fc00
                              (ash (logand amt #x3f) 16)
                              (ash (gpr rn) 5)
                              (gpr rd)))
                     ((string-equal name "ASR")
                      ;; ASR rd, rn, #amt = SBFM rd, rn, #amt, #63
                      (logior #x9340fc00
                              (ash (logand amt #x3f) 16)
                              (ash (gpr rn) 5)
                              (gpr rd)))))
                 ;; Register: LSLV/LSRV/ASRV
                 (let ((op2-code (cond ((string-equal name "LSL") #x2000)
                                       ((string-equal name "LSR") #x2400)
                                       (t                         #x2800))))
                   (logior #x9ac00000
                           op2-code
                           (ash (gpr src) 16)
                           (ash (gpr rn) 5)
                           (gpr rd))))))

            ;;=== ROR (rotate right — immediate and register) ===
            ((string-equal name "ROR")
             (let ((rd (op 0))
                   (rn (op 1))
                   (src (op 2)))
               (if (is-imm src)
                 ;; ROR rd, rn, #amt = EXTR rd, rn, rn, #amt
                 (let ((amt (imm-val src)))
                   (logior #x93c00000
                           (ash (gpr rn) 16)
                           (ash (logand amt 63) 10)
                           (ash (gpr rn) 5)
                           (gpr rd)))
                 ;; ROR rd, rn, rm = RORV rd, rn, rm
                 (logior #x9ac02c00
                         (ash (gpr src) 16)
                         (ash (gpr rn) 5)
                         (gpr rd)))))

            ;;=== SXTB / SXTH / SXTW / UXTB / UXTH ===
            ((string-equal name "SXTB")
             ;; SBFM Xd, Xn, #0, #7
             (logior #x93400000
                     (ash 7 10)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "SXTH")
             ;; SBFM Xd, Xn, #0, #15
             (logior #x93400000
                     (ash 15 10)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "SXTW")
             ;; SBFM Xd, Xn, #0, #31
             (logior #x93400000
                     (ash 31 10)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "UXTB")
             ;; UBFM Wd, Wn, #0, #7  (32-bit form)
             (logior #x53000000
                     (ash 7 10)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))
            ((string-equal name "UXTH")
             ;; UBFM Wd, Wn, #0, #15  (32-bit form)
             (logior #x53000000
                     (ash 15 10)
                     (ash (gpr (op 1)) 5)
                     (gpr (op 0))))

            ;;=== LDR / LDUR / LDR (scaled positive offset or register) ===
            ((string-equal name "LDR")
             (arm64-encode-load-store form name ops t 8 #b11))
            ((string-equal name "LDUR")
             (arm64-encode-ldur-stur form name ops t 8 #b11))
            ((string-equal name "STR")
             (arm64-encode-load-store form name ops nil 8 #b11))
            ((string-equal name "STUR")
             (arm64-encode-ldur-stur form name ops nil 8 #b11))
            ((string-equal name "LDRB")
             (arm64-encode-load-store form name ops t 1 #b00))
            ((string-equal name "LDRH")
             (arm64-encode-load-store form name ops t 2 #b01))
            ((string-equal name "LDRSB")
             ;; LDRSB (64-bit) — size=00, opc=10
             (arm64-encode-load-store form name ops t 1 #b00 #b10))
            ((string-equal name "LDRSH")
             ;; LDRSH (64-bit) — size=01, opc=10
             (arm64-encode-load-store form name ops t 2 #b01 #b10))
            ((string-equal name "LDRSW")
             ;; LDRSW — size=10, opc=10
             (arm64-encode-load-store form name ops t 4 #b10 #b10))
            ((string-equal name "STRB")
             (arm64-encode-load-store form name ops nil 1 #b00))
            ((string-equal name "STRH")
             (arm64-encode-load-store form name ops nil 2 #b01))

            ;;=== 32-bit GPR load/store (W-register form) ===
            ;; LDR32: zero-extending 32-bit load (LDR Wt, [addr])
            ;; STR32: 32-bit store (STR Wt, [addr])
            ((string-equal name "LDR32")
             (arm64-encode-load-store form name ops t 4 #b10))
            ((string-equal name "STR32")
             (arm64-encode-load-store form name ops nil 4 #b10))
            ((string-equal name "LDUR32")
             (arm64-encode-ldur-stur form name ops t 4 #b10))
            ((string-equal name "STUR32")
             (arm64-encode-ldur-stur form name ops nil 4 #b10))

            ;;=== LDP / STP ===
            ((or (string-equal name "LDP") (string-equal name "STP"))
             (arm64-encode-ldp-stp form name ops))

            ;;=== CSEL / CSINC / CSINV / CSNEG / CSET ===
            ((string-equal name "CSEL")
             ;; CSEL Xd, Xn, Xm, cond
             (let ((cond-val (encode-cond-keyword (op 3))))
               (logior #x9a800000
                       (ash (gpr (op 2)) 16)
                       (ash cond-val 12)
                       (ash (gpr (op 1)) 5)
                       (gpr (op 0)))))
            ((string-equal name "CSINC")
             (let ((cond-val (encode-cond-keyword (op 3))))
               (logior #x9a800400
                       (ash (gpr (op 2)) 16)
                       (ash cond-val 12)
                       (ash (gpr (op 1)) 5)
                       (gpr (op 0)))))
            ((string-equal name "CSINV")
             (let ((cond-val (encode-cond-keyword (op 3))))
               (logior #xda800000
                       (ash (gpr (op 2)) 16)
                       (ash cond-val 12)
                       (ash (gpr (op 1)) 5)
                       (gpr (op 0)))))
            ((string-equal name "CSNEG")
             (let ((cond-val (encode-cond-keyword (op 3))))
               (logior #xda800400
                       (ash (gpr (op 2)) 16)
                       (ash cond-val 12)
                       (ash (gpr (op 1)) 5)
                       (gpr (op 0)))))
            ((string-equal name "CSET")
             ;; CSET Xd, cond  = CSINC Xd, XZR, XZR, invert(cond)
             (let ((cond-val (logxor (encode-cond-keyword (op 1)) 1)))
               (logior #x9a9f07e0
                       (ash cond-val 12)
                       (gpr (op 0)))))

            ;;=== Floating-point arithmetic ===
            ((string-equal name "FADD")
             (arm64-encode-fp-arith ops #x1e602800))
            ((string-equal name "FSUB")
             (arm64-encode-fp-arith ops #x1e603800))
            ((string-equal name "FMUL")
             (arm64-encode-fp-arith ops #x1e600800))
            ((string-equal name "FDIV")
             (arm64-encode-fp-arith ops #x1e601800))

            ;;=== FP unary ===
            ((string-equal name "FNEG")
             (arm64-encode-fp-unary ops #x1e614000))
            ((string-equal name "FSQRT")
             (arm64-encode-fp-unary ops #x1e61c000))
            ((string-equal name "FABS")
             (arm64-encode-fp-unary ops #x1e60c000))

            ;;=== FCMP ===
            ((string-equal name "FCMP")
             (let ((fn (op 0))
                   (fm (op 1)))
               (cond
                 ;; Both double FP regs
                 ((and (arm64-dfpr-p fn) (arm64-dfpr-p fm))
                  (logior #x1e602000
                          (ash (dfpr fm) 16)
                          (ash (dfpr fn) 5)))
                 ;; Both single FP regs
                 ((and (arm64-sfpr-p fn) (arm64-sfpr-p fm))
                  (logior #x1e202000
                          (ash (sfpr fm) 16)
                          (ash (sfpr fn) 5)))
                 ;; fcmp dn, #0.0
                 ((and (arm64-dfpr-p fn)
                       (or (eql fm 0) (eql fm 0.0d0)))
                  (logior #x1e602008
                          (ash (dfpr fn) 5)))
                 ((and (arm64-sfpr-p fn)
                       (or (eql fm 0) (eql fm 0.0)))
                  (logior #x1e202008
                          (ash (sfpr fn) 5)))
                 (t (error "Invalid FCMP operands: ~s" form)))))

            ;;=== FMOV ===
            ((string-equal name "FMOV")
             (let ((dst (op 0))
                   (src (op 1)))
               (cond
                 ;; fmov dn, dm
                 ((and (arm64-dfpr-p dst) (arm64-dfpr-p src))
                  (logior #x1e604000
                          (ash (dfpr src) 5)
                          (dfpr dst)))
                 ;; fmov sn, sm
                 ((and (arm64-sfpr-p dst) (arm64-sfpr-p src))
                  (logior #x1e204000
                          (ash (sfpr src) 5)
                          (sfpr dst)))
                 ;; fmov dn, xn (gpr→double)
                 ((and (arm64-dfpr-p dst) (arm64-gpr-p src))
                  (logior #x9e670000
                          (ash (gpr src) 5)
                          (dfpr dst)))
                 ;; fmov xn, dn (double→gpr)
                 ((and (arm64-gpr-p dst) (arm64-dfpr-p src))
                  (logior #x9e660000
                          (ash (dfpr src) 5)
                          (gpr dst)))
                 ;; fmov sn, wn (gpr→single, W-reg form)
                 ((and (arm64-sfpr-p dst) (arm64-gpr-p src))
                  (logior #x1e270000
                          (ash (gpr src) 5)
                          (sfpr dst)))
                 ;; fmov wn, sn (single→gpr, W-reg form)
                 ((and (arm64-gpr-p dst) (arm64-sfpr-p src))
                  (logior #x1e260000
                          (ash (sfpr src) 5)
                          (gpr dst)))
                 (t (error "Invalid FMOV operands: ~s" form)))))

            ;;=== SCVTF ===
            ((string-equal name "SCVTF")
             (let ((dst (op 0))
                   (src (op 1)))
               (cond
                 ;; scvtf dn, xn
                 ((and (arm64-dfpr-p dst) (arm64-gpr-p src))
                  (logior #x9e620000
                          (ash (gpr src) 5)
                          (dfpr dst)))
                 ;; scvtf sn, xn  (using 64-bit source)
                 ((and (arm64-sfpr-p dst) (arm64-gpr-p src))
                  (logior #x9e220000
                          (ash (gpr src) 5)
                          (sfpr dst)))
                 (t (error "Invalid SCVTF operands: ~s" form)))))

            ;;=== FCVTZS ===
            ((string-equal name "FCVTZS")
             (let ((dst (op 0))
                   (src (op 1)))
               (cond
                 ;; fcvtzs xn, dn
                 ((and (arm64-gpr-p dst) (arm64-dfpr-p src))
                  (logior #x9e780000
                          (ash (dfpr src) 5)
                          (gpr dst)))
                 ;; fcvtzs xn, sn
                 ((and (arm64-gpr-p dst) (arm64-sfpr-p src))
                  (logior #x9e380000
                          (ash (sfpr src) 5)
                          (gpr dst)))
                 (t (error "Invalid FCVTZS operands: ~s" form)))))

            ;;=== FCVT (between float precisions) ===
            ((string-equal name "FCVT")
             (let ((dst (op 0))
                   (src (op 1)))
               (cond
                 ;; fcvt dn, sn (single→double)
                 ((and (arm64-dfpr-p dst) (arm64-sfpr-p src))
                  (logior #x1e22c000
                          (ash (sfpr src) 5)
                          (dfpr dst)))
                 ;; fcvt sn, dn (double→single)
                 ((and (arm64-sfpr-p dst) (arm64-dfpr-p src))
                  (logior #x1e624000
                          (ash (dfpr src) 5)
                          (sfpr dst)))
                 (t (error "Invalid FCVT operands: ~s" form)))))

            ;;=== UUO pseudo-instructions ===
            ;; These encode as HLT with structured 16-bit immediates.
            ;; Format: imm16 = [info:8 | reg:5 | format:3]
            ;; Nullary (format=0): (uuo-error-wrong-nargs)
            ((string-equal name "UUO-ERROR-WRONG-NARGS")
             ;; Nullary UUO, subcode 1 = wrong nargs
             (logior #xd4400000 (ash (logior 0 (ash 1 3)) 5)))

            ;; Unary register UUOs: (uuo-error-reg-not-lisptag reg (:$ tag))
            ((string-equal name "UUO-ERROR-REG-NOT-LISPTAG")
             (let ((reg (gpr (op 0)))
                   (tag (imm-val (op 1))))
               (logior #xd4400000
                       (ash (logior 1 (ash reg 3) (ash tag 8)) 5))))

            ((string-equal name "UUO-ERROR-REG-NOT-FULLTAG")
             (let ((reg (gpr (op 0)))
                   (tag (imm-val (op 1))))
               (logior #xd4400000
                       (ash (logior 2 (ash reg 3) (ash tag 8)) 5))))

            ((string-equal name "UUO-ERROR-REG-NOT-SUBTAG")
             (let ((reg (gpr (op 0)))
                   (tag (imm-val (op 1))))
               (logior #xd4400000
                       (ash (logior 3 (ash reg 3) (ash tag 8)) 5))))

            ((string-equal name "UUO-ERROR-REG-NOT-XTYPE")
             (let ((reg (gpr (op 0)))
                   (tag (imm-val (op 1))))
               (logior #xd4400000
                       (ash (logior 4 (ash reg 3) (ash tag 8)) 5))))

            ;; Unary misc UUOs: (uuo-error-unbound reg)
            ((string-equal name "UUO-ERROR-UNBOUND")
             (let ((reg (gpr (op 0))))
               (logior #xd4400000
                       (ash (logior 5 (ash reg 3) (ash 3 8)) 5))))

            ((string-equal name "UUO-ERROR-NOT-CALLABLE")
             (let ((reg (gpr (op 0))))
               (logior #xd4400000
                       (ash (logior 5 (ash reg 3) (ash 0 8)) 5))))

            ((string-equal name "UUO-ERROR-UDF")
             (let ((reg (gpr (op 0))))
               (logior #xd4400000
                       (ash (logior 5 (ash reg 3) (ash 0 8)) 5))))

            ;; Binary UUOs: (uuo-error-vector-bounds idx vec)
            ((string-equal name "UUO-ERROR-VECTOR-BOUNDS")
             (let ((idx (gpr (op 0)))
                   (vec (gpr (op 1))))
               (logior #xd4400000
                       (ash (logior 6 (ash idx 3) (ash vec 8) (ash 0 13)) 5))))

            ;; Array axis bounds: (uuo-error-array-axis-bounds idx limit header)
            ;; Uses binary format with idx and limit as regs; header reg ignored
            ;; (runtime reads it from the preceding instruction context).
            ((string-equal name "UUO-ERROR-ARRAY-AXIS-BOUNDS")
             (let ((idx (gpr (op 0)))
                   (limit (gpr (op 1))))
               (logior #xd4400000
                       (ash (logior 6 (ash idx 3) (ash limit 8) (ash 0 13)) 5))))

            ;; Slot-unbound error: (uuo-error-slot-unbound dest instance index)
            ;; Encode as binary UUO with instance and index regs.
            ((string-equal name "UUO-ERROR-SLOT-UNBOUND")
             (let ((instance (gpr (op 1)))
                   (index (gpr (op 2))))
               (logior #xd4400000
                       (ash (logior 6 (ash instance 3) (ash index 8) (ash 1 13)) 5))))

            ;; uuo-tlb-too-small reg — TLB needs to grow
            ((string-equal name "UUO-TLB-TOO-SMALL")
             (let ((reg (gpr (op 0))))
               (logior #xd4400000
                       (ash (logior 5 (ash reg 3) (ash 2 8)) 5))))

            ;; Continuable unary UUOs: same encoding as non-continuable.
            ;; The distinction is handled by the exception system based on
            ;; whether the error can be restarted with a new value.
            ((string-equal name "UUO-CERROR-REG-NOT-XTYPE")
             (let ((reg (gpr (op 0)))
                   (tag (imm-val (op 1))))
               (logior #xd4400000
                       (ash (logior 4 (ash reg 3) (ash tag 8)) 5))))

            ;;=== MRS: read system register ===
            ;; (mrs Rd (:$ sysreg-encoding))
            ;; sysreg is 15-bit: op0[1]:op1[3]:CRn[4]:CRm[4]:op2[3]
            ((string-equal name "MRS")
             (let ((rd (gpr (op 0)))
                   (sysreg (imm-val (op 1))))
               (logior #xD5300000 (ash (logand sysreg #x7FFF) 5) rd)))

            ;;=== MSR: write system register ===
            ;; (msr (:$ sysreg-encoding) Rn)
            ((string-equal name "MSR")
             (let ((sysreg (imm-val (op 0)))
                   (rn (gpr (op 1))))
               (logior #xD5100000 (ash (logand sysreg #x7FFF) 5) rn)))

            (t
             (error "Unknown ARM64 instruction: ~s" form))))))))



;;; ---- Load/store encoding helpers ----

(defun arm64-encode-load-store (form name ops is-load scale size-bits
                                &optional (opc-override nil))
  "Encode LDR/STR family with (:@ base (:$ off)) or (:@ base index) addressing."
  (declare (ignore name))
  (let* ((rt-raw (first ops))
         (addr (second ops))
         (is-fpr (arm64-fpr-p rt-raw))
         (dest (if is-fpr (need-arm64-fpr-encoding rt-raw) (need-arm64-gpr-encoding rt-raw)))
         (opc (or opc-override (if is-load (if is-fpr #b01 #b01) #b00))))
    ;; Determine addressing mode
    (cond
      ;; (:@ base (:$ offset)) — unsigned offset
      ((and (consp addr) (eq (car addr) :@)
            (consp (caddr addr)) (eq (car (caddr addr)) :$))
       (let* ((base (need-arm64-gpr-encoding (cadr addr)))
              (offset (cadr (caddr addr)))
              (v-bit (if is-fpr 1 0)))
         ;; Unsigned offset: try scaled form first
         (if (and (>= offset 0) (zerop (mod offset scale)))
           (let ((scaled-off (truncate offset scale)))
             (if (<= scaled-off #xfff)
               ;; LDR (unsigned offset): size[31:30] 11 V[26] 01 imm12[21:10] Rn[9:5] Rt[4:0]
               (logior (ash size-bits 30)
                       #x39000000
                       (ash v-bit 26)
                       (ash opc 22)
                       (ash (logand scaled-off #xfff) 10)
                       (ash base 5)
                       dest)
               ;; Offset too large for unsigned: use unscaled
               (arm64-encode-unscaled-offset size-bits v-bit opc base offset dest)))
           ;; Not naturally aligned or negative: use unscaled (LDUR/STUR form)
           (arm64-encode-unscaled-offset size-bits v-bit opc base offset dest))))
      ;; (:@ base index) — register offset (no shift, no extend)
      ((and (consp addr) (eq (car addr) :@)
            (not (consp (caddr addr))))
       (let* ((base (need-arm64-gpr-encoding (cadr addr)))
              (index (need-arm64-gpr-encoding (caddr addr)))
              (v-bit (if is-fpr 1 0)))
         ;; Register offset: size 11 V opc 1 Rm option(011=LSL) S(0) 10 Rn Rt
         (logior (ash size-bits 30)
                 #x38200800
                 (ash v-bit 26)
                 (ash opc 22)
                 (ash index 16)
                 (ash #b011 13)  ; option = LSL
                 (ash base 5)
                 dest)))
      ;; (:@! base (:$ offset)) — pre-index
      ((and (consp addr) (eq (car addr) :@!)
            (consp (caddr addr)) (eq (car (caddr addr)) :$))
       (let* ((base (need-arm64-gpr-encoding (cadr addr)))
              (offset (cadr (caddr addr)))
              (v-bit (if is-fpr 1 0)))
         (arm64-encode-pre-post-index size-bits v-bit opc base offset dest #b11)))
      ;; (:@+ base (:$ offset)) — post-index
      ((and (consp addr) (eq (car addr) :@+)
            (consp (caddr addr)) (eq (car (caddr addr)) :$))
       (let* ((base (need-arm64-gpr-encoding (cadr addr)))
              (offset (cadr (caddr addr)))
              (v-bit (if is-fpr 1 0)))
         (arm64-encode-pre-post-index size-bits v-bit opc base offset dest #b01)))
      (t (error "Unsupported addressing mode in ~s" form)))))

(defun arm64-encode-ldur-stur (form name ops is-load scale size-bits)
  "Encode LDUR/STUR — always unscaled offset."
  (declare (ignore name scale))
  (let* ((rt-raw (first ops))
         (addr (second ops))
         (is-fpr (arm64-fpr-p rt-raw))
         (dest (if is-fpr (need-arm64-fpr-encoding rt-raw) (need-arm64-gpr-encoding rt-raw)))
         (opc (if is-load (if is-fpr #b01 #b01) #b00))
         (v-bit (if is-fpr 1 0)))
    (cond
      ((and (consp addr) (eq (car addr) :@)
            (consp (caddr addr)) (eq (car (caddr addr)) :$))
       (let* ((base (need-arm64-gpr-encoding (cadr addr)))
              (offset (cadr (caddr addr))))
         (arm64-encode-unscaled-offset size-bits v-bit opc base offset dest)))
      (t (error "Unsupported addressing mode for LDUR/STUR: ~s" form)))))

(defun arm64-encode-unscaled-offset (size-bits v-bit opc base offset dest)
  "LDUR/STUR encoding: size 11 V opc 0 imm9 00 Rn Rt"
  (logior (ash size-bits 30)
          #x38000000
          (ash v-bit 26)
          (ash opc 22)
          (ash (logand offset #x1ff) 12)
          (ash base 5)
          dest))

(defun arm64-encode-pre-post-index (size-bits v-bit opc base offset dest mode)
  "Pre/post-index encoding: size 11 V opc 0 imm9 mode Rn Rt
   mode: 11=pre-index, 01=post-index"
  (logior (ash size-bits 30)
          #x38000000
          (ash v-bit 26)
          (ash opc 22)
          (ash (logand offset #x1ff) 12)
          (ash mode 10)
          (ash base 5)
          dest))

;;; ---- LDP / STP ----

(defun arm64-encode-ldp-stp (form name ops)
  "Encode LDP/STP with signed offset, pre-index, or post-index."
  (let* ((is-load (string-equal name "LDP"))
         (rt1-raw (first ops))
         (rt2-raw (second ops))
         (addr (third ops))
         (is-fpr (arm64-fpr-p rt1-raw)))
    ;; rt2 can be (:+ rt1 1) meaning consecutive register
    (let* ((rt1 (if is-fpr (need-arm64-fpr-encoding rt1-raw) (need-arm64-gpr-encoding rt1-raw)))
           (rt2 (cond
                  ((and (consp rt2-raw) (eq (car rt2-raw) :+))
                   ;; (:+ reg 1) → reg+1
                   (let ((base-reg (if is-fpr
                                     (need-arm64-fpr-encoding (cadr rt2-raw))
                                     (need-arm64-gpr-encoding (cadr rt2-raw)))))
                     (+ base-reg (caddr rt2-raw))))
                  (t (if is-fpr
                       (need-arm64-fpr-encoding rt2-raw)
                       (need-arm64-gpr-encoding rt2-raw)))))
           (scale (if is-fpr 8 8))  ; 64-bit for both GPR and FPR
           (opc-bits (if is-fpr #b01 #b10))  ; 01=FP 64-bit, 10=GPR 64-bit
           (l-bit (if is-load 1 0))
           (v-bit (if is-fpr 1 0)))
      (cond
        ;; (:@ base (:$ offset)) — signed offset
        ((and (consp addr) (eq (car addr) :@)
              (consp (caddr addr)) (eq (car (caddr addr)) :$))
         (let* ((base (need-arm64-gpr-encoding (cadr addr)))
                (offset (cadr (caddr addr)))
                (imm7 (truncate offset scale)))
           (logior (ash opc-bits 30)
                   #x29000000
                   (ash v-bit 26)
                   (ash l-bit 22)
                   (ash (logand imm7 #x7f) 15)
                   (ash rt2 10)
                   (ash base 5)
                   rt1)))
        ;; (:@! base (:$ offset)) — pre-index
        ((and (consp addr) (eq (car addr) :@!)
              (consp (caddr addr)) (eq (car (caddr addr)) :$))
         (let* ((base (need-arm64-gpr-encoding (cadr addr)))
                (offset (cadr (caddr addr)))
                (imm7 (truncate offset scale)))
           (logior (ash opc-bits 30)
                   #x29800000
                   (ash v-bit 26)
                   (ash l-bit 22)
                   (ash (logand imm7 #x7f) 15)
                   (ash rt2 10)
                   (ash base 5)
                   rt1)))
        ;; (:@+ base (:$ offset)) — post-index
        ((and (consp addr) (eq (car addr) :@+)
              (consp (caddr addr)) (eq (car (caddr addr)) :$))
         (let* ((base (need-arm64-gpr-encoding (cadr addr)))
                (offset (cadr (caddr addr)))
                (imm7 (truncate offset scale)))
           (logior (ash opc-bits 30)
                   #x28800000
                   (ash v-bit 26)
                   (ash l-bit 22)
                   (ash (logand imm7 #x7f) 15)
                   (ash rt2 10)
                   (ash base 5)
                   rt1)))
        (t (error "Unsupported LDP/STP addressing: ~s" form))))))


;;; ---- FP arithmetic helpers ----

(defun arm64-encode-fp-arith (ops base-opcode)
  "Encode 2-source FP arithmetic: FADD, FSUB, FMUL, FDIV.
   base-opcode is for double precision; single = base with bit 22 cleared."
  (let ((rd (first ops))
        (rn (second ops))
        (rm (third ops)))
    (cond
      ((and (arm64-dfpr-p rd) (arm64-dfpr-p rn) (arm64-dfpr-p rm))
       (logior base-opcode
               (ash (need-arm64-dfpr-encoding rm) 16)
               (ash (need-arm64-dfpr-encoding rn) 5)
               (need-arm64-dfpr-encoding rd)))
      ((and (arm64-sfpr-p rd) (arm64-sfpr-p rn) (arm64-sfpr-p rm))
       ;; Single precision: clear bit 22 (type field)
       (logior (logand base-opcode (lognot (ash 1 22)))
               (ash (need-arm64-sfpr-encoding rm) 16)
               (ash (need-arm64-sfpr-encoding rn) 5)
               (need-arm64-sfpr-encoding rd)))
      (t (error "Mismatched FP register types in ~s" ops)))))

(defun arm64-encode-fp-unary (ops base-opcode)
  "Encode 1-source FP: FNEG, FSQRT, FABS."
  (let ((rd (first ops))
        (rn (second ops)))
    (cond
      ((and (arm64-dfpr-p rd) (arm64-dfpr-p rn))
       (logior base-opcode
               (ash (need-arm64-dfpr-encoding rn) 5)
               (need-arm64-dfpr-encoding rd)))
      ((and (arm64-sfpr-p rd) (arm64-sfpr-p rn))
       (logior (logand base-opcode (lognot (ash 1 22)))
               (ash (need-arm64-sfpr-encoding rn) 5)
               (need-arm64-sfpr-encoding rd)))
      (t (error "Mismatched FP register types in ~s" ops)))))


;;; ---- Label reference extraction ----

(defun arm64-extract-branch-info (source)
  "Given a resolved instruction S-expression, return (values label ref-type)
   if it references a label, or (values nil nil) otherwise.
   ref-type is :b, :b-cond, :cbz, :cbnz, or :adr."
  (when (null source)
    (return-from arm64-extract-branch-info (values nil nil)))
  (let* ((mnemonic (car source))
         (ops (cdr source))
         (name (string mnemonic)))
    ;; Check for b.eq, b.ne, etc.
    (multiple-value-bind (base-mnem cond-code)
        (parse-mnemonic-condition mnemonic)
      (declare (ignore cond-code))
      (when (and base-mnem (string-equal base-mnem "B"))
        (return-from arm64-extract-branch-info
          (values (first ops) :b-cond))))
    (cond
      ((string-equal name "B")
       (if (and (consp (first ops))
                (or (eq (car (first ops)) :?)
                    (eq (car (first ops)) :~)))
         ;; (b (:? cond) label)
         (values (second ops) :b-cond)
         ;; (b label)
         (values (first ops) :b)))
      ((string-equal name "BL")
       (values (first ops) :b))
      ((string-equal name "CBZ")
       (values (second ops) :cbz))
      ((string-equal name "CBNZ")
       (values (second ops) :cbnz))
      ((string-equal name "ADR")
       (values (second ops) :adr))
      (t (values nil nil)))))


;;; ---- Resolve a branch offset into an opcode ----

(defun arm64-patch-branch-opcode (opcode ref-type diff-words diff-bytes)
  "Patch branch offset into OPCODE.  DIFF-WORDS = (label - insn) / 4."
  (case ref-type
    ;; Unconditional branch: imm26 at bits [25:0]
    (:b (logior (logand opcode #xfc000000)
                (logand diff-words #x3ffffff)))
    ;; Conditional branch: imm19 at bits [23:5]
    (:b-cond (logior (logand opcode #xff00001f)
                     (ash (logand diff-words #x7ffff) 5)))
    ;; CBZ/CBNZ: imm19 at bits [23:5]
    ((:cbz :cbnz)
     (logior (logand opcode #xff00001f)
             (ash (logand diff-words #x7ffff) 5)))
    ;; ADR: immhi at bits [23:5], immlo at bits [30:29]
    (:adr
     (logior (logand opcode #x9f00001f)
             (ash (logand (ash diff-bytes -2) #x7ffff) 5)
             (ash (logand diff-bytes #x3) 29)))
    (t (error "Unknown label ref type ~s" ref-type))))


;;; ---- arm64-finalize ----

(defun arm64-finalize (seg)
  "Encode all instructions in SEG, resolve labels.
   Returns the number of 32-bit words."
  (let* ((branch-refs nil))
    ;; Pass 1: encode all instructions, collecting branch label references
    (ccl::do-dll-nodes (element seg)
      (when (typep element 'lap-instruction)
        (let* ((source (lap-instruction-source element)))
          (when source
            (multiple-value-bind (opcode ref-type)
                (arm64-encode-instruction source)
              (setf (lap-instruction-opcode element) opcode)
              ;; Extract label reference from source s-expression
              (multiple-value-bind (label-name branch-type)
                  (arm64-extract-branch-info source)
                (declare (ignore branch-type))
                (when (and ref-type label-name)
                  (push (list element label-name ref-type) branch-refs))))))))

    ;; Pass 2: dead branch elimination — remove unconditional branches to
    ;; the immediately following label
    (let ((removed nil))
      (setq branch-refs
            (delete-if
             (lambda (ref)
               (destructuring-bind (insn label-name ref-type) ref
                 (when (eq ref-type :b)
                   (let* ((lab (find-lap-label label-name)))
                     (when (and lab
                                (lap-label-emitted-p lab)
                                (eql (lap-label-address lab)
                                     (+ (instruction-element-address insn) 4)))
                       (ccl::remove-dll-node insn)
                       (setq removed t)
                       t)))))
             branch-refs))
      (when removed
        (set-element-addresses 0 seg)))

    ;; Pass 3: resolve branch label references
    ;; ARM64 branch offsets are (label-addr - insn-addr) / 4, no PC+8 adjustment
    (dolist (ref branch-refs)
      (destructuring-bind (insn label-name ref-type) ref
        (let* ((lab (find-lap-label label-name)))
          (unless lab
            (error "Undefined label ~s" label-name))
          (when (lap-label-emitted-p lab)
            (let* ((labaddr (lap-label-address lab))
                   (insn-addr (instruction-element-address insn))
                   (diff-bytes (- labaddr insn-addr))
                   (diff-words (ash diff-bytes -2)))
              (setf (lap-instruction-opcode insn)
                    (arm64-patch-branch-opcode
                     (lap-instruction-opcode insn)
                     ref-type diff-words diff-bytes)))))))

    ;; Also resolve any label refs registered via lap-note-label-reference
    ;; (used by arm64-lap.lisp assemble-instruction path)
    (do-lap-labels (lab)
      (if (lap-label-emitted-p lab)
        (let* ((labaddr (lap-label-address lab)))
          (dolist (ref (lap-label-refs lab))
            (destructuring-bind (insn . reftype) ref
              (let* ((insn-addr (instruction-element-address insn))
                     (diff-bytes (- labaddr insn-addr))
                     (diff-words (ash diff-bytes -2)))
                (setf (lap-instruction-opcode insn)
                      (arm64-patch-branch-opcode
                       (lap-instruction-opcode insn)
                       reftype diff-words diff-bytes))))))
        (when (lap-label-refs lab)
          (error "LAP label ~s was referenced but not defined."
                 (lap-label-name lab)))))

    ;; Return number of 32-bit instruction words
    (ash (section-size seg) -2)))


(provide "ARM64-ASM")
