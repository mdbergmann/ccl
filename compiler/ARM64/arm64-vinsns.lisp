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

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require "VINSN")
  (require "ARM64-BACKEND"))

(eval-when (:compile-toplevel :execute)
  (require "ARM64ENV"))

(defmacro define-arm64-vinsn (vinsn-name (results args &optional temps) &body body)
  (%define-arm64-vinsn *arm64-backend* vinsn-name results args temps body))


(define-arm64-vinsn data-section (()
                                  ())
  (:data))

(define-arm64-vinsn code-section (()
                                  ())
  (:code))


;;; ======================================================================
;;; Chunk 2: Frame management
;;; ARM64 lisp-frame is 2 slots: savevsp(0) + savelr(8) = 16 bytes.
;;; No frame marker, no fn save (unlike ARM32's 4-slot frame).
;;; ======================================================================

;;; Save lisp context when VSP is current (no extra values pushed).
;;; ARM64: save vsp, lr, and nfn (fn=nfn on ARM64, must be preserved across calls).
;;; Frame is 32 bytes: [sp+0]=vsp, [sp+8]=lr, [sp+16]=nfn, [sp+24]=fp(x29).
(define-arm64-vinsn save-lisp-context-vsp (()
                                           ())
  (stp vsp lr (:@! sp (:$ (- arm64::lisp-frame.size))))
  (stp nfn x29 (:@ sp (:$ arm64::lisp-frame.savefn)))
  (add x29 sp (:$ 0)))

;;; Save lisp context when some number of bytes have been vpushed
;;; beyond what the compiler expects.
(define-arm64-vinsn save-lisp-context-offset (()
                                              ((nbytes-vpushed :u16const))
                                              ((imm (:u64 #.arm64::imm1))))
  (add imm vsp (:$ nbytes-vpushed))
  (stp imm lr (:@! sp (:$ (- arm64::lisp-frame.size))))
  (stp nfn x29 (:@ sp (:$ arm64::lisp-frame.savefn)))
  (add x29 sp (:$ 0)))

;;; Save lisp context with variable number of args already vpushed.
;;; Compute the effective vsp: vsp + max(0, nargs - #arg-regs) * node-size.
;;; But nargs already counts in units of node-size (nargs = n * 8), and
;;; fixnumshift=0, so nargs is already the byte count.
(define-arm64-vinsn save-lisp-context-variable (()
                                                ()
                                                ((imm (:u64 #.arm64::imm1))))
  (subs imm nargs (:$ (:apply ash $numarm64argregs arm64::word-shift)))
  (b.gt :have-extra)
  (mov imm (:$ 0))
  :have-extra
  (add imm imm vsp)
  (stp imm lr (:@! sp (:$ (- arm64::lisp-frame.size))))
  (stp nfn x29 (:@ sp (:$ arm64::lisp-frame.savefn)))
  (add x29 sp (:$ 0)))

;;; Save cleanup (unwind-protect) context.
;;; Store 0 for savevsp to mark this as a cleanup frame.
(define-arm64-vinsn save-cleanup-context (()
                                          ()
                                          ((temp (:u64 #.arm64::imm0))))
  (mov temp (:$ 0))
  (stp temp lr (:@! sp (:$ (- arm64::lisp-frame.size))))
  (stp nfn x29 (:@ sp (:$ arm64::lisp-frame.savefn)))
  (add x29 sp (:$ 0)))

;;; Save NFP (non-volatile FPR pointer).
;;; On ARM64 with no GPR NVRs, this is essentially a no-op placeholder.
;;; When NFP is actually used (for unboxed float temps), this would save
;;; the native frame pointer. For now, it does nothing.
(define-arm64-vinsn (save-nfp :predicatable) (()())
  )

;;; Restore NFP.  Like save-nfp, a placeholder for now.
(define-arm64-vinsn (restore-nfp :predicatable) (()())
  )

;;; Restore full lisp context (load vsp, lr, and nfn from frame, pop frame).
(define-arm64-vinsn (restore-full-lisp-context :lispcontext :pop :lrRestore :predicatable)
    (()
     ())
  (ldp nfn x29 (:@ sp (:$ arm64::lisp-frame.savefn)))
  (ldp vsp lr (:@+ sp (:$ arm64::lisp-frame.size))))

;;; Return from function: restore context and return.
(define-arm64-vinsn (popj :lispcontext :pop :lrRestore :jumpLR :predicatable)
    (()
     ())
  (ldp nfn x29 (:@ sp (:$ arm64::lisp-frame.savefn)))
  (ldp vsp lr (:@+ sp (:$ arm64::lisp-frame.size)))
  (ret))

;;; Jump via link register (return without restoring context).
(define-arm64-vinsn (jump-return-pc :jumpLR :predicatable)
    (()
     ())
  (ret))

;;; Restore cleanup context: just restore lr and nfn, deallocate the frame.
(define-arm64-vinsn restore-cleanup-context (()
                                             ())
  (ldp nfn x29 (:@ sp (:$ arm64::lisp-frame.savefn)))
  (ldr lr (:@ sp (:$ arm64::lisp-frame.savelr)))
  (add sp sp (:$ arm64::lisp-frame.size)))

;;; Reload nfn from the lisp frame after a non-tail call.
;;; ARM64-specific: fn=nfn=x10 is clobbered by calls; must reload.
(define-arm64-vinsn (reload-self :predicatable) (()())
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))


;;; ======================================================================
;;; Chunk 3: Index scaling and node/64-bit misc ref/set
;;; ARM64 key difference: fixnumshift=0, so a fixnum index IS the element
;;; number (not pre-shifted).  Need explicit scaling to get byte offsets.
;;; misc-data-offset=0, so no bias needed after scaling.
;;; ======================================================================

;;; Scale a fixnum index to a byte offset for node-sized (8-byte) elements.
;;; ARM32: fixnumshift=2=word-shift, so idx was already a byte offset.
;;; ARM64: fixnumshift=0, word-shift=3, so byte_offset = idx << 3.
(define-arm64-vinsn (scale-node-misc-index :predicatable)
    (((dest :u64))
     ((idx :imm))
     ())
  (lsl dest idx (:$ arm64::word-shift)))

;;; 64-bit elements (same size as node).
(define-arm64-vinsn (scale-64bit-misc-index :predicatable)
    (((dest :u64))
     ((idx :imm))
     ())
  (lsl dest idx (:$ arm64::word-shift)))

;;; 32-bit elements: byte_offset = idx << 2.
(define-arm64-vinsn (scale-32bit-misc-index :predicatable)
    (((dest :u64))
     ((idx :imm))
     ())
  (lsl dest idx (:$ 2)))

;;; 16-bit elements: byte_offset = idx << 1.
(define-arm64-vinsn (scale-16bit-misc-index :predicatable)
    (((dest :u64))
     ((idx :imm))
     ())
  (lsl dest idx (:$ 1)))

;;; 8-bit elements: byte_offset = idx (fixnumshift=0, element size=1).
(define-arm64-vinsn (scale-8bit-misc-index :predicatable)
    (((dest :u64))
     ((idx :imm))
     ())
  (mov dest idx))

;;; 1-bit elements: compute word byte-offset and bit number within word.
;;; 64 bits per word on ARM64 (vs 32 on ARM32).
(define-arm64-vinsn (scale-1bit-misc-index :predicatable)
    (((word-index :u64)
      (bitnum :u8))
     ((idx :imm))
     ())
  (and bitnum idx (:$ 63))
  (lsr word-index idx (:$ 6))
  (lsl word-index word-index (:$ arm64::word-shift)))


;;; Node (tagged Lisp object) misc ref/set.

(define-arm64-vinsn (misc-ref-node :predicatable)
    (((dest :lisp))
     ((v :lisp)
      (scaled-idx :s64))
     ())
  (ldr dest (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-c-node :predicatable)
    (((dest :lisp))
     ((v :lisp)
      (idx :s16const))
     ())
  (ldr dest (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx arm64::word-shift))))))

(define-arm64-vinsn (misc-set-node :predicatable)
    (()
     ((val :lisp)
      (v :lisp)
      (scaled-idx :u64)))
  (str val (:@ v scaled-idx)))

;;; For initialization only (val known older than v).
(define-arm64-vinsn (misc-set-c-node :predicatable)
    (()
     ((val :lisp)
      (v :lisp)
      (idx :s16const))
     ())
  (str val (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx arm64::word-shift))))))


;;; 64-bit unsigned misc ref/set (natural word size on ARM64).

(define-arm64-vinsn (misc-ref-u64 :predicatable)
    (((dest :u64))
     ((v :lisp)
      (scaled-idx :u64))
     ())
  (ldr dest (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-c-u64 :predicatable)
    (((dest :u64))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldr dest (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 3))))))

(define-arm64-vinsn (misc-ref-s64 :predicatable)
    (((dest :s64))
     ((v :lisp)
      (scaled-idx :u64))
     ())
  (ldr dest (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-c-s64 :predicatable)
    (((dest :s64))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldr dest (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 3))))))

(define-arm64-vinsn (misc-set-u64 :predicatable)
    (()
     ((val :u64)
      (v :lisp)
      (scaled-idx :u64)))
  (str val (:@ v scaled-idx)))

(define-arm64-vinsn (misc-set-c-u64 :predicatable)
    (()
     ((val :u64)
      (v :lisp)
      (idx :u32const)))
  (str val (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 3))))))

(define-arm64-vinsn (misc-set-s64 :predicatable)
    (()
     ((val :s64)
      (v :lisp)
      (scaled-idx :u64)))
  (str val (:@ v scaled-idx)))

(define-arm64-vinsn (misc-set-c-s64 :predicatable)
    (()
     ((val :s64)
      (v :lisp)
      (idx :u32const)))
  (str val (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 3))))))


;;; Element count and bounds checking.

;;; Extract the element count from a vector header as a fixnum.
;;; Header layout: bits 0-7 = subtag, bits 8-63 = element count.
;;; Since fixnumshift=0, the count IS the fixnum value.
(define-arm64-vinsn (misc-element-count-fixnum :predicatable)
    (((dest :imm))
     ((v :lisp))
     ((temp :u64)))
  (ldur temp (:@ v (:$ arm64::misc-header-offset)))
  (ubfx dest temp (:$ 0) (:$ arm64::subtag-shift)))

;;; Trap if fixnum index >= element count.
(define-arm64-vinsn check-misc-bound (()
                                      ((idx :imm)
                                       (v :lisp))
                                      ((temp :u64)))
  (ldur temp (:@ v (:$ arm64::misc-header-offset)))
  (ubfx temp temp (:$ 0) (:$ arm64::subtag-shift))
  (cmp idx temp)
  (b.lo :ok)
  (uuo-error-vector-bounds idx v)
  :ok)


;;; Multi-dimensional array index helpers.

;;; 2D unscaled index: dest = i * dim1 + j
(define-arm64-vinsn (2d-unscaled-index :predicatable)
    (((dest :imm)
      (dim1 :u64))
     ((dim1 :u64)
      (i :imm)
      (j :imm)))
  (madd dest i dim1 j))

;;; 3D unscaled index: dest = i * dim1 * dim2 + j * dim2 + k
(define-arm64-vinsn (3d-unscaled-index :predicatable)
    (((dest :imm)
      (dim1 :u64)
      (dim2 :u64))
     ((dim1 :u64)
      (dim2 :u64)
      (i :imm)
      (j :imm)
      (k :imm)))
  (mul dim1 dim1 dim2)
  (madd dim2 j dim2 k)
  (madd dest dim1 i dim2))

;;; Extract dim1 (unboxed) from a 2D array header.
;;; On ARM64 fixnumshift=0, so the stored fixnum IS the value (no shift needed).
(define-arm64-vinsn (2d-dim1 :predicatable)
    (((dest :u64))
     ((header :lisp)))
  (ldr dest (:@ header (:$ (:apply + arm64::misc-data-offset
                                    (:apply ash (:apply 1+ arm64::arrayH.dim0-cell)
                                            arm64::word-shift))))))

;;; Extract dim1 and dim2 (unboxed) from a 3D array header.
(define-arm64-vinsn (3d-dims :predicatable)
    (((dim1 :u64)
      (dim2 :u64))
     ((header :lisp)))
  (ldr dim1 (:@ header (:$ (:apply + arm64::misc-data-offset
                                    (:apply ash (:apply 1+ arm64::arrayH.dim0-cell)
                                            arm64::word-shift)))))
  (ldr dim2 (:@ header (:$ (:apply + arm64::misc-data-offset
                                    (:apply ash (:apply + 2 arm64::arrayH.dim0-cell)
                                            arm64::word-shift))))))

;;; Check 2D array bounds; return dim1 (unboxed) for index computation.
(define-arm64-vinsn check-2d-bound (((dim :u64))
                                    ((i :imm)
                                     (j :imm)
                                     (header :lisp)))
  (ldr dim (:@ header (:$ (:apply + arm64::misc-data-offset
                                   (:apply ash arm64::arrayH.dim0-cell
                                           arm64::word-shift)))))
  (cmp i dim)
  (b.lo :ok1)
  (mov dim (:$ 0))
  (uuo-error-array-axis-bounds i dim header)
  :ok1
  (ldr dim (:@ header (:$ (:apply + arm64::misc-data-offset
                                   (:apply ash (:apply 1+ arm64::arrayH.dim0-cell)
                                           arm64::word-shift)))))
  (cmp j dim)
  (b.lo :ok2)
  (mov dim (:$ arm64::fixnumone))
  (uuo-error-array-axis-bounds j dim header)
  :ok2)

;;; Check 3D array bounds; return dim1 and dim2 (unboxed).
(define-arm64-vinsn check-3d-bound (((dim1 :u64)
                                     (dim2 :u64))
                                    ((i :imm)
                                     (j :imm)
                                     (k :imm)
                                     (header :lisp)))
  (ldr dim1 (:@ header (:$ (:apply + arm64::misc-data-offset
                                    (:apply ash arm64::arrayH.dim0-cell
                                            arm64::word-shift)))))
  (cmp i dim1)
  (b.lo :ok1)
  (mov dim1 (:$ 0))
  (uuo-error-array-axis-bounds i dim1 header)
  :ok1
  (ldr dim1 (:@ header (:$ (:apply + arm64::misc-data-offset
                                    (:apply ash (:apply 1+ arm64::arrayH.dim0-cell)
                                            arm64::word-shift)))))
  (cmp j dim1)
  (b.lo :ok2)
  (mov dim1 (:$ arm64::fixnumone))
  (uuo-error-array-axis-bounds j dim1 header)
  :ok2
  (ldr dim2 (:@ header (:$ (:apply + arm64::misc-data-offset
                                    (:apply ash (:apply + 2 arm64::arrayH.dim0-cell)
                                            arm64::word-shift)))))
  (cmp k dim2)
  (b.lo :ok3)
  (mov dim2 (:$ 2))
  (uuo-error-array-axis-bounds k dim2 header)
  :ok3)



;;; ======================================================================
;;; Chunk 4: Misc ref/set for 32/16/8-bit, float, and bit types
;;; Also: array-data-vector-ref, node-slot-ref, %slot-ref
;;; ======================================================================

;;; --- 32-bit unsigned/signed ---

(define-arm64-vinsn (misc-ref-u32 :predicatable)
    (((dest :u32))
     ((v :lisp)
      (scaled-idx :u64))
     ())
  (ldr dest (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-c-u32 :predicatable)
    (((dest :u32))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldr dest (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 2))))))

(define-arm64-vinsn (misc-ref-s32 :predicatable)
    (((dest :s32))
     ((v :lisp)
      (scaled-idx :u64))
     ())
  (ldrsw dest (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-c-s32 :predicatable)
    (((dest :s32))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldrsw dest (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 2))))))

(define-arm64-vinsn (misc-set-c-u32 :predicatable)
    (()
     ((val :u32)
      (v :lisp)
      (idx :u32const)))
  (str val (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 2))))))

(define-arm64-vinsn (misc-set-c-s32 :predicatable)
    (()
     ((val :s32)
      (v :lisp)
      (idx :u32const)))
  (str val (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 2))))))

(define-arm64-vinsn (misc-set-u32 :predicatable)
    (()
     ((val :u32)
      (v :lisp)
      (scaled-idx :u64)))
  (str val (:@ v scaled-idx)))

(define-arm64-vinsn (misc-set-s32 :predicatable)
    (()
     ((val :s32)
      (v :lisp)
      (scaled-idx :u64)))
  (str val (:@ v scaled-idx)))


;;; --- 16-bit unsigned/signed ---

(define-arm64-vinsn (misc-ref-u16 :predicatable)
    (((dest :u16))
     ((v :lisp)
      (scaled-idx :u64))
     ())
  (ldrh dest (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-c-u16 :predicatable)
    (((dest :u16))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldrh dest (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 1))))))

(define-arm64-vinsn (misc-set-c-u16 :predicatable)
    (((val :u16))
     ((v :lisp)
      (idx :u32const))
     ())
  (strh val (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 1))))))

(define-arm64-vinsn (misc-set-u16 :predicatable)
    (((val :u16))
     ((v :lisp)
      (scaled-idx :s64)))
  (strh val (:@ v scaled-idx)))

(define-arm64-vinsn misc-ref-s16 (((dest :s16))
                                   ((v :lisp)
                                    (scaled-idx :u64))
                                   ())
  (ldrsh dest (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-c-s16 :predicatable)
    (((dest :s16))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldrsh dest (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 1))))))

(define-arm64-vinsn (misc-set-c-s16 :predicatable)
    (((val :s16))
     ((v :lisp)
      (idx :u32const))
     ())
  (strh val (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 1))))))

(define-arm64-vinsn (misc-set-s16 :predicatable)
    (((val :s16))
     ((v :lisp)
      (scaled-idx :s64)))
  (strh val (:@ v scaled-idx)))


;;; --- 8-bit unsigned/signed ---

(define-arm64-vinsn (misc-ref-u8 :predicatable)
    (((dest :u8))
     ((v :lisp)
      (scaled-idx :u64))
     ())
  (ldrb dest (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-c-u8 :predicatable)
    (((dest :u8))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldrb dest (:@ v (:$ (:apply + arm64::misc-data-offset idx)))))

(define-arm64-vinsn (misc-set-c-u8 :predicatable)
    (((val :u8))
     ((v :lisp)
      (idx :u32const))
     ())
  (strb val (:@ v (:$ (:apply + arm64::misc-data-offset idx)))))

(define-arm64-vinsn (misc-set-u8 :predicatable)
    (((val :u8))
     ((v :lisp)
      (scaled-idx :u64))
     ())
  (strb val (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-s8 :predicatable)
    (((dest :s8))
     ((v :lisp)
      (scaled-idx :u64))
     ())
  (ldrsb dest (:@ v scaled-idx)))

(define-arm64-vinsn (misc-ref-c-s8 :predicatable)
    (((dest :s8))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldrsb dest (:@ v (:$ (:apply + arm64::misc-data-offset idx)))))

(define-arm64-vinsn (misc-set-c-s8 :predicatable)
    (((val :s8))
     ((v :lisp)
      (idx :u32const))
     ())
  (strb val (:@ v (:$ (:apply + arm64::misc-data-offset idx)))))

(define-arm64-vinsn (misc-set-s8 :predicatable)
    (((val :s8))
     ((v :lisp)
      (scaled-idx :u64))
     ())
  (strb val (:@ v scaled-idx)))


;;; --- Bit access ---

;;; Constant-index bit ref: extract single bit from a word in a bit-vector.
;;; On ARM64 words are 64-bit, so 64 bits per word (vs 32 on ARM32).
(define-arm64-vinsn (misc-ref-c-bit :predicatable)
    (((dest :u8))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldr dest (:@ v (:$ (:apply + arm64::misc-data-offset
                               (:apply ash (:apply ash idx -6) arm64::word-shift)))))
  (lsr dest dest (:$ (:apply logand idx #x3f)))
  (and dest dest (:$ 1)))

;;; Constant-index bit ref returning a fixnum (0 or fixnumone=1).
(define-arm64-vinsn (misc-ref-c-bit-fixnum :predicatable)
    (((dest :imm))
     ((v :lisp)
      (idx :u32const))
     ((temp :u64)))
  (ldr temp (:@ v (:$ (:apply + arm64::misc-data-offset
                               (:apply ash (:apply ash idx -6) arm64::word-shift)))))
  (lsr temp temp (:$ (:apply logand idx #x3f)))
  (and dest temp (:$ arm64::fixnumone)))


;;; --- Single-float ---
;;; ARM64 uses ldr/str with s-registers for 32-bit float access.

(define-arm64-vinsn (misc-ref-single-float :predicatable)
    (((dest :single-float))
     ((v :lisp)
      (scaled-idx :u64))
     ((temp :u64)))
  (add temp v scaled-idx)
  (ldr dest (:@ temp (:$ 0))))

(define-arm64-vinsn (misc-ref-c-single-float :predicatable)
    (((dest :single-float))
     ((v :lisp)
      (idx :u32const))
     ())
  (ldr dest (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 2))))))

(define-arm64-vinsn (misc-set-single-float :predicatable)
    (()
     ((val :single-float)
      (v :lisp)
      (scaled-idx :u64))
     ((temp :u64)))
  (add temp v scaled-idx)
  (str val (:@ temp (:$ 0))))

(define-arm64-vinsn (misc-set-c-single-float :predicatable)
    (()
     ((val :single-float)
      (v :lisp)
      (idx :u32const)))
  (str val (:@ v (:$ (:apply + arm64::misc-data-offset (:apply ash idx 2))))))


;;; --- Double-float ---
;;; Takes unscaled fixnum index; scales inline by << word-shift (=3).

(define-arm64-vinsn (misc-ref-double-float :predicatable)
    (((dest :double-float))
     ((v :lisp)
      (unscaled-idx :imm))
     ((temp :u64)))
  (add temp v (:$ arm64::misc-dfloat-offset))
  (add temp temp (:lsl unscaled-idx (:$ arm64::word-shift)))
  (ldr dest (:@ temp (:$ 0))))

(define-arm64-vinsn (misc-ref-c-double-float :predicatable)
    (((dest :double-float))
     ((v :lisp)
      (idx :u32const)))
  (ldr dest (:@ v (:$ (:apply + arm64::misc-dfloat-offset (:apply ash idx 3))))))

(define-arm64-vinsn (misc-set-double-float :predicatable)
    (()
     ((val :double-float)
      (v :lisp)
      (unscaled-idx :imm))
     ((temp :u64)))
  (add temp v (:$ arm64::misc-dfloat-offset))
  (add temp temp (:lsl unscaled-idx (:$ arm64::word-shift)))
  (str val (:@ temp (:$ 0))))

(define-arm64-vinsn (misc-set-c-double-float :predicatable)
    (((val :double-float))
     ((v :lisp)
      (idx :u32const)))
  (str val (:@ v (:$ (:apply + arm64::misc-dfloat-offset (:apply ash idx 3))))))


;;; --- Complex-double-float ---
;;; Each element is 16 bytes (real + imag doubles).
;;; misc-complex-dfloat-offset=8 provides 16-byte alignment.
;;; Uses ldp/stp for paired double-float load/store.

(define-arm64-vinsn (misc-ref-complex-double-float :predicatable)
    (((dest :complex-double-float))
     ((v :lisp)
      (unscaled-idx :imm))
     ((temp :u64)))
  (add temp v (:$ arm64::misc-complex-dfloat-offset))
  (add temp temp (:lsl unscaled-idx (:$ 4)))
  (ldp dest (:+ dest 1) (:@ temp (:$ 0))))

(define-arm64-vinsn (misc-set-complex-double-float :predicatable)
    (()
     ((val :complex-double-float)
      (v :lisp)
      (unscaled-idx :imm))
     ((temp :u64)))
  (add temp v (:$ arm64::misc-complex-dfloat-offset))
  (add temp temp (:lsl unscaled-idx (:$ 4)))
  (stp val (:+ val 1) (:@ temp (:$ 0))))


;;; --- Array/slot access ---

(define-arm64-vinsn (array-data-vector-ref :predicatable)
    (((dest :lisp))
     ((header :lisp)))
  (ldr dest (:@ header (:$ arm64::arrayH.data-vector))))

(define-arm64-vinsn (node-slot-ref :predicatable)
    (((dest :lisp))
     ((node :lisp)
      (cellno :u32const)))
  (ldr dest (:@ node (:$ (:apply + arm64::misc-data-offset
                                  (:apply ash cellno arm64::word-shift))))))

(define-arm64-vinsn %slot-ref (((dest :lisp))
                                ((instance (:lisp (:ne dest)))
                                 (index :lisp))
                                ((scaled :u64)))
  (lsl scaled index (:$ arm64::word-shift))
  (ldr dest (:@ instance scaled))
  (lsr scaled dest (:$ arm64::tag-shift))
  (cmp scaled (:$ arm64::tag-slot-unbound))
  (b.ne :ok)
  (uuo-error-slot-unbound dest instance index)
  :ok)



;;; ======================================================================
;;; Chunk 5: Tag/typecode extraction and type checking
;;; ARM64 TBI tags: top byte (bits 56-63) via LSR #56.
;;; On ARM64, tag = fulltag (single full byte), unlike ARM32's 2-bit/3-bit split.
;;; Fixnum: tag 0x00 (positive) or 0xFF (negative).
;;; ======================================================================

;;; --- Tag extraction ---

(define-arm64-vinsn (extract-tag :predicatable)
    (((tag :u8))
     ((object :lisp))
     ())
  (lsr tag object (:$ arm64::tag-shift)))

;;; fulltag = tag on ARM64 (both are the full top byte).
(define-arm64-vinsn (extract-fulltag :predicatable)
    (((tag :u8))
     ((object :lisp))
     ())
  (lsr tag object (:$ arm64::tag-shift)))

;;; Extract tag as a fixnum.  Since fixnumshift=0, the tag byte IS a fixnum.
(define-arm64-vinsn (extract-tag-fixnum :predicatable)
    (((tag :imm))
     ((object :lisp)))
  (lsr tag object (:$ arm64::tag-shift)))

(define-arm64-vinsn (extract-fulltag-fixnum :predicatable)
    (((tag :imm))
     ((object :lisp)))
  (lsr tag object (:$ arm64::tag-shift)))

;;; Extract typecode: tag for non-uvector, subtag for uvector.
;;; uvector-ref (0x40) has bit 6 set; test that to distinguish.
(define-arm64-vinsn extract-typecode (((code :u8))
                                      ((object :lisp))
                                      ())
  (lsr code object (:$ arm64::tag-shift))
  (tst code (:$ arm64::uvector-ref))
  (b.eq :done)
  (ldur code (:@ object (:$ arm64::misc-subtag-offset)))
  (and code code (:$ #xff))
  :done)

;;; Typecode as fixnum (fixnumshift=0, so same as typecode).
(define-arm64-vinsn extract-typecode-fixnum (((code :imm))
                                             ((object (:lisp (:ne code))))
                                             ((subtag :u8)))
  (lsr subtag object (:$ arm64::tag-shift))
  (tst subtag (:$ arm64::uvector-ref))
  (b.eq :not-uvector)
  (ldur subtag (:@ object (:$ arm64::misc-subtag-offset)))
  (and subtag subtag (:$ #xff))
  :not-uvector
  (mov code subtag))


;;; --- trap-unless (error, not continuable) ---

;;; Fixnum: tag is 0x00 or 0xFF.
(define-arm64-vinsn trap-unless-fixnum (()
                                        ((object :lisp))
                                        ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cbz tag :ok)
  (cmp tag (:$ arm64::tag-negative-fixnum))
  (b.eq :ok)
  (uuo-error-reg-not-lisptag object (:$ arm64::tag-positive-fixnum))
  :ok)

;;; List: tag is tag-nil (0x02) or tag-cons (0x03).
(define-arm64-vinsn trap-unless-list (()
                                      ((object :lisp))
                                      ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (sub tag tag (:$ arm64::tag-nil))
  (cmp tag (:$ 2))
  (b.lo :ok)
  (uuo-error-reg-not-lisptag object (:$ arm64::tag-nil))
  :ok)

;;; Cons: tag is exactly tag-cons (0x03).
(define-arm64-vinsn trap-unless-cons (()
                                      ((object :lisp))
                                      ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cmp tag (:$ arm64::tag-cons))
  (b.eq :ok)
  (uuo-error-reg-not-fulltag object (:$ arm64::tag-cons))
  :ok)

;;; Character: tag is tag-character (0x11).
(define-arm64-vinsn trap-unless-character (()
                                           ((object :lisp))
                                           ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cmp tag (:$ arm64::tag-character))
  (b.eq :ok)
  (uuo-error-reg-not-xtype object (:$ arm64::tag-character))
  :ok)

;;; Uvector: tag has bit 6 set (uvector-ref = 0x40).
(define-arm64-vinsn trap-unless-uvector (()
                                         ((object :lisp))
                                         ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.ne :ok)
  (uuo-error-reg-not-lisptag object (:$ arm64::uvector-ref))
  :ok)

;;; Single-float: IMMEDIATE on ARM64 (tag 0x10), not heap-allocated.
(define-arm64-vinsn trap-unless-single-float (()
                                              ((object :lisp))
                                              ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cmp tag (:$ arm64::tag-single-float))
  (b.eq :ok)
  (uuo-error-reg-not-xtype object (:$ arm64::subtag-single-float))
  :ok)

;;; Double-float: heap-allocated uvector.
(define-arm64-vinsn trap-unless-double-float (()
                                              ((object :lisp))
                                              ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :fail)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-double-float))
  (b.eq :ok)
  :fail
  (uuo-error-reg-not-xtype object (:$ arm64::subtag-double-float))
  :ok)

;;; Generic typecode check: uvector with specific subtag.
(define-arm64-vinsn trap-unless-typecode= (()
                                           ((object :lisp)
                                            (tagval :u16const))
                                           ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :fail)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ tagval))
  (b.eq :ok)
  :fail
  (uuo-error-reg-not-xtype object (:$ tagval))
  :ok)


;;; --- require (continuable error) ---

(define-arm64-vinsn require-fixnum (()
                                    ((object :lisp))
                                    ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cbz tag :ok)
  (cmp tag (:$ arm64::tag-negative-fixnum))
  (b.eq :ok)
  (uuo-cerror-reg-not-lisptag object (:$ arm64::tag-positive-fixnum))
  :ok)

(define-arm64-vinsn require-integer (()
                                     ((object :lisp))
                                     ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cbz tag :got-it)
  (cmp tag (:$ arm64::tag-negative-fixnum))
  (b.eq :got-it)
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-bignum))
  (b.eq :got-it)
  :bad
  (uuo-cerror-reg-not-xtype object (:$ arm64::xtype-integer))
  :got-it)

(define-arm64-vinsn require-list (()
                                  ((object :lisp))
                                  ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (sub tag tag (:$ arm64::tag-nil))
  (cmp tag (:$ 2))
  (b.lo :ok)
  (uuo-cerror-reg-not-lisptag object (:$ arm64::tag-nil))
  :ok)

(define-arm64-vinsn require-symbol (()
                                    ((object :lisp))
                                    ((tag :u8)))
  (cmp object rnil)
  (b.eq :ok)
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-symbol))
  (b.eq :ok)
  :bad
  (uuo-cerror-reg-not-xtype object (:$ arm64::subtag-symbol))
  :ok)

(define-arm64-vinsn require-character (()
                                       ((object :lisp))
                                       ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cmp tag (:$ arm64::tag-character))
  (b.eq :ok)
  (uuo-cerror-reg-not-xtype object (:$ arm64::tag-character))
  :ok)

(define-arm64-vinsn require-simple-vector (()
                                           ((object :lisp))
                                           ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-simple-vector))
  (b.eq :ok)
  :bad
  (uuo-cerror-reg-not-xtype object (:$ arm64::subtag-simple-vector))
  :ok)

(define-arm64-vinsn require-simple-string (()
                                           ((object :lisp))
                                           ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-simple-base-string))
  (b.eq :ok)
  :bad
  (uuo-cerror-reg-not-xtype object (:$ arm64::subtag-simple-base-string))
  :ok)

;;; Real: fixnum OR single-float (immediate) OR uvector with real subtag.
;;; Real subtags: bignum, double-float, ratio, short-float (if exists).
(define-arm64-vinsn require-real (()
                                  ((object :lisp))
                                  ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cbz tag :ok)
  (cmp tag (:$ arm64::tag-negative-fixnum))
  (b.eq :ok)
  (cmp tag (:$ arm64::tag-single-float))
  (b.eq :ok)
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-double-float))
  (b.eq :ok)
  (cmp tag (:$ arm64::subtag-bignum))
  (b.eq :ok)
  (cmp tag (:$ arm64::subtag-ratio))
  (b.eq :ok)
  :bad
  (uuo-cerror-reg-not-xtype object (:$ arm64::xtype-real))
  :ok)

;;; Number: real OR complex.
(define-arm64-vinsn require-number (()
                                    ((object :lisp))
                                    ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cbz tag :ok)
  (cmp tag (:$ arm64::tag-negative-fixnum))
  (b.eq :ok)
  (cmp tag (:$ arm64::tag-single-float))
  (b.eq :ok)
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-double-float))
  (b.eq :ok)
  (cmp tag (:$ arm64::subtag-bignum))
  (b.eq :ok)
  (cmp tag (:$ arm64::subtag-ratio))
  (b.eq :ok)
  (cmp tag (:$ arm64::subtag-complex))
  (b.eq :ok)
  (cmp tag (:$ arm64::subtag-complex-single-float))
  (b.eq :ok)
  (cmp tag (:$ arm64::subtag-complex-double-float))
  (b.eq :ok)
  :bad
  (uuo-cerror-reg-not-xtype object (:$ arm64::xtype-number))
  :ok)


;;; --- Fixed-width integer requires ---
;;; On ARM64 with fixnumshift=0, the fixnum IS the integer value.
;;; Sign-extension comparison simultaneously verifies fixnum tag and range.

;;; s8: fixnum in [-128, 127].  Sign-extend low 8 bits; compare.
(define-arm64-vinsn require-s8 (()
                                ((object :lisp))
                                ((temp :u64)))
  (lsl temp object (:$ (- arm64::nbits-in-word 8)))
  (asr temp temp (:$ (- arm64::nbits-in-word 8)))
  (cmp temp object)
  (b.eq :ok)
  (uuo-cerror-reg-not-xtype object (:$ arm64::xtype-s8))
  :ok)

;;; u8: non-negative fixnum ≤ 255.  All bits above low 8 must be zero.
(define-arm64-vinsn require-u8 (()
                                ((object :lisp))
                                ())
  (tst object (:$ (:apply lognot #xff)))
  (b.eq :ok)
  (uuo-cerror-reg-not-xtype object (:$ arm64::xtype-u8))
  :ok)

;;; s16: fixnum in [-32768, 32767].
(define-arm64-vinsn require-s16 (()
                                 ((object :lisp))
                                 ((temp :u64)))
  (lsl temp object (:$ (- arm64::nbits-in-word 16)))
  (asr temp temp (:$ (- arm64::nbits-in-word 16)))
  (cmp temp object)
  (b.eq :ok)
  (uuo-cerror-reg-not-xtype object (:$ arm64::xtype-s16))
  :ok)

;;; u16: non-negative fixnum ≤ 65535.
(define-arm64-vinsn require-u16 (()
                                 ((object :lisp))
                                 ())
  (tst object (:$ (:apply lognot #xffff)))
  (b.eq :ok)
  (uuo-cerror-reg-not-xtype object (:$ arm64::xtype-u16))
  :ok)

;;; s32: fixnum in [-2^31, 2^31-1] OR one-digit bignum.
(define-arm64-vinsn require-s32 (()
                                 ((src :lisp))
                                 ((tag :u64)
                                  (header :u64)))
  (lsl tag src (:$ (- arm64::nbits-in-word 32)))
  (asr tag tag (:$ (- arm64::nbits-in-word 32)))
  (cmp tag src)
  (b.eq :got-it)
  ;; Not a fixnum in s32 range; check for one-digit bignum.
  (lsr tag src (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur header (:@ src (:$ arm64::misc-header-offset)))
  (lsr tag header (:$ arm64::subtag-shift))
  (cmp tag (:$ arm64::subtag-bignum))
  (b.ne :bad)
  (ubfx header header (:$ 0) (:$ arm64::subtag-shift))
  (cmp header (:$ 1))
  (b.eq :got-it)
  :bad
  (uuo-cerror-reg-not-xtype src (:$ arm64::xtype-s32))
  :got-it)

;;; u32: non-negative fixnum ≤ 2^32-1 OR bignum that fits.
(define-arm64-vinsn require-u32 (()
                                 ((src :lisp))
                                 ((temp :u64)))
  (tst src (:$ (:apply lognot #xffffffff)))
  (b.eq :got-it)
  ;; Check for bignum
  (lsr temp src (:$ arm64::tag-shift))
  (tst temp (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur temp (:@ src (:$ arm64::misc-header-offset)))
  (and temp temp (:$ #xff))
  (cmp temp (:$ arm64::subtag-bignum))
  (b.ne :bad)
  ;; 1-digit bignum with non-negative 32-bit value?
  (ldr temp (:@ src (:$ arm64::misc-data-offset)))
  (tst temp (:$ (:apply lognot #xffffffff)))
  (b.eq :got-it)
  :bad
  (uuo-cerror-reg-not-xtype src (:$ arm64::xtype-u32))
  :got-it)

;;; s64: any fixnum OR one-digit bignum.
(define-arm64-vinsn require-s64 (()
                                 ((src :lisp))
                                 ((tag :u64)
                                  (header :u64)))
  (lsr tag src (:$ arm64::tag-shift))
  (cbz tag :got-it)
  (cmp tag (:$ arm64::tag-negative-fixnum))
  (b.eq :got-it)
  ;; Check for bignum
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur header (:@ src (:$ arm64::misc-header-offset)))
  (lsr tag header (:$ arm64::subtag-shift))
  (cmp tag (:$ arm64::subtag-bignum))
  (b.ne :bad)
  (ubfx header header (:$ 0) (:$ arm64::subtag-shift))
  (cmp header (:$ 1))
  (b.eq :got-it)
  :bad
  (uuo-cerror-reg-not-xtype src (:$ arm64::xtype-s64))
  :got-it)

;;; u64: non-negative fixnum OR bignum with 1 digit (non-negative) OR 2 digits with high=0.
(define-arm64-vinsn require-u64 (()
                                 ((src :lisp))
                                 ((temp :u64)
                                  (header :u64)))
  ;; Quick check: non-negative fixnum (tag=0, value >= 0 → top byte = 0x00)
  (lsr temp src (:$ arm64::tag-shift))
  (cbz temp :got-it)
  ;; Check for bignum
  (tst temp (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur header (:@ src (:$ arm64::misc-header-offset)))
  (lsr temp header (:$ arm64::subtag-shift))
  (cmp temp (:$ arm64::subtag-bignum))
  (b.ne :bad)
  (ubfx header header (:$ 0) (:$ arm64::subtag-shift))
  (cmp header (:$ 2))
  (b.eq :two)
  (cmp header (:$ 1))
  (b.ne :bad)
  ;; 1-digit bignum: must be non-negative (top bit clear)
  (ldr temp (:@ src (:$ arm64::misc-data-offset)))
  (tst temp (:$ (:apply ash 1 63)))
  (b.eq :got-it)
  (b :bad)
  :two
  ;; 2-digit bignum: second word must be 0
  (ldr temp (:@ src (:$ (:apply + arm64::misc-data-offset 8))))
  (cbz temp :got-it)
  :bad
  (uuo-cerror-reg-not-xtype src (:$ arm64::xtype-u64))
  :got-it)



;;; ======================================================================
;;; Chunk 6: Boxing/unboxing and comparisons
;;; ARM64 key insight: fixnumshift=0, so fixnum IS the integer.
;;; box-fixnum and fixnum->signed/unsigned are identity (mov).
;;; ======================================================================

;;; --- Boxing (value → tagged fixnum) ---

;;; On ARM64, fixnumshift=0: the fixnum IS the raw integer.
(define-arm64-vinsn (box-fixnum :predicatable)
    (((dest :imm))
     ((src :s64)))
  (mov dest src))

(define-arm64-vinsn (fixnum->signed-natural :predicatable)
    (((dest :s64))
     ((src :imm)))
  (mov dest src))

(define-arm64-vinsn (fixnum->unsigned-natural :predicatable)
    (((dest :u64))
     ((src :imm)))
  (mov dest src))


;;; --- Unboxing (tagged value → raw value with type check) ---

(define-arm64-vinsn unbox-u8 (((dest :u8))
                               ((src :lisp)))
  (tst src (:$ (:apply lognot #xff)))
  (b.eq :ok)
  (uuo-error-reg-not-xtype src (:$ arm64::xtype-u8))
  :ok
  (mov dest src))

(define-arm64-vinsn unbox-s8 (((dest :s8))
                               ((src :lisp))
                               ((temp :u64)))
  (lsl temp src (:$ (- arm64::nbits-in-word 8)))
  (asr temp temp (:$ (- arm64::nbits-in-word 8)))
  (cmp temp src)
  (b.eq :ok)
  (uuo-error-reg-not-xtype src (:$ arm64::xtype-s8))
  :ok
  (mov dest src))

(define-arm64-vinsn unbox-u16 (((dest :u16))
                                ((src :lisp)))
  (tst src (:$ (:apply lognot #xffff)))
  (b.eq :ok)
  (uuo-error-reg-not-xtype src (:$ arm64::xtype-u16))
  :ok
  (mov dest src))

(define-arm64-vinsn unbox-s16 (((dest :s16))
                                ((src :lisp))
                                ((temp :u64)))
  (lsl temp src (:$ (- arm64::nbits-in-word 16)))
  (asr temp temp (:$ (- arm64::nbits-in-word 16)))
  (cmp temp src)
  (b.eq :ok)
  (uuo-error-reg-not-xtype src (:$ arm64::xtype-s16))
  :ok
  (mov dest src))

;;; unbox-u32: fixnum in [0, 2^32-1] OR suitable bignum.
(define-arm64-vinsn unbox-u32 (((dest :u32))
                                ((src :lisp))
                                ((temp :u64)))
  (tst src (:$ (:apply lognot #xffffffff)))
  (b.ne :check-bignum)
  (mov dest src)
  (b :got-it)
  :check-bignum
  (lsr temp src (:$ arm64::tag-shift))
  (tst temp (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur temp (:@ src (:$ arm64::misc-header-offset)))
  (and temp temp (:$ #xff))
  (cmp temp (:$ arm64::subtag-bignum))
  (b.ne :bad)
  ;; 1-digit bignum: value must be non-negative u32
  (ldr dest (:@ src (:$ arm64::misc-data-offset)))
  (tst dest (:$ (:apply lognot #xffffffff)))
  (b.eq :got-it)
  :bad
  (uuo-error-reg-not-xtype src (:$ arm64::xtype-u32))
  :got-it)

;;; unbox-s32: fixnum in [-2^31, 2^31-1] OR one-digit bignum.
(define-arm64-vinsn unbox-s32 (((dest :s32))
                                ((src :lisp))
                                ((tag :u64)
                                 (header :u64)))
  ;; Check fixnum in s32 range: sign-extend low 32 bits, compare
  (lsl tag src (:$ 32))
  (asr tag tag (:$ 32))
  (cmp tag src)
  (b.ne :check-bignum)
  (mov dest src)
  (b :got-it)
  :check-bignum
  (lsr tag src (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :bad)
  (ldur header (:@ src (:$ arm64::misc-header-offset)))
  (lsr tag header (:$ arm64::subtag-shift))
  (cmp tag (:$ arm64::subtag-bignum))
  (b.ne :bad)
  (ubfx header header (:$ 0) (:$ arm64::subtag-shift))
  (cmp header (:$ 1))
  (b.ne :bad)
  (ldr dest (:@ src (:$ arm64::misc-data-offset)))
  (b :got-it)
  :bad
  (uuo-error-reg-not-xtype src (:$ arm64::xtype-s32))
  :got-it)

;;; unbox-base-char: extract 8-bit character code from tagged character.
(define-arm64-vinsn unbox-base-char (((dest :u32))
                                     ((src :lisp))
                                     ((tag :u8)))
  (lsr tag src (:$ arm64::tag-shift))
  (cmp tag (:$ arm64::tag-character))
  (b.ne :bad)
  (lsr dest src (:$ arm64::charcode-shift))
  (and dest dest (:$ (:apply 1- (:apply ash 1 arm64::ncharcodebits))))
  (b :ok)
  :bad
  (uuo-error-reg-not-xtype src (:$ arm64::tag-character))
  :ok)

;;; unbox-bit: value must be fixnum 0 or 1.
(define-arm64-vinsn unbox-bit (((dest :u32))
                                ((src :lisp)))
  (cmp src (:$ arm64::fixnumone))
  (b.ls :ok)
  (uuo-error-reg-not-xtype src (:$ arm64::xtype-bit))
  :ok
  (mov dest src))


;;; --- Character conversions ---

;;; character->fixnum: extract charcode as fixnum (fixnumshift=0 → same value).
(define-arm64-vinsn (character->fixnum :predicatable)
    (((dest :lisp))
     ((src :lisp))
     ())
  (lsr dest src (:$ arm64::charcode-shift))
  (and dest dest (:$ (:apply 1- (:apply ash 1 arm64::ncharcodebits)))))

;;; fixnum->char: produce a tagged character from a fixnum charcode.
;;; Returns NIL for surrogate codepoints (0xD800-0xDFFF).
(define-arm64-vinsn fixnum->char (((dest :lisp))
                                  ((src :imm))
                                  ((temp :u64)))
  (lsr temp src (:$ 11))
  (cmp temp (:$ 27))
  (b.eq :bad)
  (lsl dest src (:$ arm64::charcode-shift))
  (movk dest (:$ (:apply ash arm64::tag-character 8)) (:lsl 48))
  (b :done)
  :bad
  (mov dest rnil)
  :done)


;;; --- Comparisons ---

(define-arm64-vinsn compare (((crf :crf))
                             ((arg0 t)
                              (arg1 t))
                             ())
  (cmp arg0 arg1))

;;; On ARM64, nil-value won't fit CMP immediate.  Use rnil register.
(define-arm64-vinsn compare-to-nil (((crf :crf))
                                    ((arg0 t)))
  (cmp arg0 rnil))

(define-arm64-vinsn compare-logical (((crf :crf))
                                     ((arg0 t)
                                      (arg1 t))
                                     ())
  (cmp arg0 arg1))

(define-arm64-vinsn compare-immediate (((crf :crf))
                                       ((arg t)
                                        (imm :u32const)))
  (cmp arg (:$ imm)))


;;; --- Integer widening (s32/u32 → Lisp integer) ---

;;; s32->integer: On ARM64, all s32 values fit in a fixnum (56-bit range).
;;; Just sign-extend from 32 bits to 64 bits.
(define-arm64-vinsn (s32->integer :predicatable)
    (((result :lisp))
     ((src :s32)))
  (lsl result src (:$ 32))
  (asr result result (:$ 32)))

;;; u32->integer: On ARM64, all u32 values fit in a fixnum.
;;; Zero-extend (the 32-bit register form does this automatically).
(define-arm64-vinsn (u32->integer :predicatable)
    (((result :lisp))
     ((src :u32)))
  (mov result src))


;;; ======================================================================
;;; Chunk 7: Arithmetic + logical + shift operations
;;; On ARM64 with fixnumshift=0, fixnums ARE raw integers (tags in top byte).
;;; Most arithmetic works directly; overflow means the result's tag byte
;;; is neither 0x00 (positive) nor 0xFF (negative sign-extension).
;;; Overflow check pattern: LSL 8 / ASR 8 / CMP — sign-extends from bit 55
;;; and compares to the original.  EQ = valid fixnum, NE = overflow.
;;; ======================================================================

;;; --- Fixnum arithmetic ---

(define-arm64-vinsn (fixnum-add :predicatable)
    (((dest t))
     ((x t)
      (y t)))
  (add dest x y))

(define-arm64-vinsn fixnum-add-set-flags (((dest t)
                                           (flags :crf))
                                          ((x t)
                                           (y t))
                                          ((tag :u64)))
  (add dest x y)
  (lsl tag dest (:$ 8))
  (asr tag tag (:$ 8))
  (cmp tag dest))

(define-arm64-vinsn (fixnum-sub :predicatable)
    (((dest t))
     ((x t)
      (y t)))
  (sub dest x y))

(define-arm64-vinsn fixnum-sub-set-flags (((dest t)
                                           (flags :crf))
                                          ((x t)
                                           (y t))
                                          ((tag :u64)))
  (sub dest x y)
  (lsl tag dest (:$ 8))
  (asr tag tag (:$ 8))
  (cmp tag dest))

(define-arm64-vinsn (fixnum-sub-constant :predicatable)
    (((dest t))
     ((x t)
      (y :s32const)))
  (sub dest x (:$ y)))

(define-arm64-vinsn fixnum-sub-constant-set-flags (((dest t)
                                                    (flags :crf))
                                                   ((x t)
                                                    (y :s32const))
                                                   ((tag :u64)))
  (sub dest x (:$ y))
  (lsl tag dest (:$ 8))
  (asr tag tag (:$ 8))
  (cmp tag dest))

;;; fixnum-sub-from-constant: dest = constant - src.
;;; ARM32 used RSB; ARM64 has no RSB.  Use NEG + ADD.
(define-arm64-vinsn (fixnum-sub-from-constant :predicatable)
    (((dest :imm))
     ((x :s32const)
      (y :imm)))
  (neg dest y)
  (add dest dest (:$ x)))

(define-arm64-vinsn fixnum-sub-from-constant-set-flags
    (((dest :imm)
      (flags :crf))
     ((x :s32const)
      (y :imm))
     ((tag :u64)))
  (neg dest y)
  (add dest dest (:$ x))
  (lsl tag dest (:$ 8))
  (asr tag tag (:$ 8))
  (cmp tag dest))

;;; multiply-fixnums: With fixnumshift=0, both operands are raw integers.
;;; On ARM32, one operand was unboxed first (>> fixnumshift); here just multiply.
(define-arm64-vinsn (multiply-fixnums :predicatable)
    (((dest :imm))
     ((a :imm)
      (b :imm)))
  (mul dest a b))


;;; --- Unboxed natural (machine word) arithmetic ---

(define-arm64-vinsn (%natural+ :predicatable)
    (((dest :u64))
     ((x :u64) (y :u64)))
  (add dest x y))

(define-arm64-vinsn (%natural+-c :predicatable)
    (((dest :u64))
     ((x :u64) (y :u16const)))
  (add dest x (:$ y)))

(define-arm64-vinsn (%natural- :predicatable)
    (((dest :u64))
     ((x :u64) (y :u64)))
  (sub dest x y))

(define-arm64-vinsn (%natural--c :predicatable)
    (((dest :u64))
     ((x :u64) (y :u16const)))
  (sub dest x (:$ y)))


;;; --- Unboxed natural logical operations ---

(define-arm64-vinsn (%natural-logior :predicatable)
    (((dest :u64))
     ((x :u64) (y :u64)))
  (orr dest x y))

(define-arm64-vinsn (%natural-logior-c :predicatable)
    (((dest :u64))
     ((x :u64) (c :u32const)))
  (orr dest x (:$ c)))

(define-arm64-vinsn (%natural-logxor :predicatable)
    (((dest :u64))
     ((x :u64) (y :u64)))
  (eor dest x y))

(define-arm64-vinsn (%natural-logxor-c :predicatable)
    (((dest :u64))
     ((x :u64) (c :u32const)))
  (eor dest x (:$ c)))

(define-arm64-vinsn (%natural-logand :predicatable)
    (((dest :u64))
     ((x :u64) (y :u64)))
  (and dest x y))

(define-arm64-vinsn (%natural-logand-c :predicatable)
    (((dest :u64))
     ((x :u64) (c :u32const)))
  (and dest x (:$ c)))


;;; --- Tagged fixnum logical operations ---

(define-arm64-vinsn (%logior2 :predicatable)
    (((dest :imm))
     ((x :imm)
      (y :imm))
     ())
  (orr dest x y))

(define-arm64-vinsn (logior-immediate :predicatable)
    (((dest :imm))
     ((src :imm)
      (imm :u32const)))
  (orr dest src (:$ imm)))

(define-arm64-vinsn (%logand2 :predicatable)
    (((dest :imm))
     ((x :imm)
      (y :imm))
     ())
  (and dest x y))

(define-arm64-vinsn (logand-immediate :predicatable)
    (((dest :imm))
     ((src :imm)
      (imm :u32const)))
  (and dest src (:$ imm)))

(define-arm64-vinsn (%logxor2 :predicatable)
    (((dest :imm))
     ((x :imm)
      (y :imm))
     ())
  (eor dest x y))

(define-arm64-vinsn (logxor-immediate :predicatable)
    (((dest :imm))
     ((src :imm)
      (imm :u32const)))
  (eor dest src (:$ imm)))


;;; --- Shift operations ---

;;; %ilsl: Left shift fixnum by variable count.
;;; With fixnumshift=0, count is already a raw integer; no unboxing needed.
(define-arm64-vinsn (%ilsl :predicatable)
    (((dest :imm))
     ((count :imm)
      (src :imm)))
  (lsl dest src count))

;;; %ilsl-c: Left shift fixnum by constant count.
(define-arm64-vinsn (%ilsl-c :predicatable)
    (((dest :imm))
     ((count :u8const)
      (src :imm)))
  ((:pred = count 0)
   (mov dest src))
  ((:not (:pred = count 0))
   (lsl dest src (:$ (:apply logand count 63)))))

;;; %iasr: Arithmetic right shift fixnum by variable count.
;;; ASR naturally preserves sign-extension (0x00 or 0xFF tag byte).
(define-arm64-vinsn (%iasr :predicatable)
    (((dest :imm))
     ((count :imm)
      (src :imm)))
  (asr dest src count))

;;; %iasr-c: Arithmetic right shift fixnum by constant count.
(define-arm64-vinsn (%iasr-c :predicatable)
    (((dest :imm))
     ((count :u8const)
      (src :imm)))
  ((:pred = count 0)
   (mov dest src))
  ((:not (:pred = count 0))
   (asr dest src (:$ count))))

;;; %ilsr: Logical right shift fixnum by variable count.
;;; Must clear the tag byte (bits 56-63) first, otherwise the 0xFF tag
;;; of negative fixnums would shift into the value bits.
(define-arm64-vinsn (%ilsr :predicatable)
    (((dest :imm))
     ((count :imm)
      (src :imm))
     ((temp :u64)))
  (and temp src (:$ (:apply 1- (:apply ash 1 arm64::tag-shift))))
  (lsr dest temp count))

;;; %ilsr-c: Logical right shift fixnum by constant count.
(define-arm64-vinsn (%ilsr-c :predicatable)
    (((dest :imm))
     ((count :u8const)
      (src :imm))
     ((temp :u64)))
  ((:pred = count 0)
   (mov dest src))
  ((:not (:pred = count 0))
   (and temp src (:$ (:apply 1- (:apply ash 1 arm64::tag-shift))))
   (lsr dest temp (:$ count))))


;;; --- Logical NOT ---

;;; %ilognot: Bitwise NOT of a fixnum.
;;; On ARM64, MVN naturally flips the tag byte (0x00↔0xFF),
;;; so the result is always a valid fixnum with correct tag.
(define-arm64-vinsn (%ilognot :predicatable)
    (((dest :imm))
     ((src :imm)))
  (mvn dest src))

;;; fixnum-lognot: Same as %ilognot on ARM64.
;;; (On ARM32 they differed in tag-bit handling; here both are just MVN.)
(define-arm64-vinsn (fixnum-lognot :predicatable)
    (((dest :imm))
     ((src :imm)))
  (mvn dest src))


;;; --- Fixnum negation ---

;;; negate-fixnum-set-flags: Negate with overflow detection.
;;; Overflow only when negating most-negative-fixnum (-2^55).
(define-arm64-vinsn negate-fixnum-set-flags (((dest :lisp)
                                              (flags :crf))
                                             ((src :imm))
                                             ((tag :u64)))
  (neg dest src)
  (lsl tag dest (:$ 8))
  (asr tag tag (:$ 8))
  (cmp tag dest))

;;; negate-fixnum-no-ovf: Negate without overflow check.
(define-arm64-vinsn (negate-fixnum-no-ovf :predicatable)
    (((dest :lisp))
     ((src :imm)))
  (neg dest src))


;;; ======================================================================
;;; Chunk 8: Floating-point operations
;;; ARM64 FP instructions: fadd/fsub/fmul/fdiv/fneg/fcmp/fcvt/scvtf/fmov.
;;; fcmp directly sets NZCV (no FMSTAT needed, unlike ARM32 VFP).
;;; Single-float is IMMEDIATE on ARM64 (tag 0x10, value in low 32 bits).
;;; Double-float is heap-allocated (uvector, like ARM32).
;;; ======================================================================

;;; --- Double-float arithmetic ---

(define-arm64-vinsn (double-float+-2 :predicatable)
    (((result :double-float))
     ((x :double-float)
      (y :double-float)))
  (fadd result x y))

(define-arm64-vinsn (double-float--2 :predicatable)
    (((result :double-float))
     ((x :double-float)
      (y :double-float)))
  (fsub result x y))

(define-arm64-vinsn (double-float*-2 :predicatable)
    (((result :double-float))
     ((x :double-float)
      (y :double-float)))
  (fmul result x y))

(define-arm64-vinsn (double-float/-2 :predicatable)
    (((result :double-float))
     ((x :double-float)
      (y :double-float)))
  (fdiv result x y))


;;; --- Single-float arithmetic ---

(define-arm64-vinsn (single-float+-2 :predicatable)
    (((result :single-float))
     ((x :single-float)
      (y :single-float)))
  (fadd result x y))

(define-arm64-vinsn (single-float--2 :predicatable)
    (((result :single-float))
     ((x :single-float)
      (y :single-float)))
  (fsub result x y))

(define-arm64-vinsn (single-float*-2 :predicatable)
    (((result :single-float))
     ((x :single-float)
      (y :single-float)))
  (fmul result x y))

(define-arm64-vinsn (single-float/-2 :predicatable)
    (((result :single-float))
     ((x :single-float)
      (y :single-float)))
  (fdiv result x y))


;;; --- Float compare ---
;;; ARM64 FCMP directly sets condition flags (no FMSTAT needed).

(define-arm64-vinsn double-float-compare (((crf :crf))
                                          ((arg0 :double-float)
                                           (arg1 :double-float))
                                          ())
  (fcmp arg0 arg1))

(define-arm64-vinsn single-float-compare (((crf :crf))
                                          ((arg0 :single-float)
                                           (arg1 :single-float))
                                          ())
  (fcmp arg0 arg1))


;;; --- Float negate ---

(define-arm64-vinsn (double-float-negate :predicatable)
    (((dest :double-float))
     ((src :double-float)))
  (fneg dest src))

(define-arm64-vinsn (single-float-negate :predicatable)
    (((dest :single-float))
     ((src :single-float)))
  (fneg dest src))


;;; --- Load/store double-float from/to heap object ---
;;; ARM64 TBI: tagged pointer works as address (HW ignores tag byte).
;;; double-float.value = 0, so load/store at offset 0 from tagged pointer.
;;; No LR hack needed (unlike ARM32 which used LR as address temp).

(define-arm64-vinsn (get-double :predicatable)
    (((target :double-float))
     ((source :lisp)))
  (ldr target (:@ source (:$ arm64::double-float.value))))

(define-arm64-vinsn (store-double :predicatable)
    (()
     ((dest :lisp)
      (source :double-float)))
  (str source (:@ dest (:$ arm64::double-float.value))))


;;; --- Extract/create single-float (immediate on ARM64) ---
;;; Single-float layout: tag 0x10 in bits 56-63, IEEE float in bits 0-31.
;;; get-single: extract float from immediate tagged value (GPR → FPR).
;;; The assembler generates fmov sN, wN (low 32 bits of GPR).

(define-arm64-vinsn (get-single :predicatable)
    (((target :single-float))
     ((source :lisp)))
  (fmov target source))


;;; --- Boxing operations ---

;;; single->node: Create immediate tagged single-float from FPR.
;;; fmov wN, sN zeros the upper 32 bits; movk sets the tag byte.
(define-arm64-vinsn single->node
    (((result :lisp))
     ((fpreg :single-float)))
  (fmov result fpreg)
  (movk result (:$ (:apply ash arm64::tag-single-float 8)) (:lsl 48)))

;;; double->heap: Allocate a double-float object on the heap.
;;; Allocation sequence: sub allocptr, cmp allocbase, b.hi, hlt #0.
(define-arm64-vinsn double->heap (((result :lisp))
                                  ((fpreg :double-float))
                                  ((header :u64)))
  (mov header (:$ arm64::double-float-header))
  (sub allocptr allocptr (:$ arm64::double-float.size))
  (cmp allocptr allocbase)
  (b.hi :no-trap)
  (hlt (:$ 0))
  :no-trap
  (str header (:@ allocptr (:$ 0)))
  (str fpreg (:@ allocptr (:$ arm64::node-size)))
  (add result allocptr (:$ arm64::misc-bias))
  (movk result (:$ (:apply ash arm64::tag-double-float 8)) (:lsl 48)))


;;; --- Float conversions ---

;;; fixnum->double: With fixnumshift=0, the fixnum IS the raw signed integer.
;;; SCVTF converts 64-bit signed int (x-register) to double directly.
(define-arm64-vinsn (fixnum->double :predicatable)
    (((dest :double-float))
     ((src :lisp)))
  (scvtf dest src))

;;; fixnum->single: Same, but to single-precision.
(define-arm64-vinsn (fixnum->single :predicatable)
    (((dest :single-float))
     ((src :lisp)))
  (scvtf dest src))

;;; double-to-single: Convert double to single precision.
(define-arm64-vinsn double-to-single (((result :single-float))
                                      ((arg :double-float)))
  (fcvt result arg))

;;; single-to-double: Convert single to double precision.
(define-arm64-vinsn single-to-double (((result :double-float))
                                      ((arg :single-float)))
  (fcvt result arg))


;;; ======================================================================
;;; Chunk 9: List operations + allocation
;;; Cons access, heap allocation (cons, vcell, misc), stack allocation,
;;; and C frame management for AAPCS64.
;;; ======================================================================

;;; --- List (cons cell) access ---
;;; ARM64 TBI: tagged pointer works directly as address.
;;; cons.car = 0 (LDR), cons.cdr = -8 (LDUR for negative offset).

(define-arm64-vinsn (%car :predicatable)
    (((dest :lisp))
     ((src :lisp)))
  (ldr dest (:@ src (:$ arm64::cons.car))))

(define-arm64-vinsn (%cdr :predicatable)
    (((dest :lisp))
     ((src :lisp)))
  (ldur dest (:@ src (:$ arm64::cons.cdr))))

(define-arm64-vinsn (%set-car :predicatable)
    (()
     ((cell :lisp)
      (new :lisp)))
  (str cell (:@ new (:$ arm64::cons.car))))

(define-arm64-vinsn (%set-cdr :predicatable)
    (()
     ((cell :lisp)
      (new :lisp)))
  (stur cell (:@ new (:$ arm64::cons.cdr))))


;;; --- Cons allocation ---
;;; Allocate a cons cell on the heap.
;;; Raw layout: [CDR @ allocptr+0] [CAR @ allocptr+8].
;;; Tagged pointer = allocptr + cons-bias(8), tag-cons in top byte.
;;; From tagged ptr: car = *(ptr+0), cdr = *(ptr-8).

(define-arm64-vinsn cons (((dest :lisp))
                          ((newcar :lisp)
                           (newcdr :lisp)))
  (sub allocptr allocptr (:$ arm64::dnode-size))
  (cmp allocptr allocbase)
  (b.hi :no-trap)
  (hlt (:$ 0))
  :no-trap
  (stp newcdr newcar (:@ allocptr (:$ 0)))
  (add dest allocptr (:$ arm64::cons-bias))
  (movk dest (:$ (:apply ash arm64::tag-cons 8)) (:lsl 48)))


;;; --- Stack-allocated cons ---
;;; Pushes 2 dnodes (32 bytes) onto the control stack:
;;;   [header][nil-pad][CDR][CAR]
;;; The header is a value-cell header with element-count=3 so the GC
;;; scans all 3 node slots (nil-pad, CDR, CAR) after the header.

(define-arm64-vinsn (make-stack-cons :predicatable)
    (((dest :lisp))
     ((car :lisp) (cdr :lisp))
     ((header :u64)))
  (movz header (:$ 3))
  (movk header (:$ (:apply ash arm64::subtag-value-cell 8)) (:lsl 48))
  (sub sp sp (:$ 32))
  (str header (:@ sp (:$ 0)))
  (str rnil (:@ sp (:$ 8)))
  (stp cdr car (:@ sp (:$ 16)))
  (add dest sp (:$ (:apply + arm64::dnode-size arm64::cons-bias)))
  (movk dest (:$ (:apply ash arm64::tag-cons 8)) (:lsl 48)))


;;; --- Value cell (heap-allocated) ---
;;; Layout: [header @ allocptr+0] [value @ allocptr+8].
;;; Tagged pointer = allocptr + misc-bias(8), tag-value-cell in top byte.

(define-arm64-vinsn make-vcell (((dest :lisp))
                                ((closed (:lisp :ne dest)))
                                ((header :u64)))
  (mov header (:$ arm64::value-cell-header))
  (sub allocptr allocptr (:$ arm64::value-cell.size))
  (cmp allocptr allocbase)
  (b.hi :no-trap)
  (hlt (:$ 0))
  :no-trap
  (stp header closed (:@ allocptr (:$ 0)))
  (add dest allocptr (:$ arm64::misc-bias))
  (movk dest (:$ (:apply ash arm64::tag-value-cell 8)) (:lsl 48)))


;;; --- Value cell (stack-allocated) ---
;;; Push header + value onto control stack as one dnode (16 bytes).

(define-arm64-vinsn (make-stack-vcell :predicatable)
    (((dest :lisp))
     ((closed :lisp))
     ((header :u64)))
  (mov header (:$ arm64::value-cell-header))
  (stp header closed (:@! sp (:$ -16)))
  (add dest sp (:$ arm64::misc-bias))
  (movk dest (:$ (:apply ash arm64::tag-value-cell 8)) (:lsl 48)))


;;; --- Generic misc object allocation (fixed size) ---
;;; Allocate a uvector of known physical data size.
;;; Rheader is a register containing the pre-built header word.
;;; nbytes is the compile-time-constant physical data size in bytes.
;;; Total allocation = dnode-aligned(header(8) + nbytes).
;;; Reference tag is derived at runtime from the header subtag:
;;;   tag = subtag XOR #xC0 (toggles bits 6,7: header→reference).

(define-arm64-vinsn %alloc-misc-fixed (((dest :lisp))
                                       ((Rheader :u64)
                                        (nbytes :u32const))
                                       ((tag :u64)))
  (sub allocptr allocptr (:$ (:apply logand #xFFF
                                     (:apply logand
                                             (:apply lognot 15)
                                             (:apply + 23 nbytes)))))
  ((:pred > (:apply logand (:apply lognot 15) (:apply + 23 nbytes)) #xFFF)
   (sub allocptr allocptr (:$ (:apply logand #xFFF000
                                      (:apply logand
                                              (:apply lognot 15)
                                              (:apply + 23 nbytes))))))
  (cmp allocptr allocbase)
  (b.hi :no-trap)
  (hlt (:$ 0))
  :no-trap
  (str Rheader (:@ allocptr (:$ 0)))
  (add dest allocptr (:$ arm64::misc-bias))
  ;; Derive TBI reference tag from header subtag (in high byte).
  ;; pointer_tag = header_subtag XOR 0xC0.  Extract high byte, XOR, shift back.
  (lsr tag Rheader (:$ arm64::tag-shift))
  (eor tag tag (:$ #xC0))
  (lsl tag tag (:$ arm64::tag-shift))
  (orr dest dest tag))


;;; --- Generic gvector allocation with element initialization ---
;;; Like %alloc-misc-fixed but also pops nbytes/8 node values from
;;; the vstack and stores them into the newly allocated gvector.

(define-arm64-vinsn %arm64-gvector (((dest :lisp))
                                    ((Rheader :u64)
                                     (nbytes :u32const))
                                    ((immtemp0 :u64)
                                     (nodetemp :lisp)
                                     (tag :u64)))
  (sub allocptr allocptr (:$ (:apply logand #xFFF
                                     (:apply logand
                                             (:apply lognot 15)
                                             (:apply + 23 nbytes)))))
  ((:pred > (:apply logand (:apply lognot 15) (:apply + 23 nbytes)) #xFFF)
   (sub allocptr allocptr (:$ (:apply logand #xFFF000
                                      (:apply logand
                                              (:apply lognot 15)
                                              (:apply + 23 nbytes))))))
  (cmp allocptr allocbase)
  (b.hi :no-trap)
  (hlt (:$ 0))
  :no-trap
  (str Rheader (:@ allocptr (:$ 0)))
  (add dest allocptr (:$ arm64::misc-bias))
  ;; Derive TBI reference tag from header subtag (in high byte).
  (lsr tag Rheader (:$ arm64::tag-shift))
  (eor tag tag (:$ #xC0))
  (lsl tag tag (:$ arm64::tag-shift))
  (orr dest dest tag)
  ;; Initialize gvector elements from vstack (last pushed = lowest index)
  ((:not (:pred = nbytes 0))
   (mov immtemp0 (:$ nbytes))
   :loop
   (subs immtemp0 immtemp0 (:$ arm64::node-size))
   (ldr nodetemp (:@+ vsp (:$ arm64::node-size)))
   (str nodetemp (:@ dest immtemp0))
   (b.ne :loop)))


;;; --- C frame allocation (AAPCS64) ---
;;; Allocate a C call frame on the control stack.  The frame is disguised
;;; as a u64-vector so the GC can skip it.
;;; Layout: [header(8)][prevsp(8)][arg0(8)][arg1(8)]...
;;; Element count = (n-c-args + 2) & ~1 (even, for dnode alignment).
;;; Frame size = 8 + element-count * 8.

;;; Apple Silicon requires SP to be 16-byte aligned at all times.
;;; Total frame = (1 + n-elements) * 8.  For 16-byte alignment,
;;; (1 + n-elements) must be even, so n-elements must be ODD.
;;; Also: MOV from SP must use ADD (register 31 = XZR in ORR context).
(define-arm64-vinsn (alloc-aapcs64-c-frame :predicatable)
    (()
     ((n-c-args :u16const))
     ((header :u64)
      (prevsp :imm)))
  (movz header (:$ (:apply logior (:apply logandc2 (:apply + 2 n-c-args) 1) 1)))
  (movk header (:$ (:apply ash arm64::subtag-u64-vector 8)) (:lsl 48))
  (add prevsp sp (:$ 0))
  (sub sp sp (:$ (:apply + 8
                         (:apply ash
                                 (:apply logior (:apply logandc2 (:apply + 2 n-c-args) 1) 1)
                                 3))))
  (str header (:@ sp (:$ 0)))
  (str prevsp (:@ sp (:$ 8))))


;;; Variable-size C frame: n-c-args is a lisp fixnum (= raw count since
;;; fixnumshift=0 on ARM64).

(define-arm64-vinsn (alloc-variable-aapcs64-c-frame :predicatable)
    (()
     ((n-c-args :lisp))
     ((header :u64)
      (size :imm)
      (prevsp :imm)))
  ;; element-count = ((n-c-args + 2) & ~1) | 1  → always odd for 16-byte alignment
  (add size n-c-args (:$ 2))
  (bic size size (:$ 1))
  (orr size size (:$ 1))
  (add prevsp sp (:$ 0))
  ;; header = (subtag-u64-vector << 56) | element-count
  (mov header size)
  (movk header (:$ (:apply ash arm64::subtag-u64-vector 8)) (:lsl 48))
  ;; frame-size = (element-count + 1) * 8  → always 16-byte aligned
  (add size size (:$ 1))
  (lsl size size (:$ arm64::word-shift))
  ;; sp -= frame-size
  (neg size size)
  (add sp sp size)
  (str header (:@ sp (:$ 0)))
  (str prevsp (:@ sp (:$ 8))))


;;; Discard C frame by restoring saved SP from offset 8.
;;; Must use ADD to write SP (register 31 = XZR in ORR context).

(define-arm64-vinsn (discard-c-frame :pop :discard :predicatable)
    (()
     ()
     ((temp :imm)))
  (ldr temp (:@ sp (:$ 8)))
  (add sp temp (:$ 0)))


;;; ======================================================================
;;; Chunk 10: Control flow + argument handling
;;; Jumps, conditional branches, arg count checking, optional arg
;;; defaulting, nargs manipulation, vstack push/pop, lexpr args,
;;; GPR copy, and vstack frame access.
;;; ======================================================================

;;; --- Jumps and calls ---

(define-arm64-vinsn (jump :jump :predicatable)
    (()
     ((label :label)))
  (b label))

(define-arm64-vinsn (call-label :call) (()
                                        ((label :label)))
  (bl label))

(define-arm64-vinsn (non-barrier-jump) (()
                                        ((label :label)))
  (b label))


;;; --- Conditional branches ---
;;; (:? crbit) = branch if condition true, (:~ crbit) = branch if false.

(define-arm64-vinsn (cbranch-true :branch) (()
                                            ((label :label)
                                             (crf :crf)
                                             (crbit :u8const)))
  (b (:? crbit) label))

(define-arm64-vinsn (cbranch-false :branch) (()
                                             ((label :label)
                                              (crf :crf)
                                              (crbit :u8const)))
  (b (:~ crbit) label))


;;; --- cond->boolean: convert condition code to T or NIL ---
;;; ARM64: no conditional ADD; use branch-around.
;;; T = rnil + t-offset with tag-symbol in top byte.

(define-arm64-vinsn cond->boolean (((dest :imm))
                                   ((cond :u8const)))
  (mov dest rnil)
  (b (:~ cond) :done)
  (add dest dest (:$ arm64::t-offset))
  (movk dest (:$ (:apply ash arm64::tag-symbol 8)) (:lsl 48))
  :done)


;;; --- Indirect computed jump (jump tables) ---
;;; ARM64 cannot write PC directly.  Use ADR to get the table base
;;; address, add scaled index, then BR.  Each table entry is a
;;; 4-byte B instruction, so scale by 4.

(define-arm64-vinsn (ijmp :branch) (()
                                    ((idx :u32))
                                    ((temp :u64)))
  (adr temp :base)
  (add temp temp (:lsl idx (:$ 2)))
  (br temp)
  :base)


;;; --- Argument count checking ---
;;; On ARM64, nargs = n * node-size = n * 8.

(define-arm64-vinsn check-exact-nargs (()
                                       ((n :u16const)))
  (cmp nargs (:$ (:apply ash n arm64::word-shift)))
  (b.eq :ok)
  (uuo-error-wrong-nargs)
  :ok)

(define-arm64-vinsn check-min-nargs (()
                                     ((min :u16const)))
  (cmp nargs (:$ (:apply ash min arm64::word-shift)))
  (b.hs :ok)
  (uuo-error-wrong-nargs)
  :ok)

(define-arm64-vinsn check-max-nargs (()
                                     ((max :u16const)))
  (cmp nargs (:$ (:apply ash max arm64::word-shift)))
  (b.ls :ok)
  (uuo-error-wrong-nargs)
  :ok)

;;; Large nargs check: for values that don't fit in CMP imm12 (>4095).
;;; Load the comparison value into imm0 first.
(define-arm64-vinsn check-min-nargs-large (()
                                           ((min :u16const))
                                           ((temp (:u64 #.arm64::imm0))))
  (mov temp (:$ (:apply ash min arm64::word-shift)))
  (cmp nargs temp)
  (b.hs :ok)
  (uuo-error-wrong-nargs)
  :ok)

(define-arm64-vinsn check-max-nargs-large (()
                                           ((max :u16const))
                                           ((temp (:u64 #.arm64::imm0))))
  (mov temp (:$ (:apply ash max arm64::word-shift)))
  (cmp nargs temp)
  (b.ls :ok)
  (uuo-error-wrong-nargs)
  :ok)

;;; default-optionals: call .SPdefault-optional-args subprim.
;;; On entry, nargs has actual count; n is expected total (required + optional).
;;; The subprim vpushes all argregs and initializes unfilled slots to nil.
(define-arm64-vinsn (default-optionals :call :subprim) (()
                                                        ((n :u16const))
                                                        ((temp (:u64 #.arm64::imm0))))
  (mov temp (:$ (:apply ash n arm64::word-shift)))
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPdefault-optional-args))))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))


;;; --- Default optional arguments ---
;;; Shift arg registers down and set defaults to nil.
;;; On ARM64, use rnil instead of (:$ nil-value).

(define-arm64-vinsn default-1-arg (()
                                   ((min :u16const)))
  (cmp nargs (:$ (:apply ash min arm64::word-shift)))
  (b.ne :done)
  ;; Got exactly min args; default arg_z to nil
  ((:pred >= min 3)
   (str arg_x (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred >= min 2)
   (mov arg_x arg_y))
  ((:pred >= min 1)
   (mov arg_y arg_z))
  (mov arg_z rnil)
  :done)

(define-arm64-vinsn default-2-args (()
                                    ((min :u16const)))
  (cmp nargs (:$ (:apply ash (:apply 1+ min) arm64::word-shift)))
  (b.gt :done)
  (b.eq :one)
  ;; Got min args: default both arg_y and arg_z
  ((:pred >= min 3)
   (str arg_x (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred >= min 2)
   (str arg_y (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred >= min 1)
   (mov arg_x arg_z))
  (mov arg_y rnil)
  (b :last)
  :one
  ;; Got min+1 args: arg_y supplied, default arg_z
  ((:pred >= min 2)
   (str arg_x (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred >= min 1)
   (mov arg_x arg_y))
  (mov arg_y arg_z)
  :last
  (mov arg_z rnil)
  :done)

(define-arm64-vinsn default-3-args (()
                                    ((min :u16const)))
  (cmp nargs (:$ (:apply ash min arm64::word-shift)))
  (b.eq :none)
  (cmp nargs (:$ (:apply ash (:apply + 2 min) arm64::word-shift)))
  (b.gt :done)
  (b.eq :two)
  ;; Got min+1 args: 1st optional supplied
  ((:pred >= min 2)
   (str arg_x (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred >= min 1)
   (str arg_y (:@! vsp (:$ (- arm64::node-size)))))
  (mov arg_x arg_z)
  (b :last-2)
  :two
  ;; Got min+2 args: 1st and 2nd optional supplied
  ((:pred >= min 1)
   (str arg_x (:@! vsp (:$ (- arm64::node-size)))))
  (mov arg_x arg_y)
  (mov arg_y arg_z)
  (b :last-1)
  :none
  ;; Got exactly min args: all 3 optional default
  ((:pred >= min 3)
   (str arg_x (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred >= min 2)
   (str arg_y (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred >= min 1)
   (str arg_z (:@! vsp (:$ (- arm64::node-size)))))
  (mov arg_x rnil)
  :last-2
  (mov arg_y rnil)
  :last-1
  (mov arg_z rnil)
  :done)


;;; --- Nargs manipulation ---

(define-arm64-vinsn (set-nargs :predicatable)
    (()
     ((n :s16const)))
  (mov nargs (:$ (:apply ash n arm64::word-shift))))

;;; Adjust nargs after accounting for nfixed required args.
(define-arm64-vinsn (scale-nargs :predicatable)
    (()
     ((nfixed :s16const)))
  ((:pred > nfixed 0)
   (sub nargs nargs (:$ (:apply ash nfixed arm64::word-shift)))))


;;; --- Vstack push/pop ---

(define-arm64-vinsn (vpush-register :push :node :vsp :predicatable)
    (()
     ((reg :lisp)))
  (str reg (:@! vsp (:$ (- arm64::node-size)))))

(define-arm64-vinsn (vpop-register :pop :node :vsp :predicatable)
    (((dest :lisp))
     ())
  (ldr dest (:@+ vsp (:$ arm64::node-size))))


;;; --- Push/pop argument registers ---
;;; ARM64: no conditional loads/stores; use branch-around with fallthrough.

(define-arm64-vinsn (vpush-argregs :push :node :vsp) (()
                                                      ((num-fixed-args :u16const)))
  ((:pred = num-fixed-args 0)
   (cmp nargs (:$ 0))
   (b.eq :done))
  ((:pred < num-fixed-args 2)
   (cmp nargs (:$ (:apply ash 2 arm64::word-shift)))
   (b.lo :one)
   (b.eq :two)
   (str arg_x (:@! vsp (:$ (- arm64::node-size))))
   :two
   (str arg_y (:@! vsp (:$ (- arm64::node-size))))
   :one
   (str arg_z (:@! vsp (:$ (- arm64::node-size))))
   :done)
  ((:pred = num-fixed-args 2)
   (cmp nargs (:$ (:apply ash 2 arm64::word-shift)))
   (b.eq :two-only)
   (str arg_x (:@! vsp (:$ (- arm64::node-size))))
   :two-only
   (str arg_y (:@! vsp (:$ (- arm64::node-size))))
   (str arg_z (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred > num-fixed-args 2)
   (str arg_x (:@! vsp (:$ (- arm64::node-size))))
   (str arg_y (:@! vsp (:$ (- arm64::node-size))))
   (str arg_z (:@! vsp (:$ (- arm64::node-size))))))

(define-arm64-vinsn (pop-argument-registers :pop :node :vsp) (()
                                                              ())
  (cmp nargs (:$ 0))
  (b.eq :done)
  (ldr arg_z (:@+ vsp (:$ arm64::node-size)))
  (cmp nargs (:$ (:apply ash 2 arm64::word-shift)))
  (b.lo :done)
  (ldr arg_y (:@+ vsp (:$ arm64::node-size)))
  (b.eq :done)
  (ldr arg_x (:@+ vsp (:$ arm64::node-size)))
  :done)


;;; --- Save lexpr arg registers ---
;;; Push supplied arg regs, push extra-args count, set up lexpr frame.
;;; ARM64 lisp frame is 2-slot (entry-vsp + lr), no marker or fn save.

(define-arm64-vinsn save-lexpr-argregs
    (()
     ((min-fixed :u16const))
     ((entry-vsp (:u64 #.arm64::imm1))
      (arg-temp (:u64 #.arm64::imm0))
      (preserve (:u64 #.arm64::nargs))
      (other-temp :imm)))
  ;; Push arg regs based on nargs and min-fixed
  ((:pred >= min-fixed $numarm64argregs)
   (str arg_x (:@! vsp (:$ (- arm64::node-size))))
   (str arg_y (:@! vsp (:$ (- arm64::node-size))))
   (str arg_z (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred = min-fixed 2)
   (cmp nargs (:$ (:apply ash 2 arm64::word-shift)))
   (b.eq :skip-x-2)
   (str arg_x (:@! vsp (:$ (- arm64::node-size))))
   :skip-x-2
   (str arg_y (:@! vsp (:$ (- arm64::node-size))))
   (str arg_z (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred = min-fixed 1)
   (cmp nargs (:$ (:apply ash 2 arm64::word-shift)))
   (b.lo :one-1)
   (b.eq :two-1)
   (str arg_x (:@! vsp (:$ (- arm64::node-size))))
   :two-1
   (str arg_y (:@! vsp (:$ (- arm64::node-size))))
   :one-1
   (str arg_z (:@! vsp (:$ (- arm64::node-size)))))
  ((:pred = min-fixed 0)
   (cmp nargs (:$ 0))
   (b.eq :done-push)
   (cmp nargs (:$ (:apply ash 2 arm64::word-shift)))
   (b.lo :one-0)
   (b.eq :two-0)
   (str arg_x (:@! vsp (:$ (- arm64::node-size))))
   :two-0
   (str arg_y (:@! vsp (:$ (- arm64::node-size))))
   :one-0
   (str arg_z (:@! vsp (:$ (- arm64::node-size))))
   :done-push)
  ;; Push extra-args count (nargs - min-fixed*node-size)
  ((:pred = min-fixed 0)
   (str nargs (:@! vsp (:$ (- arm64::node-size)))))
  ((:not (:pred = min-fixed 0))
   (sub arg-temp nargs (:$ (:apply ash min-fixed arm64::word-shift)))
   (str arg-temp (:@! vsp (:$ (- arm64::node-size)))))
  ;; entry-vsp = vsp + nargs + node-size
  (add entry-vsp vsp nargs)
  (add entry-vsp entry-vsp (:$ arm64::node-size))
  ;; Load ret1valaddr kernel global (offset within LDUR range)
  (ldur other-temp (:@ rnil (:$ (arm64::%kernel-global 'arm64::ret1valaddr))))
  (cmp other-temp lr)
  ;; Save lisp frame
  (stp entry-vsp lr (:@! sp (:$ (- arm64::lisp-frame.size))))
  (stp nfn x29 (:@ sp (:$ arm64::lisp-frame.savefn)))
  (add x29 sp (:$ 0))
  (b.ne :not-multiple)
  ;; lr == ret1valaddr: multi-value lexpr return
  (sub arg-temp rnil (:$ (- (arm64::%kernel-global 'arm64::lexpr-return))))
  (ldr arg-temp (:@ arg-temp (:$ 0)))
  (stp entry-vsp arg-temp (:@! sp (:$ (- arm64::lisp-frame.size))))
  (stp nfn x29 (:@ sp (:$ arm64::lisp-frame.savefn)))
  (add x29 sp (:$ 0))
  (mov lr other-temp)
  (b :done-lexpr)
  :not-multiple
  ;; lr != ret1valaddr: single-value lexpr return
  (sub arg-temp rnil (:$ (- (arm64::%kernel-global 'arm64::lexpr-return1v))))
  (ldr lr (:@ arg-temp (:$ 0)))
  :done-lexpr)


;;; --- GPR copy ---

(define-arm64-vinsn (copy-node-gpr :predicatable)
    (((dest :lisp))
     ((src :lisp)))
  ((:not (:pred =
                (:apply %hard-regspec-value dest)
                (:apply %hard-regspec-value src)))
   (mov dest src)))

(define-arm64-vinsn (copy-gpr :predicatable)
    (((dest t))
     ((src t)))
  ((:not (:pred =
                (:apply %hard-regspec-value dest)
                (:apply %hard-regspec-value src)))
   (mov dest src)))


;;; --- Vstack management ---

(define-arm64-vinsn (vstack-discard :vsp :pop :discard :predicatable)
    (()
     ((nwords :u32const)))
  ((:not (:pred = nwords 0))
   (add vsp vsp (:$ (:apply ash nwords arm64::word-shift)))))

;;; Load from vstack frame.  Offset from current vsp =
;;; cur-vsp - node-size - frame-offset.
(define-arm64-vinsn (vframe-load :predicatable)
    (((dest :lisp))
     ((frame-offset :u16const)
      (cur-vsp :u16const)))
  ((:pred < (:apply - (:apply - cur-vsp arm64::node-size) frame-offset) 32761)
   (ldr dest (:@ vsp (:$ (:apply - (:apply - cur-vsp arm64::node-size) frame-offset)))))
  ((:pred >= (:apply - (:apply - cur-vsp arm64::node-size) frame-offset) 32761)
   (mov dest (:$ (:apply - (:apply - cur-vsp arm64::node-size) frame-offset)))
   (ldr dest (:@ vsp dest))))

;;; Store to vstack frame.
(define-arm64-vinsn (vframe-store :predicatable)
    (()
     ((src :lisp)
      (frame-offset :u16const)
      (cur-vsp :u16const)))
  ((:pred < (:apply - (:apply - cur-vsp arm64::node-size) frame-offset) 32761)
   (str src (:@ vsp (:$ (:apply - (:apply - cur-vsp arm64::node-size) frame-offset)))))
  ((:pred >= (:apply - (:apply - cur-vsp arm64::node-size) frame-offset) 32761)
   ;; Large offset: temporarily save rcontext on vstack to use as temp
   (str rcontext (:@! vsp (:$ (- arm64::node-size))))
   (mov rcontext (:$ (:apply - cur-vsp frame-offset)))
   (str src (:@ vsp rcontext))
   (ldr rcontext (:@+ vsp (:$ arm64::node-size)))))

;;; Adjust vsp by a signed constant.
(define-arm64-vinsn (adjust-vsp :predicatable :vsp :pop :discard)
    (()
     ((amount :s16const)))
  (add vsp vsp (:$ amount)))


;;; ======================================================================
;;; Chunk 11: Symbol/function ops + memory access
;;; Symbol value lookup (via TLB), function lookup, known-symbol/function
;;; calls and jumps, constant loading, LRI, untagged memory access,
;;; macptr operations, lisp-word-ref.
;;; ======================================================================

;;; --- Symbol value operations ---

;;; ref-symbol-value: checked symbol value lookup (signals unbound).
;;; Delegates to .SPspecrefcheck subprim.
(define-arm64-vinsn (ref-symbol-value :call :subprim)
    (((val :lisp))
     ((sym (:lisp (:ne val)))))
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPspecrefcheck))))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))

;;; ref-symbol-value-inline: inline TLB lookup with unbound check.
;;; TBI: symbol fields accessed via tagged pointer (TBI ignores tag byte).
(define-arm64-vinsn ref-symbol-value-inline (((dest :lisp))
                                             ((src (:lisp (:ne dest))))
                                             ((table :imm)
                                              (idx :imm)))
  (ldr idx (:@ src (:$ arm64::symbol.binding-index)))
  (ldr table (:@ rcontext (:$ arm64::tcr.tlb-limit)))
  (cmp idx table)
  (b.lo :in-range)
  (mov idx (:$ 0))
  :in-range
  (ldr table (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (ldr dest (:@ table idx))
  (lsr idx dest (:$ arm64::tag-shift))
  (cmp idx (:$ arm64::tag-no-thread-local-binding))
  (b.ne :have-val)
  (ldr dest (:@ src (:$ arm64::symbol.vcell)))
  :have-val
  (lsr idx dest (:$ arm64::tag-shift))
  (cmp idx (:$ arm64::tag-unbound))
  (b.ne :bound)
  (uuo-error-unbound src)
  :bound)

;;; %ref-symbol-value: unchecked symbol value lookup (no unbound error).
(define-arm64-vinsn (%ref-symbol-value :call :subprim)
    (((val :lisp))
     ((sym (:lisp (:ne val)))))
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPspecref))))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))

;;; %ref-symbol-value-inline: inline TLB lookup, no unbound check.
(define-arm64-vinsn %ref-symbol-value-inline (((dest :lisp))
                                              ((src (:lisp (:ne dest))))
                                              ((table :imm)
                                               (idx :imm)))
  (ldr idx (:@ src (:$ arm64::symbol.binding-index)))
  (ldr table (:@ rcontext (:$ arm64::tcr.tlb-limit)))
  (cmp idx table)
  (b.lo :in-range)
  (mov idx (:$ 0))
  :in-range
  (ldr table (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (ldr dest (:@ table idx))
  (lsr idx dest (:$ arm64::tag-shift))
  (cmp idx (:$ arm64::tag-no-thread-local-binding))
  (b.ne :done)
  (ldr dest (:@ src (:$ arm64::symbol.vcell)))
  :done)

;;; setq-special: set symbol value via subprim.
(define-arm64-vinsn (setq-special :call :subprim)
    (()
     ((sym :lisp)
      (val :lisp)))
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPspecset))))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))


;;; --- Symbol function lookup ---

;;; symbol-function: load function cell, verify it's a function.
;;; On ARM64 TBI each uvector type has a unique reference tag, so
;;; we check tag-function directly in the tag byte.
(define-arm64-vinsn symbol-function (((val :lisp))
                                     ((sym (:lisp (:ne val))))
                                     ((tag :u64)))
  (ldr val (:@ sym (:$ arm64::symbol.fcell)))
  (lsr tag val (:$ arm64::tag-shift))
  (cmp tag (:$ arm64::tag-function))
  (b.eq :defined)
  (uuo-error-udf sym)
  :defined)


;;; --- %symbol->symptr ---
;;; Convert a possible NIL or symbol to a symbol pointer.
;;; NIL is not tagged as a symbol — its symbol structure is at nilsym-offset.
(define-arm64-vinsn %symbol->symptr (((dest :lisp))
                                     ((src :lisp))
                                     ((tag :u64)))
  (cmp src rnil)
  (b.eq :nilsym)
  (lsr tag src (:$ arm64::tag-shift))
  (cmp tag (:$ arm64::tag-symbol))
  (b.eq :symbol)
  (uuo-cerror-reg-not-xtype src (:$ arm64::subtag-symbol))
  :symbol
  ((:not (:pred =
                (:apply %hard-regspec-value dest)
                (:apply %hard-regspec-value src)))
   (mov dest src))
  (b :done)
  :nilsym
  (add dest rnil (:$ arm64::nilsym-offset))
  :done)


;;; --- istruct-type ---
;;; Return the first data slot of an istruct, or NIL if not an istruct.
(define-arm64-vinsn istruct-type (((dest :lisp))
                                  ((val :lisp))
                                  ((tag :u64)))
  (lsr tag val (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :not-istruct)
  (ldur tag (:@ val (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-istruct))
  (b.ne :not-istruct)
  (ldr dest (:@ val (:$ arm64::misc-data-offset)))
  (b :done)
  :not-istruct
  (mov dest rnil)
  :done)


;;; --- Function calls and jumps ---

;;; call-known-symbol: fname (x9) holds the symbol; load fcell, get entrypoint, call.
(define-arm64-vinsn (call-known-symbol :call) (((result (:lisp arm64::arg_z)))
                                               ())
  (ldr nfn (:@ fname (:$ arm64::symbol.fcell)))
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (blr lr))

;;; jump-known-symbol: tail-call via symbol.
(define-arm64-vinsn (jump-known-symbol :jumplr) (()
                                                 ())
  (ldr nfn (:@ fname (:$ arm64::symbol.fcell)))
  (ldr imm2 (:@ nfn (:$ arm64::function.entrypoint)))
  (br imm2))

;;; call-known-function: nfn already holds the function object.
(define-arm64-vinsn (call-known-function :call) (()
                                                 ())
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (blr lr))

;;; jump-known-function: tail-call via function object in nfn.
(define-arm64-vinsn (jump-known-function :jumplr) (()
                                                   ())
  (ldr imm2 (:@ nfn (:$ arm64::function.entrypoint)))
  (br imm2))


;;; --- Loading constants ---

;;; load-nil: use rnil register.
(define-arm64-vinsn (load-nil :constant-ref :predicatable)
    (((dest t))
     ())
  (mov dest rnil))

;;; load-t: nil + t-offset.
(define-arm64-vinsn (load-t :constant-ref :predicatable)
    (((dest t))
     ())
  (add dest rnil (:$ arm64::t-offset)))

;;; ref-constant: load from function's constant pool.
;;; ARM64 uses nfn instead of fn.  Offset = misc-data-offset + (index+2)*8.
(define-arm64-vinsn (ref-constant :constant-ref :predicatable)
    (((dest :lisp))
     ((src :s16const)))
  (ldr dest (:@ nfn (:$ (:apply + arm64::misc-data-offset (:apply ash (:apply + src 2) arm64::word-shift))))))

;;; ref-indexed-constant: load from function via register index.
(define-arm64-vinsn (ref-indexed-constant :predicatable)
    (((dest :lisp))
     ((idxreg :s64)))
  (ldr dest (:@ nfn idxreg)))

;;; load-character-constant: build an immediate character in a register.
;;; ARM64 TBI: character = (code << charcode-shift) with tag-character in top byte.
(define-arm64-vinsn (load-character-constant :predicatable)
    (((dest :lisp))
     ((code :u32const)))
  (movz dest (:$ (:apply logand #xffff (:apply ash code arm64::charcode-shift))))
  ((:pred /= (:apply logand #xffff (:apply ash code (:apply - arm64::charcode-shift 16))) 0)
   (movk dest (:$ (:apply logand #xffff (:apply ash code (:apply - arm64::charcode-shift 16)))) (:lsl 16)))
  (movk dest (:$ (:apply ash arm64::tag-character 8)) (:lsl 48)))

;;; lri: load register immediate (arbitrary 64-bit value).
;;; Uses movz + up to 3 movk instructions.
(define-arm64-vinsn (lri :constant-ref :predicatable)
    (((dest :imm))
     ((intval :u64const))
     ())
  (movz dest (:$ (:apply logand #xffff intval)))
  ((:pred /= (:apply logand #xffff (:apply ash intval -16)) 0)
   (movk dest (:$ (:apply logand #xffff (:apply ash intval -16))) (:lsl 16)))
  ((:pred /= (:apply logand #xffff (:apply ash intval -32)) 0)
   (movk dest (:$ (:apply logand #xffff (:apply ash intval -32))) (:lsl 32)))
  ((:pred /= (:apply logand #xffff (:apply ash intval -48)) 0)
   (movk dest (:$ (:apply logand #xffff (:apply ash intval -48))) (:lsl 48))))


;;; --- Lisp word reference ---

(define-arm64-vinsn (lisp-word-ref :predicatable)
    (((dest t))
     ((base t)
      (offset t)))
  (ldr dest (:@ base offset)))

(define-arm64-vinsn (lisp-word-ref-c :predicatable)
    (((dest t))
     ((base t)
      (offset :s16const)))
  ((:pred >= offset 0)
   (ldr dest (:@ base (:$ offset))))
  ((:pred < offset 0)
   (ldur dest (:@ base (:$ offset)))))

;;; load-indexed-node: load a node from base + signed constant offset.
(define-arm64-vinsn (load-indexed-node :predicatable)
    (((node :lisp))
     ((base :lisp)
      (offset :s16const)))
  ((:pred >= offset 0)
   (ldr node (:@ base (:$ offset))))
  ((:pred < offset 0)
   (ldur node (:@ base (:$ offset)))))


;;; --- Untagged memory access ---

;;; Natural-width (64-bit on ARM64) memory ref/set.
(define-arm64-vinsn (mem-ref-c-fullword :predicatable)
    (((dest :u64))
     ((src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (ldr dest (:@ src (:$ index))))
  ((:pred < index 0)
   (ldur dest (:@ src (:$ index)))))

(define-arm64-vinsn (mem-ref-c-signed-fullword :predicatable)
    (((dest :s64))
     ((src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (ldr dest (:@ src (:$ index))))
  ((:pred < index 0)
   (ldur dest (:@ src (:$ index)))))

(define-arm64-vinsn (mem-ref-c-natural :predicatable)
    (((dest :u64))
     ((src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (ldr dest (:@ src (:$ index))))
  ((:pred < index 0)
   (ldur dest (:@ src (:$ index)))))

(define-arm64-vinsn (mem-ref-fullword :predicatable)
    (((dest :u64))
     ((src :address)
      (index :s64)))
  (ldr dest (:@ src index)))

(define-arm64-vinsn (mem-ref-signed-fullword :predicatable)
    (((dest :s64))
     ((src :address)
      (index :s64)))
  (ldr dest (:@ src index)))

(define-arm64-vinsn (mem-ref-natural :predicatable)
    (((dest :u64))
     ((src :address)
      (index :s64)))
  (ldr dest (:@ src index)))

;;; 16-bit memory ref.
(define-arm64-vinsn (mem-ref-c-u16 :predicatable)
    (((dest :u16))
     ((src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (ldrh dest (:@ src (:$ index))))
  ((:pred < index 0)
   (ldurh dest (:@ src (:$ index)))))

(define-arm64-vinsn (mem-ref-u16 :predicatable)
    (((dest :u16))
     ((src :address)
      (index :s64)))
  (ldrh dest (:@ src index)))

(define-arm64-vinsn (mem-ref-c-s16 :predicatable)
    (((dest :s16))
     ((src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (ldrsh dest (:@ src (:$ index))))
  ((:pred < index 0)
   (ldursh dest (:@ src (:$ index)))))

(define-arm64-vinsn (mem-ref-s16 :predicatable)
    (((dest :s16))
     ((src :address)
      (index :s64)))
  (ldrsh dest (:@ src index)))

;;; 8-bit memory ref.
(define-arm64-vinsn (mem-ref-c-u8 :predicatable)
    (((dest :u8))
     ((src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (ldrb dest (:@ src (:$ index))))
  ((:pred < index 0)
   (ldurb dest (:@ src (:$ index)))))

(define-arm64-vinsn (mem-ref-u8 :predicatable)
    (((dest :u8))
     ((src :address)
      (index :s64)))
  (ldrb dest (:@ src index)))

(define-arm64-vinsn (mem-ref-c-s8 :predicatable)
    (((dest :s8))
     ((src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (ldrsb dest (:@ src (:$ index))))
  ((:pred < index 0)
   (ldursb dest (:@ src (:$ index)))))

(define-arm64-vinsn (mem-ref-s8 :predicatable)
    (((dest :s8))
     ((src :address)
      (index :s64)))
  (ldrsb dest (:@ src index)))

;;; Bit memory ref.
(define-arm64-vinsn (mem-ref-c-bit :predicatable)
    (((dest :u8))
     ((src :address)
      (byte-index :s16const)
      (bit-shift :u8const)))
  (ldrb dest (:@ src (:$ byte-index)))
  (lsr dest dest (:$ bit-shift))
  (and dest dest (:$ 1)))

(define-arm64-vinsn (mem-ref-c-bit-fixnum :predicatable)
    (((dest :lisp))
     ((src :address)
      (byte-index :s16const)
      (bit-shift :u8const))
     ((byteval :u8)))
  (ldrb byteval (:@ src (:$ byte-index)))
  (lsr byteval byteval (:$ bit-shift))
  (and dest byteval (:$ 1)))

;;; Double-float memory ref/set.
(define-arm64-vinsn (mem-ref-c-double-float :predicatable)
    (((dest :double-float))
     ((src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (ldr dest (:@ src (:$ index))))
  ((:pred < index 0)
   (ldur dest (:@ src (:$ index)))))

(define-arm64-vinsn (mem-ref-double-float :predicatable)
    (((dest :double-float)
      (src :address))
     ((src :address)
      (index :lisp)))
  (add src src index)
  (ldr dest (:@ src (:$ 0))))

(define-arm64-vinsn (mem-set-c-double-float :predicatable)
    (()
     ((val :double-float)
      (src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (str val (:@ src (:$ index))))
  ((:pred < index 0)
   (stur val (:@ src (:$ index)))))

(define-arm64-vinsn (mem-set-double-float :predicatable)
    (()
     ((val :double-float)
      (src :address)
      (index :s64))
     ((addr :u64)))
  (add addr src index)
  (str val (:@ addr (:$ 0))))

;;; Single-float memory ref/set.
(define-arm64-vinsn (mem-ref-c-single-float :predicatable)
    (((dest :single-float))
     ((src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (ldr dest (:@ src (:$ index))))
  ((:pred < index 0)
   (ldur dest (:@ src (:$ index)))))

(define-arm64-vinsn (mem-ref-single-float :predicatable)
    (((dest :single-float)
      (src :address))
     ((src :address)
      (index :lisp)))
  (add src src index)
  (ldr dest (:@ src (:$ 0))))

(define-arm64-vinsn (mem-set-c-single-float :predicatable)
    (()
     ((val :single-float)
      (src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (str val (:@ src (:$ index))))
  ((:pred < index 0)
   (stur val (:@ src (:$ index)))))

(define-arm64-vinsn (mem-set-single-float :predicatable)
    (()
     ((val :single-float)
      (src :address)
      (index :s64))
     ((temp :address)))
  (add temp src index)
  (str val (:@ temp (:$ 0))))

;;; Address/fullword/halfword/byte memory set.
(define-arm64-vinsn (mem-set-c-address :predicatable)
    (()
     ((val :address)
      (src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (str val (:@ src (:$ index))))
  ((:pred < index 0)
   (stur val (:@ src (:$ index)))))

(define-arm64-vinsn (mem-set-address :predicatable)
    (()
     ((val :address)
      (src :address)
      (index :s64)))
  (str val (:@ src index)))

(define-arm64-vinsn (mem-set-c-fullword :predicatable)
    (()
     ((val :u64)
      (src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (str val (:@ src (:$ index))))
  ((:pred < index 0)
   (stur val (:@ src (:$ index)))))

(define-arm64-vinsn (mem-set-fullword :predicatable)
    (()
     ((val :u64)
      (src :address)
      (index :s64)))
  (str val (:@ src index)))

(define-arm64-vinsn (mem-set-c-halfword :predicatable)
    (()
     ((val :u16)
      (src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (strh val (:@ src (:$ index))))
  ((:pred < index 0)
   (sturh val (:@ src (:$ index)))))

(define-arm64-vinsn (mem-set-halfword :predicatable)
    (()
     ((val :u16)
      (src :address)
      (index :s64)))
  (strh val (:@ src index)))

(define-arm64-vinsn (mem-set-c-byte :predicatable)
    (()
     ((val :u8)
      (src :address)
      (index :s16const)))
  ((:pred >= index 0)
   (strb val (:@ src (:$ index))))
  ((:pred < index 0)
   (sturb val (:@ src (:$ index)))))

(define-arm64-vinsn (mem-set-byte :predicatable)
    (()
     ((val :u8)
      (src :address)
      (index :s64)))
  (strb val (:@ src index)))

;;; Bit set operations.
(define-arm64-vinsn (mem-set-c-bit-0 :predicatable)
    (()
     ((src :address)
      (byte-index :s16const)
      (mask :u8const))
     ((val :u8)))
  (ldrb val (:@ src (:$ byte-index)))
  (and val val (:$ (:apply lognot mask)))
  (strb val (:@ src (:$ byte-index))))

(define-arm64-vinsn (mem-set-c-bit-1 :predicatable)
    (()
     ((src :address)
      (byte-index :s16const)
      (mask :u8const))
     ((val :u8)))
  (ldrb val (:@ src (:$ byte-index)))
  (orr val val (:$ mask))
  (strb val (:@ src (:$ byte-index))))

(define-arm64-vinsn mem-set-c-bit (()
                                   ((src :address)
                                    (byte-index :s16const)
                                    (bit-index :u8const)
                                    (val :imm))
                                   ((byteval :u8)
                                    (mask :u8)))
  (mov mask (:$ 1))
  (lsl mask mask (:$ bit-index))
  (ldrb byteval (:@ src (:$ byte-index)))
  (cmp val (:$ 0))
  (b.eq :clear)
  (orr byteval byteval mask)
  (b :store)
  :clear
  (and byteval byteval (:$ (:apply lognot (:apply ash 1 bit-index))))
  :store
  (strb byteval (:@ src (:$ byte-index))))


;;; --- Macptr operations ---

;;; deref-macptr: extract the raw address from a macptr.
(define-arm64-vinsn (deref-macptr :predicatable)
    (((addr :address))
     ((src :lisp))
     ())
  (ldr addr (:@ src (:$ arm64::macptr.address))))

;;; set-macptr-address: store a raw address into a macptr.
(define-arm64-vinsn (set-macptr-address :predicatable)
    (()
     ((addr :address)
      (src :lisp))
     ())
  (str addr (:@ src (:$ arm64::macptr.address))))

;;; macptr->heap: allocate a macptr on the heap.
(define-arm64-vinsn macptr->heap (((dest :lisp))
                                  ((address :address))
                                  ((header :u64)))
  (mov header (:$ arm64::macptr-header))
  (sub allocptr allocptr (:$ arm64::macptr.size))
  (cmp allocptr allocbase)
  (b.hi :no-trap)
  (hlt (:$ 0))
  :no-trap
  (str header (:@ allocptr (:$ 0)))
  (add dest allocptr (:$ arm64::misc-bias))
  (movk dest (:$ (:apply ash arm64::tag-macptr 8)) (:lsl 48))
  (str address (:@ dest (:$ arm64::macptr.address)))
  ;; Zero domain and type fields
  (mov header (:$ 0))
  (str header (:@ dest (:$ arm64::macptr.domain)))
  (str header (:@ dest (:$ arm64::macptr.type))))

;;; macptr->stack: allocate a macptr on the control stack.
(define-arm64-vinsn (macptr->stack :predicatable)
    (((dest :lisp))
     ((address :address))
     ((header :u64)
      (zero :u64)))
  (mov header (:$ arm64::macptr-header))
  (mov zero (:$ 0))
  (sub sp sp (:$ arm64::macptr.size))
  (str header (:@ sp (:$ 0)))
  (str zero (:@ sp (:$ (:apply + arm64::misc-bias arm64::macptr.domain))))
  (str zero (:@ sp (:$ (:apply + arm64::misc-bias arm64::macptr.type))))
  (str address (:@ sp (:$ (:apply + arm64::misc-bias arm64::macptr.address))))
  (add dest sp (:$ arm64::misc-bias))
  (movk dest (:$ (:apply ash arm64::tag-macptr 8)) (:lsl 48)))


;;; --- Misc operations ---

;;; vcell-ref: load the value slot from a value-cell.
(define-arm64-vinsn (vcell-ref :predicatable)
    (((dest :lisp))
     ((vcell :lisp)))
  (ldr dest (:@ vcell (:$ arm64::value-cell.value))))

;;; %closure-code%: load the %closure-code% symbol's vcell from nil-relative symbols.
(define-arm64-vinsn (%closure-code% :predicatable)
    (((dest :lisp))
     ())
  (ldur dest (:@ rnil (:$ (:apply + arm64::symbol.vcell (arm64::nrs-offset %closure-code%))))))

;;; %codevector-entry: compute entry point from code vector.
;;; On ARM64 the entrypoint is at misc-data-offset (=0) past the tagged pointer.
(define-arm64-vinsn %codevector-entry (((dest t))
                                       ((cv :lisp)))
  (add dest cv (:$ arm64::misc-data-offset)))

;;; single-float-bits: extract 32-bit float value from an immediate single-float.
;;; On ARM64, single-float is immediate with the float bits in the low 32 bits.
(define-arm64-vinsn (single-float-bits :predicatable)
    (((dest :u32))
     ((src :lisp)))
  (mov dest src))

;;; eep.address: load address from an external-entry-point.
(define-arm64-vinsn eep.address (((dest t))
                                 ((src (:lisp (:ne dest)))))
  (ldr dest (:@ src (:$ (:apply + arm64::misc-data-offset 8))))
  (cmp dest rnil)
  (b.ne :ok)
  (uuo-eep-unresolved dest src)
  :ok)


;;; --- Fixnum double-float ref/set (for unboxed arrays via fixnum base) ---

(define-arm64-vinsn fixnum-ref-c-double-float (((dest :double-float))
                                               ((base :imm)
                                                (idx :u32const)))
  (ldr dest (:@ base (:$ (:apply ash idx 3)))))

(define-arm64-vinsn fixnum-ref-double-float (((dest :double-float))
                                             ((base :imm)
                                              (idx :imm))
                                             ((temp :imm)))
  (add temp base idx)
  (ldr dest (:@ temp (:$ 0))))

(define-arm64-vinsn fixnum-set-c-double-float (()
                                               ((base :imm)
                                                (idx :u32const)
                                                (val :double-float)))
  (str val (:@ base (:$ (:apply ash idx 3)))))

(define-arm64-vinsn fixnum-set-double-float (()
                                             ((base :imm)
                                              (idx :imm)
                                              (val :double-float))
                                             ((temp :imm)))
  (add temp base idx)
  (str val (:@ temp (:$ 0))))


;;; --- Subprim call/jump (generic) ---

(define-arm64-vinsn (call-subprim :call :subprim) (()
                                                    ((spno :s32const)))
  (ldr imm2 (:@ rcontext (:$ spno)))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))

(define-arm64-vinsn (jump-subprim :jumplr) (()
                                             ((spno :s32const)))
  (ldr imm2 (:@ rcontext (:$ spno)))
  (br imm2))

;;; Subprim calls with arg/result tracking.
(define-arm64-vinsn (call-subprim-0 :call :subprim) (((dest t))
                                                      ((spno :s32const)))
  (ldr imm2 (:@ rcontext (:$ spno)))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))

(define-arm64-vinsn (call-subprim-1 :call :subprim) (((dest t))
                                                      ((spno :s32const)
                                                       (z t)))
  (ldr imm2 (:@ rcontext (:$ spno)))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))

(define-arm64-vinsn (call-subprim-2 :call :subprim) (((dest t))
                                                      ((spno :s32const)
                                                       (y t)
                                                       (z t)))
  (ldr imm2 (:@ rcontext (:$ spno)))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))

(define-arm64-vinsn (call-subprim-3 :call :subprim) (((dest t))
                                                      ((spno :s32const)
                                                       (x t)
                                                       (y t)
                                                       (z t)))
  (ldr imm2 (:@ rcontext (:$ spno)))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))


;;; --- tail-funcall-vsp ---
;;; Restore lisp context and jump to funcall subprim.
(define-arm64-vinsn (tail-funcall-vsp :jumplr :predicatable) (() ())
  (ldp vsp lr (:@+ sp (:$ arm64::lisp-frame.size)))
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPfuncall))))
  (br imm2))


;;; ======================================================================
;;; Chunk 12: Subprim macros + remaining vinsns + provide
;;; Macro-generated subprim call/jump vinsns, fixnum overflow handling,
;;; frame/TCR introspection, debug traps, interrupt level management,
;;; type checks, and file footer.
;;; ======================================================================

;;; --- Subprim call/jump vinsn macros ---
;;; These generate vinsn definitions that load a subprim address from the
;;; TCR subprim table and branch to it.  The offset is computed at macro
;;; expansion time from *arm64-subprims*.

(defmacro define-arm64-subprim-call-vinsn ((name &rest other-attrs) spno)
  (let ((offset (arm64::arm64-subprimitive-offset spno)))
    `(define-arm64-vinsn (,name :call :subprim ,@other-attrs) (() ())
       (ldr imm2 (:@ rcontext (:$ ,offset)))
       (blr imm2)
       (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))))

(defmacro define-arm64-subprim-jump-vinsn ((name &rest other-attrs) spno)
  (let ((offset (arm64::arm64-subprimitive-offset spno)))
    `(define-arm64-vinsn (,name :jumplr ,@other-attrs) (() ())
       (ldr imm2 (:@ rcontext (:$ ,offset)))
       (br imm2))))


;;; --- Subprim call vinsns ---

(define-arm64-subprim-call-vinsn (save-values) .SPsave-values)

(define-arm64-subprim-call-vinsn (recover-values) .SPrecover-values)

(define-arm64-subprim-call-vinsn (add-values) .SPadd-values)

(define-arm64-subprim-call-vinsn (pass-multiple-values) .SPmvpass)

(define-arm64-subprim-call-vinsn (pass-multiple-values-symbol) .SPmvpasssym)

(define-arm64-subprim-jump-vinsn (jump-known-symbol-ool) .SPjmpsym)

(define-arm64-subprim-call-vinsn (call-known-symbol-ool) .SPjmpsym)

(define-arm64-subprim-jump-vinsn (tail-call-sym-gen) .SPtcallsymgen)

(define-arm64-subprim-jump-vinsn (tail-call-fn-gen) .SPtcallnfngen)

(define-arm64-subprim-jump-vinsn (tail-call-sym-slide) .SPtcallsymslide)

(define-arm64-subprim-jump-vinsn (tail-call-fn-slide) .SPtcallnfnslide)

(define-arm64-subprim-call-vinsn (funcall) .SPfuncall)

(define-arm64-subprim-jump-vinsn (tail-funcall-gen) .SPtfuncallgen)

(define-arm64-subprim-jump-vinsn (tail-funcall-slide) .SPtfuncallslide)

(define-arm64-subprim-call-vinsn (spread-lexpr) .SPspread-lexprz)

(define-arm64-subprim-call-vinsn (spread-list) .SPspreadargz)

(define-arm64-subprim-call-vinsn (getu32) .SPgetu32)

(define-arm64-subprim-call-vinsn (gets32) .SPgets32)

(define-arm64-subprim-call-vinsn (stack-cons-list) .SPstkconslist)

(define-arm64-subprim-call-vinsn (list) .SPconslist)

(define-arm64-subprim-call-vinsn (stack-cons-list*) .SPstkconslist-star)

(define-arm64-subprim-call-vinsn (list*) .SPconslist-star)

(define-arm64-subprim-call-vinsn (make-stack-block) .SPmakestackblock)

(define-arm64-subprim-call-vinsn (make-stack-block0) .SPmakestackblock0)

(define-arm64-subprim-call-vinsn (make-stack-list) .SPmakestacklist)

(define-arm64-subprim-call-vinsn (make-stack-vector) .SPmkstackv)

(define-arm64-subprim-call-vinsn (make-stack-gvector) .SPstkgvector)

;;; make-stack-closure: allocate via SPstkgvector, then fix up entrypoint.
;;; ARM64 function layout has only function.entrypoint (no separate codevector).
;;; TODO: entrypoint fixup may need revision when closure model is finalized.
(define-arm64-vinsn (make-stack-closure :call :subprim) (() ())
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPstkgvector))))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))

(define-arm64-subprim-call-vinsn (stack-misc-alloc) .SPstack-misc-alloc)

(define-arm64-subprim-call-vinsn (stack-misc-alloc-init) .SPstack-misc-alloc-init)

(define-arm64-subprim-call-vinsn (bind-nil) .SPbind-nil)

(define-arm64-subprim-call-vinsn (bind-self) .SPbind-self)

(define-arm64-subprim-call-vinsn (bind-self-boundp-check) .SPbind-self-boundp-check)

(define-arm64-subprim-call-vinsn (bind) .SPbind)

(define-arm64-subprim-jump-vinsn (nvalret :jumplr) .SPnvalret)

(define-arm64-subprim-call-vinsn (nthrowvalues) .SPnthrowvalues)

(define-arm64-subprim-call-vinsn (nthrow1value) .SPnthrow1value)

(define-arm64-subprim-call-vinsn (slide-values) .SPmvslide)

(define-arm64-subprim-call-vinsn (debind) .SPdebind)

(define-arm64-subprim-call-vinsn (keyword-bind) .SPkeyword-bind)

(define-arm64-subprim-call-vinsn (stack-rest-arg) .SPstack-rest-arg)

(define-arm64-subprim-call-vinsn (req-stack-rest-arg) .SPreq-stack-rest-arg)

(define-arm64-subprim-call-vinsn (stack-cons-rest-arg) .SPstack-cons-rest-arg)

(define-arm64-subprim-call-vinsn (heap-rest-arg) .SPheap-rest-arg)

(define-arm64-subprim-call-vinsn (req-heap-rest-arg) .SPreq-heap-rest-arg)

(define-arm64-subprim-call-vinsn (heap-cons-rest-arg) .SPheap-cons-rest-arg)

(define-arm64-subprim-call-vinsn (opt-supplied-p) .SPopt-supplied-p)

(define-arm64-subprim-call-vinsn (gvector) .SPgvector)

(define-arm64-subprim-call-vinsn (discard-temp-frame) .SPdiscard_stack_object)

;;; nth-value: special — has a result register.
(define-arm64-vinsn (nth-value :call :subprim) (((result :lisp))
                                                ())
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPnthvalue))))
  (blr imm2)
  (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))

(define-arm64-subprim-call-vinsn (fitvals) .SPfitvals)

(define-arm64-subprim-call-vinsn (misc-alloc) .SPmisc-alloc)

(define-arm64-subprim-call-vinsn (misc-alloc-init) .SPmisc-alloc-init)

(define-arm64-subprim-call-vinsn (integer-sign) .SPinteger-sign)

;;; throw: special — jump-unknown control flow.
(define-arm64-vinsn (throw :jump-unknown) (()
                                           ())
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPthrow))))
  (blr imm2))

;;; Catch/unwind subprims use mkcatch() which does "add lr,lr,#4".
;;; The two branch instructions (B cleanup, B normal) must be at LR+0 and LR+4
;;; relative to the BLR, so these vinsns must NOT include reload-self (ldr nfn).
;;; The catch/unwind frame saves/restores nfn, so it's safe to omit.
(define-arm64-vinsn (mkcatchmv :call :subprim) (() ())
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPmkcatchmv))))
  (blr imm2))

(define-arm64-vinsn (mkcatch1v :call :subprim) (() ())
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPmkcatch1v))))
  (blr imm2))

(define-arm64-subprim-call-vinsn (setqsym) .SPsetqsym)

(define-arm64-subprim-call-vinsn (ksignalerr) .SPksignalerr)

(define-arm64-subprim-call-vinsn (subtag-misc-ref) .SPsubtag-misc-ref)

(define-arm64-subprim-call-vinsn (subtag-misc-set) .SPsubtag-misc-set)

(define-arm64-vinsn (mkunwind :call :subprim) (() ())
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPmkunwind))))
  (blr imm2))
(define-arm64-vinsn (nmkunwind :call :subprim) (() ())
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPmkunwind))))
  (blr imm2))

;;; progvsave also uses mkcatch() — no reload-self before branch pair.
(define-arm64-vinsn (progvsave :call :subprim) (() ())
  (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPprogvsave))))
  (blr imm2))

(define-arm64-subprim-jump-vinsn (progvrestore) .SPprogvrestore)

(define-arm64-subprim-call-vinsn (misc-ref) .SPmisc-ref)

(define-arm64-subprim-call-vinsn (misc-set) .SPmisc-set)

(define-arm64-subprim-call-vinsn (gets64) .SPgets64)

(define-arm64-subprim-call-vinsn (getu64) .SPgetu64)

(define-arm64-subprim-call-vinsn (makeu64) .SPmakeu64)

(define-arm64-subprim-call-vinsn (makes64) .SPmakes64)

(define-arm64-subprim-call-vinsn (bind-interrupt-level-0) .SPbind-interrupt-level-0)

(define-arm64-subprim-call-vinsn (bind-interrupt-level-m1) .SPbind-interrupt-level-m1)

(define-arm64-subprim-call-vinsn (bind-interrupt-level) .SPbind-interrupt-level)

(define-arm64-subprim-call-vinsn (unbind-interrupt-level) .SPunbind-interrupt-level)

(define-arm64-subprim-call-vinsn (aapcs64-ff-call-simple) .SPaapcs64-ff-call-simple)

(define-arm64-subprim-call-vinsn (aapcs64-ff-callhf) .SPaapcs64-ff-callhf)


;;; --- Handle fixnum overflow (inline) ---
;;; When a fixnum operation overflows (detected by sign-extend check),
;;; allocate a two-digit bignum.  On ARM64 with fixnumshift=0, the
;;; 64-bit result IS the correct mathematical value (no unboxing needed).
;;; Bignum digits are 32-bit, so we store low and high halves.
;;; Layout: [header(8)] [low32 | high32] = 16 bytes = 1 dnode.

(define-arm64-vinsn handle-fixnum-overflow-inline (((dest :lisp))
                                                   ((src :imm))
                                                   ((header :u64)))
  ;; dest holds the overflowed 64-bit value (= correct mathematical result)
  (mov header (:$ arm64::two-digit-bignum-header))
  ;; Allocate one dnode (16 bytes): header(8) + two 32-bit digits(8)
  (sub allocptr allocptr (:$ arm64::dnode-size))
  (cmp allocptr allocbase)
  (b.hi :no-trap)
  (hlt (:$ 0))
  :no-trap
  (str header (:@ allocptr (:$ 0)))
  ;; Store the 64-bit value at data offset (low 32 bits first on LE)
  (str dest (:@ allocptr (:$ arm64::node-size)))
  (add dest allocptr (:$ arm64::misc-bias))
  (movk dest (:$ (:apply ash arm64::tag-bignum 8)) (:lsl 48)))


;;; --- Frame/TCR introspection ---

(define-arm64-vinsn (%current-frame-ptr :predicatable)
    (((dest :imm))
     ())
  (add dest sp (:$ 0)))

(define-arm64-vinsn (%current-tcr :predicatable)
    (((dest :imm))
     ())
  (mov dest rcontext))


;;; --- Dynamic binding payback ---
;;; Unbind N special bindings.

(define-arm64-vinsn (dpayback :call :subprim) (()
                                               ((n :s16const))
                                               ((temp (:u64 #.arm64::imm0))))
  ((:pred > n 1)
   (mov temp (:$ n))
   (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPunbind-n))))
   (blr imm2)
   (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn))))
  ((:pred = n 1)
   (ldr imm2 (:@ rcontext (:$ (:apply arm64::arm64-subprimitive-offset '.SPunbind))))
   (blr imm2)
   (ldr nfn (:@ x29 (:$ arm64::lisp-frame.savefn)))))


;;; --- Interrupt control ---

;;; ref-interrupt-level: load current interrupt level from TLB.
(define-arm64-vinsn (ref-interrupt-level :predicatable)
    (((dest :imm))
     ()
     ((temp :u64)))
  (ldr temp (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (ldr dest (:@ temp (:$ arm64::interrupt-level-binding-index))))

;;; disable-interrupts: set interrupt-level to -1 (fixnum -1 on ARM64 with
;;; fixnumshift=0 is just -1), return old value.
(define-arm64-vinsn (disable-interrupts :predicatable)
    (((dest :lisp))
     ()
     ((temp :imm)
      (temp2 :imm)))
  (ldr temp2 (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (ldr dest (:@ temp2 (:$ arm64::interrupt-level-binding-index)))
  (mov temp (:$ -1))
  (str temp (:@ temp2 (:$ arm64::interrupt-level-binding-index))))

;;; bind-interrupt-level-0-inline: bind interrupt level to 0.
;;; Push old value, binding index, and db-link onto vstack, set to 0.
;;; If transitioning from negative to 0, check for pending interrupts.
(define-arm64-vinsn bind-interrupt-level-0-inline (()
                                                   ()
                                                   ((tlb :imm)
                                                    (value :imm)
                                                    (link :imm)
                                                    (temp :imm)))
  (ldr tlb (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (ldr value (:@ tlb (:$ arm64::interrupt-level-binding-index)))
  (ldr link (:@ rcontext (:$ arm64::tcr.db-link)))
  (cmp value (:$ 0))
  (mov temp (:$ arm64::interrupt-level-binding-index))
  (str value (:@! vsp (:$ (- arm64::node-size))))
  (str temp (:@! vsp (:$ (- arm64::node-size))))
  (str link (:@! vsp (:$ (- arm64::node-size))))
  (mov temp (:$ 0))
  (str temp (:@ tlb (:$ arm64::interrupt-level-binding-index)))
  (str vsp (:@ rcontext (:$ arm64::tcr.db-link)))
  (b.ge :done)
  (ldr nargs (:@ rcontext (:$ arm64::tcr.interrupt-pending)))
  (cmp nargs (:$ 0))
  (b.eq :done)
  (uuo-interrupt-now)
  :done)

;;; bind-interrupt-level-m1-inline: bind interrupt level to -1.
(define-arm64-vinsn bind-interrupt-level-m1-inline (()
                                                    ()
                                                    ((tlb :imm)
                                                     (oldvalue :imm)
                                                     (link :imm)
                                                     (newvalue :imm)
                                                     (idx :imm)))
  (mov newvalue (:$ -1))
  (mov idx (:$ arm64::interrupt-level-binding-index))
  (ldr tlb (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (ldr oldvalue (:@ tlb (:$ arm64::interrupt-level-binding-index)))
  (ldr link (:@ rcontext (:$ arm64::tcr.db-link)))
  (str oldvalue (:@! vsp (:$ (- arm64::node-size))))
  (str idx (:@! vsp (:$ (- arm64::node-size))))
  (str link (:@! vsp (:$ (- arm64::node-size))))
  (str newvalue (:@ tlb (:$ arm64::interrupt-level-binding-index)))
  (str vsp (:@ rcontext (:$ arm64::tcr.db-link))))

;;; unbind-interrupt-level-inline: restore interrupt level from binding stack.
;;; If transitioning from negative to non-negative, check for pending interrupts.
(define-arm64-vinsn unbind-interrupt-level-inline (()
                                                   ()
                                                   ((tlb :imm)
                                                    (link :imm)
                                                    (saved-value :imm)
                                                    (restored-value :imm)))
  (ldr tlb (:@ rcontext (:$ arm64::tcr.tlb-pointer)))
  (ldr saved-value (:@ tlb (:$ arm64::interrupt-level-binding-index)))
  (ldr link (:@ rcontext (:$ arm64::tcr.db-link)))
  (ldr restored-value (:@ link (:$ 16)))
  (ldr link (:@ link (:$ 0)))
  (cmp restored-value (:$ 0))
  (str restored-value (:@ tlb (:$ arm64::interrupt-level-binding-index)))
  (str link (:@ rcontext (:$ arm64::tcr.db-link)))
  (b.lt :done)
  (cmp saved-value (:$ 0))
  (b.ge :done)
  (ldr link (:@ rcontext (:$ arm64::tcr.interrupt-pending)))
  (cmp link (:$ 0))
  (b.eq :done)
  (uuo-interrupt-now)
  :done)


;;; --- NOP and debug ---

(define-arm64-vinsn nop (()
                         ())
  (nop))

(define-arm64-vinsn %debug-trap (()
                                 ())
  (uuo-debug-trap))


;;; --- Test fixnum(s) ---
;;; ARM64 TBI fixnum check: tag byte is 0x00 (positive) or 0xFF (negative).
;;; Extract tag, add 1 → positive fixnum gives 1, negative gives 0 (wrap).
;;; Then test if result < 2.

(define-arm64-vinsn test-fixnum (((dest :crf))
                                 ((src :lisp))
                                 ((tag :u64)))
  (lsr tag src (:$ arm64::tag-shift))
  (add tag tag (:$ 1))
  (cmp tag (:$ 2)))

;;; Test if both x and y are fixnums.
(define-arm64-vinsn test-fixnums (((dest :crf))
                                  ((x :lisp)
                                   (y :lisp))
                                  ((tag :u64)))
  (orr tag x y)
  (lsr tag tag (:$ arm64::tag-shift))
  (add tag tag (:$ 1))
  (cmp tag (:$ 2)))


;;; --- Typecode predicates ---

;;; ivector-typecode-p: check if a typecode represents an ivector.
(define-arm64-vinsn ivector-typecode-p (((dest :lisp))
                                        ((src :lisp))
                                        ((tag :u64)
                                         (mask :u64)))
  ;; Ivector subtags have bit 7 set, bit 5 clear
  (and tag src (:$ #xff))
  (eor tag tag (:$ arm64::uvector-header))
  (mov mask (:$ (:apply logior arm64::uvector-header arm64::gvector-tag-mask)))
  (tst tag mask)
  (b.ne :not-ivector)
  ((:not (:pred =
                (:apply %hard-regspec-value dest)
                (:apply %hard-regspec-value src)))
   (mov dest src))
  (b :done)
  :not-ivector
  (mov dest (:$ 0))
  :done)

;;; gvector-typecode-p: check if a typecode represents a gvector.
;;; Gvector subtags have bits 7,5 set (uvector-header | gvector-tag-mask = 0xA0).
;;; 0xA0 is not a valid ARM64 bitmask immediate, so use register-based masking.
(define-arm64-vinsn gvector-typecode-p (((dest :lisp))
                                        ((src :lisp))
                                        ((tag :u64)
                                         (mask :u64)))
  (and tag src (:$ #xff))
  (mov mask (:$ (:apply logior arm64::uvector-header arm64::gvector-tag-mask)))
  (and tag tag mask)
  (cmp tag mask)
  (b.ne :not-gvector)
  ((:not (:pred =
                (:apply %hard-regspec-value dest)
                (:apply %hard-regspec-value src)))
   (mov dest src))
  (b :done)
  :not-gvector
  (mov dest (:$ 0))
  :done)


;;; --- Complex float accessors ---
;;; Complex-single-float has realpart and imagpart as consecutive 32-bit
;;; values in one 8-byte slot.

(define-arm64-vinsn %complex-single-float-realpart (((dest :single-float))
                                                    ((src :lisp))
                                                    ((temp :u32)))
  (ldr temp (:@ src (:$ arm64::complex-single-float.realpart)))
  (fmov dest temp))

(define-arm64-vinsn %complex-single-float-imagpart (((dest :single-float))
                                                    ((src :lisp))
                                                    ((temp :u32)))
  (ldr temp (:@ src (:$ arm64::complex-single-float.imagpart)))
  (fmov dest temp))

;;; Complex-double-float: realpart and imagpart as consecutive 8-byte values.
(define-arm64-vinsn %complex-double-float-realpart (((dest :double-float))
                                                    ((src :lisp)))
  (ldr dest (:@ src (:$ arm64::complex-double-float.realpart))))

(define-arm64-vinsn %complex-double-float-imagpart (((dest :double-float))
                                                    ((src :lisp)))
  (ldr dest (:@ src (:$ arm64::complex-double-float.imagpart))))


;;; --- set-eq-bit: set Z flag ---
(define-arm64-vinsn set-eq-bit (((flags :crf))
                                ())
  (cmp sp sp))


;;; --- sign-extend-halfword: sign-extend 16-bit value to tagged fixnum ---
;;; Used by %word-to-int operator.  ARM64 SXTH sign-extends bits 0-15.
(define-arm64-vinsn (sign-extend-halfword :predicatable)
    (((dest :lisp))
     ((src :lisp))
     ())
  (sxth dest src))

;;; --- u32->char: wrap a u32 value into a character-tagged node ---
;;; Used by %code-char operator.
(define-arm64-vinsn (u32->char :predicatable)
    (((dest :lisp))
     ((src :imm))
     ())
  (lsl dest src (:$ arm64::charcode-shift))
  (movk dest (:$ (:apply ash arm64::tag-character 8)) (:lsl 48)))


;;; ======================================================================
;;; Missing vinsns — added during cross-compilation bring-up
;;; ======================================================================

;;; --- Bit test operations ---

(define-arm64-vinsn %ilogbitp-constant-bit (((dest :crf))
                                             ((fixnum :imm)
                                              (bitnum :u8const)))
  (tst fixnum (:$ (:apply ash 1 bitnum))))

(define-arm64-vinsn %ilogbitp-variable-bit (((dest :crf))
                                             ((fixnum :imm)
                                              (bitnum :u8))
                                             ((mask :imm)))
  (mov mask (:$ 1))
  (tst fixnum (:lsl mask bitnum)))

(define-arm64-vinsn extract-variable-bit-fixnum (((dest :lisp))
                                                  ((src :imm)
                                                   (bitnum :u8)))
  (lsr dest src bitnum)
  (and dest dest (:$ 1)))

;;; --- Bit manipulation ---

(define-arm64-vinsn set-constant-bit-to-0 (((dest :u32))
                                            ((src :u32)
                                             (bitnum :u8const)))
  (bic dest src (:$ (:apply ash 1 bitnum))))

(define-arm64-vinsn set-constant-bit-to-1 (((dest :u32))
                                            ((src :u32)
                                             (bitnum :u8const)))
  (orr dest src (:$ (:apply ash 1 bitnum))))

(define-arm64-vinsn set-constant-bit-to-variable-value (((dest :u32))
                                                         ((src :u32)
                                                          (val :u32)
                                                          (bitnum :u8const))
                                                         ((mask :u32)))
  (mov mask (:$ (:apply ash 1 bitnum)))
  (bic dest src mask)
  (tst val val)
  (b.eq :done)
  (orr dest dest mask)
  :done)

(define-arm64-vinsn set-or-clear-bit (((dest :u32))
                                       ((src :u32)
                                        (mask :u32)
                                        (crf :crf)))
  (b.eq :clear)
  (orr dest src mask)
  (b :done)
  :clear
  (bic dest src mask)
  :done)

(define-arm64-vinsn shift-left-variable-word (((dest :u32))
                                               ((src :u32)
                                                (count :u32)))
  (lsl dest src count))

(define-arm64-vinsn u32logandc2 (((dest :u32))
                                  ((x :u32)
                                   (y :u32)))
  (bic dest x y))

(define-arm64-vinsn u32logior (((dest :u32))
                                ((x :u32)
                                 (y :u32)))
  (orr dest x y))

;;; --- Arithmetic ---

(define-arm64-vinsn (add-immediate :predicatable) (((dest :imm))
                                                    ((src :imm)
                                                     (imm :s32const)))
  (add dest src (:$ imm)))

(define-arm64-vinsn add-immediate-set-flags (((dest :imm)
                                              (flags :crf))
                                             ((src :imm)
                                              (imm :s32const)))
  (adds dest src (:$ imm)))

(define-arm64-vinsn (natural-shift-left :predicatable) (((dest :u64))
                                                         ((src :u64)
                                                          (count :u8const)))
  (lsl dest src (:$ count)))

(define-arm64-vinsn (natural-shift-right :predicatable) (((dest :u64))
                                                          ((src :u64)
                                                           (count :u8const)))
  (lsr dest src (:$ count)))

(define-arm64-vinsn set-carry-if-fixnum-in-range (((idx :lisp)
                                                   (flags :crf))
                                                  ((reg :imm)
                                                   (min :s32const)
                                                   (span :u32const)))
  (sub idx reg (:$ min))
  (cmp idx (:$ span)))

;;; --- Stack / frame ---

(define-arm64-vinsn (adjust-sp :predicatable) (()
                                                ((amount :s32const)))
  (add sp sp (:$ amount)))

(define-arm64-vinsn load-vframe-address (((dest :imm))
                                          ((offset :s32const)))
  (add dest sp (:$ offset)))

(define-arm64-vinsn copy-lexpr-argument (()
                                          ()
                                          ((temp :imm)))
  (ldr temp (:@ vsp nargs))
  (str temp (:@! vsp (:$ (- arm64::node-size)))))

;;; --- Type checks ---

(define-arm64-vinsn trap-unless-macptr (()
                                        ((object :lisp))
                                        ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :fail)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-macptr))
  (b.eq :ok)
  :fail
  (uuo-error-reg-not-xtype object (:$ arm64::subtag-macptr))
  :ok)

(define-arm64-vinsn trap-unless-simple-1d-array (()
                                                  ((object :lisp)
                                                   (expected :u8const))
                                                  ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :fail)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ expected))
  (b.eq :ok)
  :fail
  (uuo-error-reg-not-xtype object (:$ expected))
  :ok)

(define-arm64-vinsn trap-unless-simple-array-2 (()
                                                 ((object :lisp)
                                                  (expected :u8const))
                                                 ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :fail)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ expected))
  (b.eq :ok)
  :fail
  (uuo-error-reg-not-xtype object (:$ expected))
  :ok)

(define-arm64-vinsn trap-unless-simple-array-3 (()
                                                 ((object :lisp)
                                                  (expected :u8const))
                                                 ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :fail)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ expected))
  (b.eq :ok)
  :fail
  (uuo-error-reg-not-xtype object (:$ expected))
  :ok)

(define-arm64-vinsn trap-unless-typed-array-2 (()
                                                ((object :lisp)
                                                 (expected :u8const))
                                                ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :fail)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ expected))
  (b.eq :ok)
  :fail
  (uuo-error-reg-not-xtype object (:$ expected))
  :ok)

(define-arm64-vinsn trap-unless-typed-array-3 (()
                                                ((object :lisp)
                                                 (expected :u8const))
                                                ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :fail)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ expected))
  (b.eq :ok)
  :fail
  (uuo-error-reg-not-xtype object (:$ expected))
  :ok)

(define-arm64-vinsn trap-unless-vector-type (()
                                              ((object :lisp)
                                               (expected :u8const))
                                              ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (tst tag (:$ arm64::uvector-ref))
  (b.eq :fail)
  (ldur tag (:@ object (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ expected))
  (b.eq :ok)
  :fail
  (uuo-error-reg-not-xtype object (:$ expected))
  :ok)

;;; Vector header operations
(define-arm64-vinsn set-z-if-vector-header (((dest :crf))
                                             ((src :lisp))
                                             ((tag :u8)))
  (ldur tag (:@ src (:$ arm64::misc-subtag-offset)))
  (and tag tag (:$ #xff))
  (cmp tag (:$ arm64::subtag-vectorH)))

(define-arm64-vinsn check-vector-header-bound (()
                                                ((header :lisp)
                                                 (index :imm))
                                                ((dim :imm)))
  (ldr dim (:@ header (:$ arm64::vectorH.logsize)))
  (cmp index dim)
  (b.lo :ok)
  (uuo-error-vector-bounds index header)
  :ok)

(define-arm64-vinsn deref-vector-header (((vector :lisp)
                                          (index :imm))
                                         ((vector :lisp)
                                          (index :imm))
                                         ((temp :imm)))
  :again
  (ldr temp (:@ vector (:$ arm64::vectorH.flags)))
  (tst temp (:$ (:apply ash 1 $arh_disp_bit)))
  (ldr temp (:@ vector (:$ arm64::vectorH.displacement)))
  (add index index temp)
  (ldr vector (:@ vector (:$ arm64::vectorH.data-vector)))
  (b.ne :again))

;;; Character / string operations

(define-arm64-vinsn require-char-code (()
                                        ((object :lisp))
                                        ((tag :u8)))
  (lsr tag object (:$ arm64::tag-shift))
  (cmp tag (:$ arm64::tag-character))
  (b.eq :ok)
  (uuo-cerror-reg-not-xtype object (:$ arm64::tag-character))
  :ok)

(define-arm64-vinsn (code-char->char :predicatable) (((dest :lisp))
                                                      ((src :imm)))
  (lsl dest src (:$ arm64::charcode-shift))
  (movk dest (:$ (:apply ash arm64::tag-character 8)) (:lsl 48)))

;;; 8-bit string access
(define-arm64-vinsn (%schar8 :predicatable) (((dest :lisp))
                                              ((str :lisp)
                                               (idx :imm))
                                              ((temp :u32)))
  (add temp idx (:$ arm64::misc-data-offset))
  (ldrb temp (:@ str temp))
  (lsl dest temp (:$ arm64::charcode-shift))
  (movk dest (:$ (:apply ash arm64::tag-character 8)) (:lsl 48)))

(define-arm64-vinsn (%scharcode8 :predicatable) (((dest :imm))
                                                   ((str :lisp)
                                                    (idx :imm))
                                                   ((temp :u32)))
  (add temp idx (:$ arm64::misc-data-offset))
  (ldrb dest (:@ str temp)))

(define-arm64-vinsn %set-schar8 (()
                                   ((str :lisp)
                                    (idx :imm)
                                    (char :lisp))
                                   ((temp :u32)
                                    (offset :u32)))
  (lsr temp char (:$ arm64::charcode-shift))
  (add offset idx (:$ arm64::misc-data-offset))
  (strb temp (:@ str offset)))

(define-arm64-vinsn %set-scharcode8 (()
                                      ((str :lisp)
                                       (idx :imm)
                                       (code :imm))
                                      ((offset :u32)))
  (add offset idx (:$ arm64::misc-data-offset))
  (strb code (:@ str offset)))

;;; 32-bit string access
(define-arm64-vinsn (%schar32 :predicatable) (((dest :lisp))
                                               ((str :lisp)
                                                (idx :imm))
                                               ((temp :u32)))
  (add temp idx (:$ (:apply ash arm64::misc-data-offset -2)))
  (ldr temp (:@ str (:lsl temp 2)))
  (lsl dest temp (:$ arm64::charcode-shift))
  (movk dest (:$ (:apply ash arm64::tag-character 8)) (:lsl 48)))

(define-arm64-vinsn (%scharcode32 :predicatable) (((dest :imm))
                                                    ((str :lisp)
                                                     (idx :imm))
                                                    ((temp :u32)))
  (add temp idx (:$ (:apply ash arm64::misc-data-offset -2)))
  (ldr dest (:@ str (:lsl temp 2))))

(define-arm64-vinsn %set-schar32 (()
                                   ((str :lisp)
                                    (idx :imm)
                                    (char :lisp))
                                   ((temp :u32)
                                    (offset :u32)))
  (lsr temp char (:$ arm64::charcode-shift))
  (add offset idx (:$ (:apply ash arm64::misc-data-offset -2)))
  (str temp (:@ str (:lsl offset 2))))

(define-arm64-vinsn %set-scharcode32 (()
                                       ((str :lisp)
                                        (idx :imm)
                                        (code :imm))
                                       ((offset :u32)))
  (add offset idx (:$ (:apply ash arm64::misc-data-offset -2)))
  (str code (:@ str (:lsl offset 2))))

;;; --- Unboxing ---

(define-arm64-vinsn (%unbox-u8 :predicatable) (((dest :u8))
                                                ((src :lisp)))
  (and dest src (:$ #xff)))

;;; --- Integer narrowing ---

(define-arm64-vinsn (s8->fixnum :predicatable) (((dest :imm))
                                                 ((src :imm)))
  (sbfx dest src 0 8))

(define-arm64-vinsn (s16->fixnum :predicatable) (((dest :imm))
                                                  ((src :imm)))
  (sbfx dest src 0 16))

(define-arm64-vinsn (u8->fixnum :predicatable) (((dest :imm))
                                                 ((src :imm)))
  (and dest src (:$ #xff)))

(define-arm64-vinsn (u16->fixnum :predicatable) (((dest :imm))
                                                  ((src :imm)))
  (and dest src (:$ #xffff)))

(define-arm64-vinsn (s8->s32 :predicatable) (((dest :s32))
                                              ((src :s32)))
  (sbfx dest src 0 8))

(define-arm64-vinsn (s16->s32 :predicatable) (((dest :s32))
                                               ((src :s32)))
  (sbfx dest src 0 16))

(define-arm64-vinsn (u8->u32 :predicatable) (((dest :u32))
                                              ((src :u32)))
  (and dest src (:$ #xff)))

(define-arm64-vinsn (u16->u32 :predicatable) (((dest :u32))
                                               ((src :u32)))
  (and dest src (:$ #xffff)))

;;; --- Memory access (doubleword = 64-bit) ---

(define-arm64-vinsn (mem-ref-c-doubleword :predicatable) (((dest :u64))
                                                           ((src :address)
                                                            (index :s16const)))
  (ldr dest (:@ src (:$ index))))

(define-arm64-vinsn (mem-ref-doubleword :predicatable) (((dest :u64))
                                                         ((src :address)
                                                          (index :imm)))
  (ldr dest (:@ src index)))

(define-arm64-vinsn (mem-set-c-doubleword :predicatable) (()
                                                           ((val :u64)
                                                            (dest :address)
                                                            (index :s16const)))
  (str val (:@ dest (:$ index))))

(define-arm64-vinsn (mem-set-doubleword :predicatable) (()
                                                         ((val :u64)
                                                          (dest :address)
                                                          (index :imm)))
  (str val (:@ dest index)))

;;; --- Bit memory access ---

(define-arm64-vinsn mem-ref-bit (((dest :u32))
                                  ((src :address)
                                   (bit-offset :imm))
                                  ((word-offset :imm)
                                   (bit-shift :imm)))
  (lsr word-offset bit-offset (:$ 5))
  (ldr dest (:@ src (:lsl word-offset 2)))
  (and bit-shift bit-offset (:$ 31))
  (lsr dest dest bit-shift)
  (and dest dest (:$ 1)))

(define-arm64-vinsn mem-ref-bit-fixnum (((dest :lisp))
                                         ((src :address)
                                          (bit-offset :imm))
                                         ((word-offset :imm)
                                          (bit-shift :imm)))
  (lsr word-offset bit-offset (:$ 5))
  (ldr dest (:@ src (:lsl word-offset 2)))
  (and bit-shift bit-offset (:$ 31))
  (lsr dest dest bit-shift)
  (and dest dest (:$ 1)))

(define-arm64-vinsn mem-set-bit (()
                                  ((src :address)
                                   (bit-offset :imm)
                                   (val :imm))
                                  ((word-offset :imm)
                                   (bit-shift :imm)
                                   (mask :u32)
                                   (word :u32)))
  (lsr word-offset bit-offset (:$ 5))
  (ldr word (:@ src (:lsl word-offset 2)))
  (and bit-shift bit-offset (:$ 31))
  (mov mask (:$ 1))
  (lsl mask mask bit-shift)
  (tst val val)
  (b.eq :clear)
  (orr word word mask)
  (b :store)
  :clear
  (bic word word mask)
  :store
  (str word (:@ src (:lsl word-offset 2))))

;;; --- Float operations ---

(define-arm64-vinsn (zero-double-float-register :predicatable) (((dest :double-float))
                                                                 ()
                                                                 ((temp :u64)))
  ;; FMOV Dd, XZR — zero the double-float register via zero GPR
  (mov temp (:$ 0))
  (fmov dest temp))

(define-arm64-vinsn (zero-single-float-register :predicatable) (((dest :single-float))
                                                                 ()
                                                                 ((temp :u32)))
  ;; FMOV Sn, Wtemp — zero the single-float register via zero GPR
  (mov temp (:$ 0))
  (fmov dest temp))

(define-arm64-vinsn (double-to-double :predicatable) (((dest :double-float))
                                                       ((src :double-float)))
  (fmov dest src))

(define-arm64-vinsn (single-to-single :predicatable) (((dest :single-float))
                                                       ((src :single-float)))
  (fmov dest src))

(define-arm64-vinsn load-double-float-constant-from-data (((dest :double-float))
                                                           ((high :u32const)
                                                            (low :u32const))
                                                           ((temp :u64)))
  (mov temp (:$ low))
  (movk temp (:$ (:apply ldb (byte 16 16) low)) (:lsl 16))
  (movk temp (:$ (:apply ldb (byte 16 0) high)) (:lsl 32))
  (movk temp (:$ (:apply ldb (byte 16 16) high)) (:lsl 48))
  (fmov dest temp))

(define-arm64-vinsn load-single-float-constant-from-data (((dest :single-float))
                                                            ((bits :u32const))
                                                            ((temp :u32)))
  (mov temp (:$ (:apply logand bits #xffff)))
  (movk temp (:$ (:apply ldb (byte 16 16) bits)) (:lsl 16))
  (fmov dest temp))

;;; --- Complex float ---

(define-arm64-vinsn complex-single-float (((dest :complex-single-float))
                                           ((real :single-float)
                                            (imag :single-float)))
  (fmov dest real)
  (ins dest (:element 1) imag (:element 0)))

(define-arm64-vinsn complex-double-float (((dest :complex-double-float))
                                           ((real :double-float)
                                            (imag :double-float)))
  (fmov dest real)
  (ins dest (:element 1) imag (:element 0)))

(define-arm64-vinsn complex-single-float+-2 (((dest :complex-single-float))
                                              ((x :complex-single-float)
                                               (y :complex-single-float)))
  (fadd dest x y))

(define-arm64-vinsn complex-single-float--2 (((dest :complex-single-float))
                                              ((x :complex-single-float)
                                               (y :complex-single-float)))
  (fsub dest x y))

(define-arm64-vinsn complex-double-float+-2 (((dest :complex-double-float))
                                              ((x :complex-double-float)
                                               (y :complex-double-float)))
  (fadd dest x y))

(define-arm64-vinsn complex-double-float--2 (((dest :complex-double-float))
                                              ((x :complex-double-float)
                                               (y :complex-double-float)))
  (fsub dest x y))

(define-arm64-vinsn (complex-single-float->node :call :subprim)
    (((dest :lisp))
     ((src :complex-single-float))
     ((header :u64)))
  ;; Allocate 16 bytes: header(8) + 2 single floats(8)
  (mov header (:$ arm64::complex-single-float-header))
  (sub allocptr allocptr (:$ arm64::dnode-size))
  (cmp allocptr allocbase)
  (b.hi :no-trap)
  (hlt (:$ 0))
  :no-trap
  (str header (:@ allocptr (:$ 0)))
  (str src (:@ allocptr (:$ arm64::complex-single-float.realpart)))
  (add dest allocptr (:$ arm64::misc-bias))
  (movk dest (:$ (:apply ash arm64::tag-complex-single-float 8)) (:lsl 48)))

(define-arm64-vinsn (complex-double-float->heap :call :subprim)
    (((dest :lisp))
     ((src :complex-double-float))
     ((header :u64)))
  ;; Allocate 32 bytes: header(8) + pad(8) + 2 doubles(16)
  (mov header (:$ arm64::complex-double-float-header))
  (sub allocptr allocptr (:$ 32))
  (cmp allocptr allocbase)
  (b.hi :no-trap)
  (hlt (:$ 0))
  :no-trap
  (str header (:@ allocptr (:$ 0)))
  (str src (:@ allocptr (:$ arm64::complex-double-float.realpart)))
  (add dest allocptr (:$ arm64::misc-bias))
  (movk dest (:$ (:apply ash arm64::tag-complex-double-float 8)) (:lsl 48)))

(define-arm64-vinsn complex-single-float-to-complex-single-float
    (((dest :complex-single-float))
     ((src :complex-single-float)))
  (mov dest src))

(define-arm64-vinsn complex-double-float-to-complex-double-float
    (((dest :complex-double-float))
     ((src :complex-double-float)))
  (mov dest src))

(define-arm64-vinsn (get-complex-double-float :predicatable)
    (((dest :complex-double-float))
     ((src :lisp)))
  (ldr dest (:@ src (:$ arm64::complex-double-float.realpart))))

(define-arm64-vinsn (get-complex-single-float :predicatable)
    (((dest :complex-single-float))
     ((src :lisp)))
  (ldr dest (:@ src (:$ arm64::complex-single-float.realpart))))

;;; --- FPU exception handling ---

(define-arm64-vinsn clear-pending-fpu-exceptions (()
                                                   ()
                                                   ((temp :u64)))
  (mrs temp (:$ #xDA21))
  (and temp temp (:$ #xFFFFFFFFFFFFFF00))
  (msr (:$ #xDA21) temp))

(define-arm64-vinsn trap-if-fpu-exception (()
                                            ()
                                            ((temp :u64)))
  (mrs temp (:$ #xDA21))
  (tst temp (:$ #x1F))
  (b.eq :ok)
  (uuo-error-reg-not-xtype temp (:$ 0))
  :ok)

;;; --- NFP (native frame pointer) operations ---
;;; Non-nested: offset from SP.  Nested: from tcr.nfp.

(define-arm64-vinsn (nfp-load-double-float :nfp :ref) (((val :double-float))
                                                        ((offset :u16const)))
  (ldr val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-load-double-float-nested :nfp :ref) (((val :double-float))
                                                                ((offset :u16const))
                                                                ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (ldr val (:@ nfp-reg (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-double-float :nfp :set) (()
                                                         ((val :double-float)
                                                          (offset :u16const)))
  (str val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-double-float-nested :nfp :set) (()
                                                                 ((val :double-float)
                                                                  (offset :u16const))
                                                                 ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (str val (:@ nfp-reg (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-load-single-float :nfp :ref) (((val :single-float))
                                                        ((offset :u16const)))
  (ldr val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-load-single-float-nested :nfp :ref) (((val :single-float))
                                                                ((offset :u16const))
                                                                ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (ldr val (:@ nfp-reg (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-single-float :nfp :set) (()
                                                         ((val :single-float)
                                                          (offset :u16const)))
  (str val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-single-float-nested :nfp :set) (()
                                                                 ((val :single-float)
                                                                  (offset :u16const))
                                                                 ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (str val (:@ nfp-reg (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-load-unboxed-word :nfp :ref) (((val :u64))
                                                        ((offset :u16const)))
  (ldr val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-load-unboxed-word-nested :nfp :ref) (((val :u64))
                                                                ((offset :u16const))
                                                                ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (ldr val (:@ nfp-reg (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-unboxed-word :nfp :set) (()
                                                         ((val :u64)
                                                          (offset :u16const)))
  (str val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-unboxed-word-nested :nfp :set) (()
                                                                 ((val :u64)
                                                                  (offset :u16const))
                                                                 ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (str val (:@ nfp-reg (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-load-complex-double-float :nfp :ref) (((val :complex-double-float))
                                                                 ((offset :u16const)))
  (ldr val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-load-complex-double-float-nested :nfp :ref) (((val :complex-double-float))
                                                                       ((offset :u16const))
                                                                       ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (ldr val (:@ nfp-reg (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-complex-double-float :nfp :set) (()
                                                                  ((val :complex-double-float)
                                                                   (offset :u16const)))
  (str val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-complex-double-float-nested :nfp :set) (()
                                                                        ((val :complex-double-float)
                                                                         (offset :u16const))
                                                                        ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (str val (:@ nfp-reg (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-load-complex-single-float :nfp :ref) (((val :complex-single-float))
                                                                 ((offset :u16const)))
  (ldr val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-load-complex-single-float-nested :nfp :ref) (((val :complex-single-float))
                                                                       ((offset :u16const))
                                                                       ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (ldr val (:@ nfp-reg (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-complex-single-float :nfp :set) (()
                                                                  ((val :complex-single-float)
                                                                   (offset :u16const)))
  (str val (:@ sp (:$ (:apply + 8 offset)))))

(define-arm64-vinsn (nfp-store-complex-single-float-nested :nfp :set) (()
                                                                        ((val :complex-single-float)
                                                                         (offset :u16const))
                                                                        ((nfp-reg :imm)))
  (ldr nfp-reg (:@ rcontext (:$ arm64::tcr.nfp)))
  (str val (:@ nfp-reg (:$ (:apply + 8 offset)))))

;;; --- NVR save/restore ---
;;; Push/pop non-volatile registers to/from vstack.
;;; ARM64 NVRs: save0-save7 (x16-x23).
;;; N is the register number of the first NVR to save (save0=lowest).

(define-arm64-vinsn (save-nvrs :push :node :vsp :multiple) (()
                                                             ((n :u8const)))
  (str save0 (:@! vsp (:$ (- arm64::node-size))))
  ((:pred <= n 1)
   (str save1 (:@! vsp (:$ (- arm64::node-size))))
   ((:pred <= n 2)
    (str save2 (:@! vsp (:$ (- arm64::node-size))))
    ((:pred <= n 3)
     (str save3 (:@! vsp (:$ (- arm64::node-size))))
     ((:pred <= n 4)
      (str save4 (:@! vsp (:$ (- arm64::node-size))))
      ((:pred <= n 5)
       (str save5 (:@! vsp (:$ (- arm64::node-size))))
       ((:pred <= n 6)
        (str save6 (:@! vsp (:$ (- arm64::node-size))))
        ((:pred <= n 7)
         (str save7 (:@! vsp (:$ (- arm64::node-size))))))))))))

(define-arm64-vinsn (restore-nvrs :pop :node :vsp :multiple) (()
                                                               ((n :u8const)
                                                                (basereg :imm)))
  ((:pred = n 8)
   (ldr save7 (:@+ basereg (:$ arm64::node-size))))
  ((:pred >= n 7)
   (ldr save6 (:@+ basereg (:$ arm64::node-size))))
  ((:pred >= n 6)
   (ldr save5 (:@+ basereg (:$ arm64::node-size))))
  ((:pred >= n 5)
   (ldr save4 (:@+ basereg (:$ arm64::node-size))))
  ((:pred >= n 4)
   (ldr save3 (:@+ basereg (:$ arm64::node-size))))
  ((:pred >= n 3)
   (ldr save2 (:@+ basereg (:$ arm64::node-size))))
  ((:pred >= n 2)
   (ldr save1 (:@+ basereg (:$ arm64::node-size))))
  (ldr save0 (:@+ basereg (:$ arm64::node-size))))

;;; --- FPR save/restore ---

(define-arm64-vinsn (push-nvfprs :push :multiple) (()
                                                    ((n :u16const)
                                                     (header :u16const)))
  ;; Push a vector header followed by N double-float registers.
  ;; The header word describes the saved block for GC.
  ;; TODO: actual NEON push sequence for d8-d15.
  (nop))

(define-arm64-vinsn (pop-nvfprs :pop :multiple) (()
                                                  ((n :u16const)))
  ;; Pop N saved double-float registers.
  ;; TODO: actual NEON pop sequence.
  (nop))

;;; --- FFI ---

;;; Store a C argument at word index OFFSET in the c-frame.
;;; Byte offset = dnode-size + offset * node-size (skip header+prevsp, then index).
(define-arm64-vinsn (set-aapcs64-c-arg :predicatable) (()
                                                        ((val :u64)
                                                         (offset :u16const)))
  (str val (:@ sp (:$ (:apply + arm64::dnode-size (:apply ash offset arm64::word-shift))))))

(define-arm64-vinsn (set-double-aapcs64-c-arg :predicatable) (()
                                                                ((val :double-float)
                                                                 (offset :u16const)))
  (str val (:@ sp (:$ (:apply + arm64::dnode-size (:apply ash offset arm64::word-shift))))))

(define-arm64-vinsn (set-single-aapcs64-c-arg :predicatable) (()
                                                                ((val :single-float)
                                                                 (offset :u16const)))
  (str val (:@ sp (:$ (:apply + arm64::dnode-size (:apply ash offset arm64::word-shift))))))

;;; --- Misc / forms ---

(define-arm64-vinsn (forms :predicatable) (()
                                            ((v :lisp)))
  ;; This vinsn exists just to note that form V was evaluated for side effect.
  (nop))


;;; In case arm64::*arm64-opcodes* was changed since this file was compiled.
#+maybe-never
(queue-fixup
 (fixup-vinsn-templates *arm64-vinsn-templates* arm64::*arm64-opcode-numbers*))

(provide "ARM64-VINSNS")
