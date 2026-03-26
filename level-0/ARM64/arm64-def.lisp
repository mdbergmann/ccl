;;; -*- Mode: Lisp; Package: CCL -*-
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

;;; ARM64: function layout has only entrypoint as fixed field.
;;; The code vector is element 1 (at offset node-size from tagged ptr).
;;; The entrypoint must be an UNTAGGED code address because ARM64
;;; TBI only applies to data accesses (ldr/str), NOT to instruction
;;; fetches (br/blr).  Strip the TBI tag byte before storing.
(defarm64lapfunction %fix-fn-entrypoint ((func arg_z))
  (ldr temp0 (:@ func (:$ arm64::node-size)))    ; element 1 = code vector (tagged)
  (and temp0 temp0 (:$ #x00FFFFFFFFFFFFFF))      ; strip TBI tag for branch target
  (str temp0 (:@ func (:$ arm64::function.entrypoint)))
  (ret))

;;; Do an FF-CALL to MakeDataExecutable so that the data cache gets flushed.
;;; If the GC moves this function while we're trying to flush the cache,
;;; it'll flush the cache: no harm done in that case.

(defun %make-code-executable (codev)
  (with-macptrs (p)
    (let* ((nbytes (ash (uvsize codev) arm64::word-shift)))
      (%vect-data-to-macptr codev p)
      (ff-call (%kernel-import arm64::kernel-import-MakeDataExecutable)
               :address p
               :unsigned-doubleword nbytes
               :void))))

;;; Allocate an xcode-vector in the MAP_JIT code area (AREA_CODE).
;;; element-count is a fixnum (= raw count since fixnumshift=0).
;;; Returns a macptr whose address is the untagged data address of
;;; the new code vector in the code area.  The code area is left
;;; WRITABLE — caller must write instruction data then call
;;; %make-code-vector-executable.
;;;
;;; To get a tagged Lisp ivector reference for storing in function
;;; slots, use %code-vector-macptr-to-tagged.
(defun %alloc-code-vector (element-count)
  (let* ((addr (ff-call (%kernel-import arm64::kernel-import-alloc-code-vector)
                        :unsigned-doubleword element-count
                        :address)))
    addr))

;;; Toggle the code area back to executable and flush icache.
;;; addr is a macptr (or fixnum address) pointing to the code vector data.
(defun %make-code-vector-executable (addr)
  (ff-call (%kernel-import arm64::kernel-import-make-code-vector-executable)
           :address addr
           :void))

;;; ARM64: rnil holds the nil value.  Kernel globals are at negative
;;; offsets from rnil.  The offset arg is a fixnum byte offset.
;;; With fixnumshift=0, the offset IS the byte offset.
(defarm64lapfunction %get-kernel-global-from-offset ((offset arg_z))
  (check-nargs 1)
  (sub imm0 rnil offset)
  (ldr arg_z (:@ imm0 (:$ 0)))
  (ret))


(defarm64lapfunction %set-kernel-global-from-offset ((offset arg_y) (new-value arg_z))
  (check-nargs 2)
  (sub imm0 rnil offset)
  (str new-value (:@ imm0 (:$ 0)))
  (ret))



(defarm64lapfunction %get-kernel-global-ptr-from-offset ((offset arg_y)
                                                         (ptr arg_z))
  (check-nargs 2)
  (sub imm0 rnil offset)
  (ldr imm0 (:@ imm0 (:$ 0)))
  (str imm0 (:@ ptr (:$ arm64::macptr.address)))
  (ret))




(defarm64lapfunction %fixnum-ref ((fixnum arg_y) #| &optional |# (offset arg_z))
  (:arglist (fixnum &optional offset))
  (check-nargs 1 2)
  (cmp nargs (:$ 8))                    ; 1 arg = 1*8 = 8
  (b.ne @two)
  (mov fixnum offset)
  (mov offset (:$ 0))
  @two
  ;; ARM64: fixnumshift=0, unbox-fixnum is identity
  (ldr arg_z (:@ fixnum offset))
  (ret))


(defarm64lapfunction %fixnum-ref-natural ((fixnum arg_y) #| &optional |# (offset arg_z))
  (:arglist (fixnum &optional offset))
  (check-nargs 1 2)
  (cmp nargs (:$ 8))
  (b.ne @two)
  (mov fixnum offset)
  (mov offset (:$ 0))
  @two
  (ldr imm0 (:@ fixnum offset))
  (spjump .SPmakeu64))



(defarm64lapfunction %fixnum-set ((fixnum arg_x) (offset arg_y) #| &optional |# (new-value arg_z))
  (:arglist (fixnum offset &optional new-value))
  (check-nargs 2 3)
  (cmp nargs (:$ 16))                   ; 2 args = 2*8 = 16
  (b.ne @three)
  (mov fixnum offset)
  (mov offset (:$ 0))
  @three
  (str new-value (:@ fixnum offset))
  (mov arg_z new-value)
  (ret))

(defarm64lapfunction %fixnum-set-natural ((fixnum arg_x) (offset arg_y) #| &optional |# (new-value arg_z))
  (check-nargs 2 3)
  (cmp nargs (:$ 16))
  (b.ne @three)
  (mov fixnum offset)
  (mov offset (:$ 0))
  @three
  (test-fixnum new-value)
  (mov imm2 new-value)
  (b.eq @store)
  (extract-subtag imm1 new-value)
  (cmp imm1 (:$ arm64::subtag-bignum))
  (b.eq @ok1)
  (uuo-error-reg-not-xtype new-value (:$ arm64::xtype-u64))
  @ok1
  (getvheader imm0 new-value)
  (header-length temp0 imm0)
  ;; ARM64: bignum digits are 32-bit, so a u64 fits in 2 digits.
  ;; Load the 64-bit value from the bignum data area.
  (cmp temp0 (:$ 2))
  (b.gt @toobig)
  (ldr imm2 (:@ new-value (:$ arm64::misc-data-offset)))
  (b.eq @check-two-digit)
  ;; 1-digit bignum: check non-negative
  (cmp imm2 (:$ 0))
  (b.ge @store)
  (uuo-error-reg-not-xtype new-value (:$ arm64::xtype-u64))
  @check-two-digit
  ;; 2-digit bignum: the 64-bit value is loaded; ensure it fits u64
  ;; (it always does for a 2-digit bignum with positive sign)
  (b @store)
  @toobig
  (uuo-error-reg-not-xtype new-value (:$ arm64::xtype-u64))
  @store
  (str imm2 (:@ fixnum offset))
  (mov arg_z new-value)
  (ret))



(defarm64lapfunction %current-frame-ptr ()
  (check-nargs 0)
  (mov arg_z sp)
  (ret))

(defarm64lapfunction %current-vsp ()
  (check-nargs 0)
  (mov arg_z vsp)
  (ret))




(defarm64lapfunction %set-current-vsp ((new-vsp arg_z))
  (check-nargs 1)
  (mov vsp new-vsp)
  (ret))



;;; ARM64 lisp frame is (savevsp, savelr), 16 bytes.
;;; No marker word, no fn save.
;;; Stack frame backlink walking needs to know the frame layout.
;;; This is a simplified version; the full implementation depends
;;; on the kernel's stack conventions.
(defarm64lapfunction %%frame-backlink ((p arg_z))
  (check-nargs 1)
  ;; ARM64 lisp frame: savevsp at offset 0, savelr at offset 8.
  ;; The savevsp IS the backlink on the value stack side.
  ;; On the control stack side, frames are 16-byte aligned.
  ;; For now, return p + lisp-frame.size as the next frame.
  (add arg_z p (:$ arm64::lisp-frame.size))
  (ret))


(defarm64lapfunction %%frame-savevsp ((p arg_z))
  (check-nargs 1)
  (ldr arg_z (:@ arg_z (:$ arm64::lisp-frame.savevsp)))
  (ret))


(defarm64lapfunction %uvector-data-fixnum ((uv arg_z))
  (check-nargs 1)
  ;; ARM64: misc-data-offset = 0, so the tagged pointer IS the data address.
  ;; With TBI, the tag byte is ignored for memory access.
  (mov arg_z uv)
  (ret))

(defarm64lapfunction %catch-top ((tcr arg_z))
  (check-nargs 1)
  (ldr arg_z (:@ tcr (:$ arm64::tcr.catch-top)))
  (cmp arg_z (:$ 0))
  (b.ne @done)
  (mov arg_z rnil)
  @done
  (ret))




;;; Same as %address-of, but doesn't cons any bignums
;;; It also left shift fixnums just like everything else.
(defarm64lapfunction %fixnum-address-of ((x arg_z))
  (check-nargs 1)
  ;; ARM64: fixnumshift=0, box-fixnum is identity
  (box-fixnum arg_z x)
  (ret))

(defarm64lapfunction %dnode-address-of ((x arg_z))
  (check-nargs 1)
  ;; Clear the tag byte (top 8 bits) and align to dnode (16 bytes).
  ;; First clear tag byte:
  (lsl arg_z x (:$ 8))
  (lsr arg_z arg_z (:$ 8))
  ;; Then clear low 4 bits (dnode-align):
  (and arg_z arg_z (:$ -16))
  (ret))

(defarm64lapfunction %save-standard-binding-list ((bindings arg_z))
  (ldr imm0 (:@ rcontext (:$ arm64::tcr.vs-area)))
  (ldr imm1 (:@ imm0 (:$ arm64::area.high)))
  (push1 bindings imm1)
  (ret))

(defarm64lapfunction %saved-bindings-address ()
  (ldr imm0 (:@ rcontext (:$ arm64::tcr.vs-area)))
  (ldr imm1 (:@ imm0 (:$ arm64::area.high)))
  (sub arg_z imm1 (:$ arm64::node-size))
  (ret))

(defarm64lapfunction %code-vector-pc ((code-vector arg_y) (pcptr arg_z))
  (build-lisp-frame)
  (macptr-ptr imm0 pcptr)
  (ldr lr (:@ imm0 (:$ 0)))
  (sub imm0 lr code-vector)
  ;; ARM64: misc-data-offset = 0, so no subtraction needed.
  (getvheader imm1 code-vector)
  (header-size imm1 imm1)
  ;; Compare PC offset against code vector size in bytes (element-count * 4 for 32-bit code)
  (lsl imm1 imm1 (:$ 2))
  (cmp imm0 imm1)
  (b.hs @no)
  ;; Return the PC offset as a fixnum
  (mov arg_z imm0)
  (vpush1 arg_y)
  (vpush1 arg_z)
  (b @go)
  @no
  (vpush1 rnil)
  (vpush1 rnil)
  @go
  (set-nargs 2)
  (spjump .SPnvalret))



;;; ARM64: AAPCS64 calling convention.
;;; The C frame and FFI calling are fundamentally different from ARM32 EABI.
(defarm64lapfunction %do-ff-call ((tag arg_x) (result arg_y) (entry arg_z))
  (stp tag result (:@! vsp (:$ -16)))
  (spcall .SPaapcs64-ff-call-simple)
  (ldp tag result (:@+ vsp (:$ 16)))
  (macptr-ptr imm2 result)
  ;; Store integer result (x0) and FP result (d0).
  (str imm0 (:@ imm2 (:$ 0)))
  (str d0 (:@ imm2 (:$ 8)))
  (vpush1 tag)
  (mov arg_z rnil)
  (vpush1 arg_z)
  (set-nargs 1)
  (spcall .SPthrow)
  ;; Should not return
  (ret))

(defun %ff-call (entry &rest specs-and-vals)
  (declare (dynamic-extent specs-and-vals))
  (let* ((len (length specs-and-vals))
         (total-words 0)
         (fp-words 8))                          ; AAPCS64: 8 FP arg slots (d0-d7)
    (declare (fixnum len total-words fp-words))
    (let* ((result-spec (or (car (last specs-and-vals)) :void))
           (nargs (ash (the fixnum (1- len)) -1)))
      (declare (fixnum nargs))
      (ecase result-spec
        ((:address :unsigned-doubleword :signed-doubleword
                   :single-float :double-float
                   :signed-fullword :unsigned-fullword
                   :signed-halfword :unsigned-halfword
                   :signed-byte :unsigned-byte
                   :void)
         (do* ((i 0 (1+ i))
               (specs specs-and-vals (cddr specs))
               (spec (car specs) (car specs)))
              ((= i nargs))
           (declare (fixnum i))
           (case spec
             ((:address :signed-doubleword :unsigned-doubleword
                        :signed-fullword :unsigned-fullword
                        :signed-halfword :unsigned-halfword
                        :signed-byte :unsigned-byte)
              (incf total-words))
             (:single-float
              (if (> fp-words 0)
                (decf fp-words)
                (incf total-words)))
             (:double-float
              (if (> fp-words 0)
                (decf fp-words)
                (incf total-words)))
             (t (if (typep spec 'unsigned-byte)
                  (incf total-words spec)
                  (error "unknown arg spec ~s" spec)))))
         ;; It's necessary to ensure that the C frame is the youngest thing on
         ;; the foreign stack here.
         (let* ((tag (cons nil nil)))
           (declare (dynamic-extent tag))
           (%stack-block ((result 16))
             (catch tag
               (with-macptrs ((argptr))
                 (with-variable-c-frame
                     (+ total-words 16) frame
                     (%setf-macptr-to-object argptr frame)
                     (let* ((fp-arg-offset 8)
                            (arg-offset 72))    ; 8 GPR slots * 8 bytes + 8 bytes
                       (declare (fixnum arg-offset fp-arg-offset))
                       (do* ((i 0 (1+ i))
                             (specs specs-and-vals (cddr specs))
                             (spec (car specs) (car specs))
                             (val (cadr specs) (cadr specs)))
                            ((= i nargs))
                         (declare (fixnum i))
                         (case spec
                           (:address
                            (setf (%get-ptr argptr arg-offset) val)
                            (incf arg-offset 8))
                           ((:signed-doubleword :signed-fullword :signed-halfword :signed-byte)
                            (setf (%%get-signed-longlong argptr arg-offset) val)
                            (incf arg-offset 8))
                           ((:unsigned-doubleword :unsigned-fullword :unsigned-halfword :unsigned-byte)
                            (setf (%%get-unsigned-longlong argptr arg-offset) val)
                            (incf arg-offset 8))
                           (:double-float
                            (cond ((<= fp-arg-offset 64)
                                   (setf (%get-double-float argptr fp-arg-offset) val)
                                   (incf fp-arg-offset 8))
                                  (t
                                   (setf (%get-double-float argptr arg-offset) val)
                                   (incf arg-offset 8))))
                           (:single-float
                            (cond ((< fp-arg-offset 72)
                                   (setf (%get-single-float argptr fp-arg-offset) val)
                                   (incf fp-arg-offset 8))
                                  (t
                                   (setf (%get-single-float argptr arg-offset) val)
                                   (incf arg-offset 8))))
                           (t
                              (let* ((p 0))
                                (declare (fixnum p))
                                (dotimes (i (the fixnum spec))
                                  (setf (%get-ptr argptr arg-offset) (%get-ptr val p))
                                  (incf p 8)
                                  (incf arg-offset 8)))))))
                         (%do-ff-call tag result entry))))
             (ecase result-spec
               (:void nil)
               (:address (%get-ptr result 0))
               (:unsigned-byte (%get-unsigned-byte result 0))
               (:signed-byte (%get-signed-byte result 0))
               (:unsigned-halfword (%get-unsigned-word result 0))
               (:signed-halfword (%get-signed-word result 0))
               (:unsigned-fullword (%get-unsigned-long result 0))
               (:signed-fullword (%get-signed-long result 0))
               (:unsigned-doubleword (%%get-unsigned-longlong result 0))
               (:signed-doubleword (%%get-signed-longlong result 0))
               (:single-float (%get-single-float result 8))
               (:double-float (%get-double-float result 8))))))))))



(defarm64lapfunction %get-object ((macptr arg_y) (offset arg_z))
  (check-nargs 2)
  (trap-unless-xtype= arg_y arm64::subtag-macptr)
  (trap-unless-fixnum arg_z)
  (macptr-ptr imm0 arg_y)
  (ldr arg_z (:@ imm0 arg_z))
  (ret))


(defarm64lapfunction %set-object ((macptr arg_x) (offset arg_y) (value arg_z))
  (check-nargs 3)
  (trap-unless-xtype= arg_x arm64::subtag-macptr)
  (trap-unless-fixnum arg_y)
  (macptr-ptr imm0 arg_x)
  (str arg_z (:@ imm0 arg_y))
  (ret))


(defarm64lapfunction %apply-lexpr-with-method-context ((magic arg_x)
                                                     (function arg_y)
                                                     (args arg_z))
  ;; Put magic arg in next-method-context (= temp1).
  ;; Put function in nfn (= temp2).
  ;; Set nargs to 0, then spread "args" on stack.
  ;; Jump to the function in nfn.
  (mov next-method-context magic)
  (mov nfn function)
  (set-nargs 0)
  (build-lisp-frame)
  (spcall .SPspread-lexprz)
  (ldr lr (:@ sp (:$ arm64::lisp-frame.savelr)))
  (discard-lisp-frame)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))


(defarm64lapfunction %apply-with-method-context ((magic arg_x)
                                               (function arg_y)
                                               (args arg_z))
  (mov next-method-context magic)
  (mov nfn function)
  (set-nargs 0)
  (build-lisp-frame)
  (spcall .SPspreadargz)
  (ldr lr (:@ sp (:$ arm64::lisp-frame.savelr)))
  (discard-lisp-frame)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))




(defarm64lapfunction %apply-lexpr-tail-wise ((method arg_y) (args arg_z))
  ;; See ARM32 version for detailed comments.
  ;; Lexpr-cleanup: check if multiple-value context.
  (ref-global imm0 ret1valaddr)
  (cmp lr imm0)
  (ldr nargs (:@ args (:$ 0)))
  (mov nfn method)
  (b.ne @no-discard)
  (add sp sp (:$ arm64::lisp-frame.size))  ; discard extra frame
  @no-discard
  ;; Restore from lisp frame
  (ldr lr (:@ sp (:$ arm64::lisp-frame.savelr)))
  (ldr imm0 (:@ sp (:$ arm64::lisp-frame.savevsp)))
  (sub vsp imm0 nargs)
  (add sp sp (:$ arm64::lisp-frame.size))
  ;; Pop argregs based on nargs
  (cmp nargs (:$ 0))
  (b.eq @go)
  (vpop1 arg_z)
  (cmp nargs (:$ 16))                   ; 2 args = 16
  (b.lo @go)
  (vpop1 arg_y)
  (b.eq @go)
  (vpop1 arg_x)
  @go
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))


(defun %copy-function (proto &optional target)
  (let* ((total-size (uvsize proto))
         (new (or target (allocate-typed-vector :function total-size))))
    (declare (fixnum total-size))
    (when target
      (unless (eql total-size (uvsize target))
        (error "Wrong size target ~s" target)))
    (%copy-gvector-to-gvector proto 0 new 0 total-size)
    (%fix-fn-entrypoint new)))

(defun replace-function-code (target-fn proto-fn)
  (if (typep target-fn 'function)
    (if (typep proto-fn 'function)
      (progn
        (setf (uvref target-fn 0) (%lookup-subprim-address
                                   #.(arm64::arm64-subprimitive-offset '.SPfix-nfn-entrypoint))
              (uvref target-fn 1) (uvref proto-fn 1))
        (%fix-fn-entrypoint target-fn))
      (report-bad-arg proto-fn 'function))
    (report-bad-arg target-fn 'function)))

(defun closure-function (fun)
  (while (and (functionp fun)  (not (compiled-function-p fun)))
    (setq fun (%svref fun 2))
    (when (vectorp fun)
      (setq fun (svref fun 0))))
  fun)


;;; For use by (setf (apply ...) ...)
;;; (apply+ f butlast last) = (apply f (append butlast (list last)))
(defarm64lapfunction apply+ ()
  (:arglist (function arg1 arg2 &rest other-args))
  (check-nargs 3 nil)
  (vpush1 arg_x)
  (mov temp0 arg_z)                     ; last
  (mov arg_z arg_y)                     ; butlast
  (sub nargs nargs (:$ 16))            ; remove count for butlast & last (2*8)
  (build-lisp-frame)
  (spcall .SPspreadargz)
  (cmp nargs (:$ 24))                  ; 3*8 = 24
  (ldr lr (:@ sp (:$ arm64::lisp-frame.savelr)))
  (discard-lisp-frame)
  (add nargs nargs (:$ 8))            ; count for last (1*8)
  (b.lo @no-push)
  (str arg_x (:@! vsp (:$ (- arm64::node-size))))
  @no-push
  (mov arg_x arg_y)
  (mov arg_y arg_z)
  (mov arg_z temp0)
  (ldr nfn (:@ nfn 'funcall))
  (spjump .SPfuncall))

(defarm64lapfunction %lookup-subprim-address ((subp arg_z))
  ;; ARM64: fixnumshift=0, so subp IS the byte offset into TCR subprim table.
  (ldr imm0 (:@ rcontext subp))
  (spjump .SPmakeu64))

;;; end of arm64-def.lisp
