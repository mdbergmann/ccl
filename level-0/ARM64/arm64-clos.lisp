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

;;; It's easier to keep this is LAP; we want to play around with its
;;; constants.

;;; This just maps a SLOT-ID to a SLOT-DEFINITION or NIL.
;;; The map is a vector of (UNSIGNED-BYTE 8); this should
;;; be used when there are less than 255 slots in the class.
(defarm64lapfunction %small-map-slot-id-lookup ((slot-id arg_z))
  (ldr temp1 (:@ nfn 'map))
  (svref arg_x slot-id.index slot-id)
  (getvheader imm0 temp1)
  (header-length imm1 imm0)
  (ldr temp0 (:@ nfn 'table))
  (cmp arg_x imm1)
  ;; ARM64: fixnumshift=0, misc-data-offset=0.
  ;; arg_x is the raw index; byte offset into the u8 map is just arg_x.
  (b.hs @default)
  (ldrb imm1 (:@ temp1 arg_x))
  ;; Scale byte value to node offset: imm1 * 8 (word-shift=3).
  (lsl imm1 imm1 (:$ arm64::word-shift))
  (add imm1 imm1 (:$ arm64::misc-data-offset))
  (ldr arg_z (:@ temp0 imm1))
  (ret)
  @default
  (mov imm1 (:$ arm64::misc-data-offset))
  (ldr arg_z (:@ temp0 imm1))
  (ret))

;;; The same idea, only the map is a vector of (UNSIGNED-BYTE 32).
(defarm64lapfunction %large-map-slot-id-lookup ((slot-id arg_z))
  (ldr temp1 (:@ nfn 'map))
  (svref arg_x slot-id.index slot-id)
  (getvheader imm0 temp1)
  (header-length imm1 imm0)
  (ldr temp0 (:@ nfn 'table))
  (cmp arg_x imm1)
  (b.hs @default)
  ;; ARM64: 32-bit elements in the map.  Scale index by 4.
  (lsl imm0 arg_x (:$ 2))
  (add imm0 imm0 (:$ arm64::misc-data-offset))
  (ldr imm1 (:@ temp1 imm0))
  ;; Scale to node offset
  (lsl imm1 imm1 (:$ arm64::word-shift))
  (add imm1 imm1 (:$ arm64::misc-data-offset))
  (ldr arg_z (:@ temp0 imm1))
  (ret)
  @default
  (mov imm1 (:$ arm64::misc-data-offset))
  (ldr arg_z (:@ temp0 imm1))
  (ret))

(defarm64lapfunction %small-slot-id-value ((instance arg_y) (slot-id arg_z))
  (ldr temp1 (:@ nfn 'map))
  (svref arg_x slot-id.index slot-id)
  (getvheader imm0 temp1)
  (ldr temp0 (:@ nfn 'table))
  (header-length imm1 imm0)
  (cmp arg_x imm1)
  (b.hs @missing)
  (ldrb imm1 (:@ temp1 arg_x))
  (cmp imm1 (:$ 0))
  (b.eq @missing)
  (lsl imm1 imm1 (:$ arm64::word-shift))
  (add imm1 imm1 (:$ arm64::misc-data-offset))
  (ldr arg_z (:@ temp0 imm1))
  (ldr arg_x (:@ nfn 'class))
  (ldr nfn (:@ nfn '%maybe-std-slot-value))
  (set-nargs 3)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr)
  @missing                              ; (%slot-id-ref-missing instance id)
  (ldr nfn (:@ nfn '%slot-id-ref-missing))
  (set-nargs 2)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))

(defarm64lapfunction %large-slot-id-value ((instance arg_y) (slot-id arg_z))
  (ldr temp1 (:@ nfn 'map))
  (svref arg_x slot-id.index slot-id)
  (getvheader imm0 temp1)
  (ldr temp0 (:@ nfn 'table))
  (header-length imm1 imm0)
  (cmp arg_x imm1)
  (b.hs @missing)
  ;; 32-bit map element
  (lsl imm0 arg_x (:$ 2))
  (add imm0 imm0 (:$ arm64::misc-data-offset))
  (ldr imm1 (:@ temp1 imm0))
  ;; On ARM64, fixnumshift=0, so no shift needed.  Scale to node offset.
  (lsl imm1 imm1 (:$ arm64::word-shift))
  (add imm1 imm1 (:$ arm64::misc-data-offset))
  (cmp imm1 (:$ arm64::misc-data-offset))
  (b.eq @missing)
  (ldr arg_x (:@ nfn 'class))
  (ldr arg_z (:@ temp0 imm1))
  (ldr nfn (:@ nfn '%maybe-std-slot-value-using-class))
  (set-nargs 3)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr)
  @missing                              ; (%slot-id-ref-missing instance id)
  (ldr nfn (:@ nfn '%slot-id-ref-missing))
  (set-nargs 2)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))


(defarm64lapfunction %small-set-slot-id-value ((instance arg_x)
                                             (slot-id arg_y)
                                             (new-value arg_z))
  (ldr temp1 (:@ nfn 'map))
  (svref temp0 slot-id.index slot-id)
  (getvheader imm0 temp1)
  (header-length imm1 imm0)
  (cmp temp0 imm1)
  (ldr temp0 (:@ nfn 'table))
  (b.hs @missing)
  (ldrb imm1 (:@ temp1 arg_x))
  (cmp imm1 (:$ 0))
  (b.eq @missing)
  (lsl imm1 imm1 (:$ arm64::word-shift))
  (add imm1 imm1 (:$ arm64::misc-data-offset))
  @have-scaled-table-index
  (ldr temp1 (:@ nfn 'class))
  (ldr arg_y (:@ temp0 imm1))
  (ldr nfn (:@ nfn '%maybe-std-setf-slot-value-using-class))
  (set-nargs 4)
  (vpush1 temp1)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr)
  @missing                              ; (%slot-id-set-missing instance id new-value)
  (ldr nfn (:@ nfn '%slot-id-set-missing))
  (set-nargs 3)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))

(defarm64lapfunction %large-set-slot-id-value ((instance arg_x)
                                             (slot-id arg_y)
                                             (new-value arg_z))
  (ldr temp1 (:@ nfn 'map))
  (svref temp0 slot-id.index slot-id)
  (getvheader imm0 temp1)
  (header-length imm1 imm0)
  (cmp temp0 imm1)
  (ldr temp0 (:@ nfn 'table))
  (b.hs @missing)
  ;; 32-bit map element
  (lsl imm0 arg_x (:$ 2))
  (add imm0 imm0 (:$ arm64::misc-data-offset))
  (ldr imm1 (:@ temp1 imm0))
  (lsl imm1 imm1 (:$ arm64::word-shift))
  (add imm1 imm1 (:$ arm64::misc-data-offset))
  (cmp imm1 (:$ arm64::misc-data-offset))
  (b.eq @missing)
  @have-scaled-table-index
  (ldr temp1 (:@ nfn 'class))
  (ldr arg_y (:@ temp0 imm1))
  (ldr nfn (:@ nfn '%maybe-std-setf-slot-value-using-class))
  (set-nargs 4)
  (vpush1 temp1)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr)
  @missing                              ; (%slot-id-set-missing instance id new-value)
  (ldr nfn (:@ nfn '%slot-id-ref-missing))
  (set-nargs 3)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))

(defparameter *gf-proto*
  (nfunction
   gag
   (lambda (&lap &lexpr args)
     (arm64-lap-function
      gag
      ()
      (vpush-argregs)
      (vpush1 nargs)
      (ref-global arg_x ret1valaddr)
      (add imm1 vsp nargs)
      (add imm1 imm1 (:$ arm64::node-size))         ; caller's vsp
      (cmp lr arg_x)
      (build-lisp-frame imm1)
      (b.ne @single-value)
      ;; Multiple-value return: push lexpr-return frame, redirect lr.
      (ref-global imm0 lexpr-return)
      (mov imm1 (:$ 0))
      (stp imm1 imm0 (:@! sp (:$ -16)))             ; push marker + lexpr-return
      (mov lr arg_x)                                  ; lr = ret1valaddr
      (b @call)
      @single-value
      ;; Single-value return: redirect lr to lexpr-return1v.
      (ref-global lr lexpr-return1v)
      @call
      (mov arg_z vsp)
      (nth-immediate arg_y gf.dispatch-table nfn)    ; dispatch-table
      (set-nargs 2)
      (nth-immediate nfn gf.dcode nfn)               ; dcode function
      (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
      (br lr)))))



(defarm64lapfunction funcallable-trampoline ()
  (nth-immediate nfn gf.dcode nfn)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))

;;; This can't reference any of the function's constants.
(defarm64lapfunction unset-fin-trampoline ()
  (build-lisp-frame)
  (spcall .SPheap-rest-arg)
  (vpop1 arg_z)                          ; whoops, didn't really want to
  (mov arg_x (:$ #.$XNOFINFUNCTION))
  (mov arg_y nfn)
  (set-nargs 3)
  (spcall .SPksignalerr)
  (mov arg_z rnil)
  (return-lisp-frame))

;;; is a winner - saves ~15%
(defarm64lapfunction gag-one-arg ((arg arg_z))
  (check-nargs 1)
  (nth-immediate arg_y gf.dispatch-table nfn) ; mention dt first
  (set-nargs 2)
  (nth-immediate nfn gf.dcode nfn)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))


(defarm64lapfunction gag-two-arg ((arg0 arg_y) (arg1 arg_z))
  (check-nargs 2)
  (nth-immediate arg_x gf.dispatch-table nfn) ; mention dt first
  (set-nargs 3)
  (nth-immediate nfn gf.dcode nfn)
  (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
  (br lr))

(defparameter *cm-proto*
  (nfunction
   gag
   (lambda (&lap &lexpr args)
     (arm64-lap-function
      gag
      ()
      (vpush-argregs)
      (vpush1 nargs)
      (ref-global arg_x ret1valaddr)
      (add imm1 vsp nargs)
      (add imm1 imm1 (:$ arm64::node-size))         ; caller's vsp
      (cmp lr arg_x)
      (build-lisp-frame imm1)
      (b.ne @single-value)
      ;; Multiple-value return: push lexpr-return frame, redirect lr.
      (ref-global imm0 lexpr-return)
      (mov imm1 (:$ 0))
      (stp imm1 imm0 (:@! sp (:$ -16)))             ; push marker + lexpr-return
      (mov lr arg_x)                                  ; lr = ret1valaddr
      (b @call)
      @single-value
      ;; Single-value return: redirect lr to lexpr-return1v.
      (ref-global lr lexpr-return1v)
      @call
      (mov arg_z vsp)
      (nth-immediate arg_y combined-method.thing nfn) ; thing
      (set-nargs 2)
      (nth-immediate nfn combined-method.dcode nfn)   ; dcode function
      (ldr lr (:@ nfn (:$ arm64::function.entrypoint)))
      (br lr)))))
