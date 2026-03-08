;;;-*-Mode: LISP; Package: CCL -*-
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

;;; ARM64 thread/stack utilities.
;;; Port of arm-threads-utils.lisp for the ARM64 TBI-tagged architecture.

(in-package "CCL")

(defun %frame-backlink (p &optional context)
  (declare (ignore context))
  (cond ((fake-stack-frame-p p)
         (%fixnum-ref p arm64::fake-stack-frame.next-sp))
        ((fixnump p) (%%frame-backlink p))
        (t (error "~s is not a valid stack frame" p))))



;;; On ARM64, tagged pointers have the tag in the top byte (TBI).
;;; To get the raw address from a catch frame pointer (which is
;;; stack-consed and fixnum-tagged), we need to clear the top byte.
;;; ARM32 cleared low bits via logandc2; ARM64 clears the top byte.
(defun catch-frame-sp (catch)
  (%stack-block ((ptr arm64::node-size))
    (%set-object ptr 0 catch)           ;catch frame is stack-consed
    ;; Clear the top byte (TBI tag) to get the raw address
    (setf (%%get-unsigned-longlong ptr 0)
          (logand (%%get-unsigned-longlong ptr 0) #x00FFFFFFFFFFFFFF))
    (+ (%get-object ptr 0)
       (1+ arm64::catch-frame.element-count))))

(defun fake-stack-frame-p (x)
  (and (typep x 'fixnum)
       (evenp x)
       (eql (%fixnum-ref-natural x)
            (logior (ash arm64::subtag-istruct arm64::subtag-shift)
                    (ash (- arm64::fake-stack-frame.size arm64::node-size)
                         (- arm64::word-shift))))
       (let* ((type (%fixnum-ref x arm64::node-size)))
         (and (consp type)
              (eq (car type) 'arm64::fake-stack-frame)))))

(defun current-fake-stack-frame ()
  (do* ((p (%get-frame-ptr) (%%frame-backlink p)))
       ((or (zerop p) (bottom-of-stack-p p nil)))
    (when (fake-stack-frame-p p) (return p))))



(defun bottom-of-stack-p (p context)
  (and (fixnump p)
       (locally (declare (fixnum p))
	 (let* ((tcr (if context (bt.tcr context) (%current-tcr)))
                (cs-area (%fixnum-ref tcr target::tcr.cs-area)))
	   (not (%ptr-in-area-p p cs-area))))))

;;; ARM64 has no lisp-frame-marker (frames are just 2 slots: savevsp + savelr).
;;; A frame is a lisp frame if it's not fake and not bottom-of-stack.
(defun lisp-frame-p (p context)
  (if (bottom-of-stack-p p context)
    (values nil t)
    (values (or (fake-stack-frame-p p)
                ;; ARM64 has no lisp-frame-marker; all non-fake,
                ;; non-bottom frames are assumed to be lisp frames.
                (not (fake-stack-frame-p p))) nil)))

;;; ARM64 subtag layout:
;;;   bit 7 (0x80) = uvector header flag
;;;   bit 6 (0x40) = uvector reference tag
;;;   bit 5 (0x20) = gvector flag (1=node, 0=ivector) within uvectors
;;;   bits 0-4 = subtype index
;;; A valid subtag has bit 7 set (header) and is a recognized type.
(defun valid-subtag-p (subtag)
  (declare (fixnum subtag))
  (when (logbitp 7 subtag)
    ;; It's a header byte.  Check if gvector or ivector.
    (if (logbitp 5 subtag)
        ;; gvector (nodeheader): index is bits 0-4
        (let* ((idx (logand subtag #x1F)))
          (declare (fixnum idx))
          (not (eq (%svref *nodeheader-types* idx) 'bogus)))
        ;; ivector (immheader): index is bits 0-4
        (let* ((idx (logand subtag #x1F)))
          (declare (fixnum idx))
          (not (eq (%svref *immheader-types* idx) 'bogus))))))



(defun valid-header-p (thing)
  (let* ((typecode (typecode thing)))
    (declare (fixnum typecode))
    (cond
      ;; If the typecode has the uvector-ref bit set, it's a misc object
      ((logbitp 6 typecode) (valid-subtag-p typecode))
      ;; Header bytes shouldn't appear as object tags
      ((logbitp 7 typecode) nil)
      ;; Everything else (fixnum, cons, immediate) is valid
      (t t))))



(defun bogus-thing-p (x)
  (when x
    #+cross-compiling (return-from bogus-thing-p nil)
    (or (not (valid-header-p x))
        (let ((typecode (typecode x)))
          (declare (fixnum typecode))
          (cond
            ;; Fixnums (tag byte 0x00 or 0xFF) are always valid
            ((or (eql (ldb (byte 8 56) (%address-of x)) 0)
                 (eql (ldb (byte 8 56) (%address-of x)) #xFF))
             nil)
            ;; Immediate types (single-float, character, etc) are valid
            ((logbitp 4 typecode) nil)
            ;; Cons cells
            ((eql typecode arm64::tag-cons)
             (unless (or (in-any-consing-area-p x)
                         (temporary-cons-p x))
               t))
            ;; Symbols
            ((eql typecode arm64::subtag-symbol) nil)  ; no stack-consed symbols
            ;; Value cells can be on vstack
            ((eql typecode arm64::subtag-value-cell)
             (not (or (in-any-consing-area-p x)
                      (on-any-vstack x))))
            ;; Other uvector types
            ((logbitp 6 typecode)
             (not (or (in-any-consing-area-p x)
                      (on-any-csp-stack x)
                      (%heap-ivector-p x))))
            ;; Unknown tag
            (t t))))))
