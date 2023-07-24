;;;; Cyclic Redundancy Checks
;;;
;;; So far we implement CRC-32 and CRC-64. If we add any more, this file could
;;; use a refactor; the CRC implementations are all very similar.
(cl:in-package #:semz.decompress)

;;;; CRC-32
;;;
;;; We normally use the textbook bytewise implementation that can be found
;;; anywhere; on SBCL, we use the sliced implementation from
;;; https://create.stephan-brumme.com/crc32/ instead, which cuts runtime down to
;;; some 60%, but needs efficient bit operations on 32-bit integers to be good.
;;;
;;; Chipz contains an implementation using 16-bit arithmetic that claims to be
;;; less cons-heavy on 32-bit implementations, but at least under ABCL (which
;;; has 32-bit signed fixnums even on 64-bit implementations), it still seems to
;;; be significantly slower, so I didn't bother with that. Maybe not the best
;;; kind of benchmark since ABCL is wonky, but I had no 32-bit impls at hand.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (declaim (type (simple-array (unsigned-byte 32) (256)) +crc-32-table+))
  (define-constant +crc-32-table+
      (let* ((result (make-array 256 :element-type '(unsigned-byte 32)))
             (magic #xEDB88320))
        (dotimes (i 256 result)
          (let ((next i))
            (dotimes (j 8)
              (setf next (if (logbitp 0 next)
                             (logxor (ash next -1) magic)
                             (ash next -1))))
            (setf (aref result i) next))))
    :test 'equalp))

(defmacro define-basic-update-crc (function-name base-table-constant)
  `(defun ,function-name (data start end state)
     (declare (type buffer data)
              (type array-length start end)
              (type (unsigned-byte 32) state)
              (optimize speed))
     (assert (<= 0 start end (length data)))
     ;; Safety 0 makes a crazy difference under ECL (2.8x) and improves CCL a
     ;; bit as well (1.16x).
     (locally (declare (optimize (safety 0)))
       (loop :while (< start end) :do
         (setf state (logxor (aref ,base-table-constant
                                   (logand #xFF (logxor state (aref data start))))
                             (ash state -8)))
         (incf start)))
     state))

;; The parameter 2 is derived empirically. 3 gives about the same performance
;; but requires larger tables. 1 and 4 are slower. If you wanted to do
;; something really cursed, you could benchmark this at compile time and
;; choose the implementation and parameters based on the results.
(defmacro define-fast-update-crc (function-name remainder-function base-table-constant)
  (let* ((var-count 2)
         (vars (map-into (make-list var-count) #'gensym))
         (table-count (* 4 var-count))
         (table (make-array (list table-count 256) :element-type '(unsigned-byte 32))))
    (assert (>= table-count 4))
    (dotimes (i 256)
      (setf (aref table 0 i) (aref (eval base-table-constant) i)))
    (dotimes (i 256)
      (loop :for j :from 1 :below table-count :do
        (setf (aref table j i)
              (logxor (ash (aref table (- j 1) i) -8)
                      (aref table 0 (logand #xFF (aref table (- j 1) i)))))))

    `(defun ,function-name (data start end state)
       (declare (type buffer data)
                (type array-length start end)
                (type (unsigned-byte 32) state)
                (optimize speed))
       (let ((table ,table))
         (declare (type (simple-array (unsigned-byte 32) (,table-count 256)) table))
         (loop :while (>= (- end start) ,(* 4 var-count)) :do
           (let (,@(loop :for v :in vars
                         :for off :from 0 :by 4
                         :collect `(,v (locally (declare (optimize (safety 0)))
                                         (ub32ref/le data (+ start ,off))))))
             (declare (type (unsigned-byte 32) ,@vars))
             (setf ,(first vars) (logxor state ,(first vars)))
             (setf state (logxor
                          ,@(loop :for v :in vars
                                  :for index :downfrom table-count :by 4
                                  :collect `(aref table ,(- index 1) (ldb (byte 8 0) ,v))
                                  :collect `(aref table ,(- index 2) (ldb (byte 8 8) ,v))
                                  :collect `(aref table ,(- index 3) (ldb (byte 8 16) ,v))
                                  :collect `(aref table ,(- index 4) (ldb (byte 8 24) ,v)))))
             (incf start ,table-count))))
       ;; Deal with remaining bytes
       (,remainder-function data start end state))))

(defmacro define-update-crc (function-name base-table-constant)
  (with-gensyms (basic-update fast-update)
    `(progn
       (define-basic-update-crc ,basic-update ,base-table-constant)
       (define-fast-update-crc ,fast-update ,basic-update ,base-table-constant)
       (defun ,function-name (data start end state)
         (#+sbcl ,fast-update
          #-sbcl ,basic-update
          data start end state)))))

(define-update-crc update-crc-32 +crc-32-table+)

(defun start-crc-32 ()
  #xFFFFFFFF)
(defun finish-crc-32 (state)
  (logxor #xFFFFFFFF state))
(defun crc-32 (data start end)
  (finish-crc-32 (update-crc-32 data start end (start-crc-32))))




;;;; CRC-64
;;;
;;; The textbook implementation is good enough for SBCL (and ABCL, amusingly
;;; enough), but CCL chokes on it pretty badly, so we provide a second
;;; implementation in terms of 32-bit integers. For ECL it makes little
;;; performance difference, but the 32-bit version puts less pressure on the GC.

(eval-when (:compile-toplevel :load-toplevel :execute)
  (declaim (type (simple-array (unsigned-byte 64) (256)) +crc-64-table+))
  (define-constant +crc-64-table+
      (let* ((result (make-array 256 :element-type '(unsigned-byte 64)))
             (magic #xC96C5795D7870F42))
        (dotimes (i 256 result)
          (let ((next i))
            (dotimes (j 8)
              (setf next (if (logbitp 0 next)
                             (logxor (ash next -1) magic)
                             (ash next -1))))
            (setf (aref result i) next))))
    :test 'equalp)

  (declaim (type (simple-array (unsigned-byte 32) (256 2)) +split-crc-64-table+))
  (define-constant +split-crc-64-table+
      (let* ((result (make-array '(256 2) :element-type '(unsigned-byte 32))))
        (dotimes (i 256 result)
          (setf (aref result i 0) (ldb (byte 32  0) (aref +crc-64-table+ i))
                (aref result i 1) (ldb (byte 32 32) (aref +crc-64-table+ i)))))
    :test 'equalp))

(defun start-crc-64 ()
  (- (expt 2 64) 1))

(defun finish-crc-64 (state)
  (logxor (- (expt 2 64) 1) state))

(defun basic-update-crc-64 (data start end state)
  (declare (type buffer data)
           (type array-length start end)
           (type (unsigned-byte 64) state)
           ;; Silence complaints about the return value.
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note)
           (optimize speed))
  (assert (<= 0 start end (length data)))
  (locally (declare (optimize (safety 0)))
    (loop :while (< start end) :do
      (setf state (logxor (aref +crc-64-table+ (logxor (logand #xFF state) (aref data start)))
                          (ash state -8)))
      (incf start)))
  state)

(defun split-update-crc-64 (data start end state)
  (declare (type buffer data)
           (type array-length start end)
           (type (unsigned-byte 64) state)
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note)
           (optimize speed))
  (assert (<= 0 start end (length data)))
  (let ((state1 (ldb (byte 32 0) state))
        (state2 (ldb (byte 32 32) state)))
    (declare (type (unsigned-byte 32) state1 state2))
    (locally (declare (optimize (safety 0)))
      (loop :while (< start end) :do
        (psetf state1 (logxor (aref +split-crc-64-table+
                                    (logxor (logand #xFF state1) (aref data start))
                                    0)
                              (logior (ash (ldb (byte 8 0) state2) 24)
                                      (ash state1 -8)))
               state2 (logxor (aref +split-crc-64-table+
                                    (logxor (logand #xFF state1) (aref data start))
                                    1)
                              (ash state2 -8)))
        (incf start)))
    (logior (ash state2 32) state1)))

(defun update-crc-64 (data start end state)
  #+(or sbcl abcl)
  (basic-update-crc-64 data start end state)
  #-(or sbcl abcl)
  (split-update-crc-64 data start end state))
