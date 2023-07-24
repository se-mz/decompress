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
(cl:in-package #:semz.decompress)

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
