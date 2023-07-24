;;;; Fast buffer I/O
;;;
;;; We accept input from either a byte stream or a buffer. `read-byte' is
;;; required to prevent stream overreads, but is really slow; we therefore wrap
;;; streams with an inlineable in-memory stream if possible and define functions
;;; that can deal with both our in-memory streams and normal byte streams. This
;;; also provides an easy way to accept non-buffer arrays while optimizing for
;;; buffers in the hot paths.
;;;
;;; The functions `bs-read-byte' and `bs-read-sequence' both signal `eof' on
;;; input exhaustion, rather than `end-of-file'.
(cl:in-package #:semz.decompress)

(declaim (inline buffer-stream-buffer buffer-stream-start buffer-stream-end
                 buffer-stream-refill-function buffer-stream-p))
(defstruct buffer-stream
  (buffer +dummy-buffer+ :type buffer)
  (start 0 :type array-length)
  (end   0 :type array-length)
  ;; Returns either a replacement buffer and the start/end range of the newly
  ;; available bytes in said buffer, or nil if we ran out of input. Once it
  ;; returns nil, it must return nil consistently.
  (refill-function (constantly nil)))

(deftype byte-source ()
  '(or stream buffer-stream))

(defun array->buffer-stream (array start end &key (buffer-size *default-buffer-size*))
  (assert (<= 0 start end (length array)))
  (if (typep array 'buffer)
      (make-buffer-stream :buffer array :start start :end end)
      (let ((buffer (make-array (min buffer-size (- end start)) :element-type 'octet)))
        (make-buffer-stream :refill-function
                            (lambda ()
                              (if (< start end)
                                  (let ((bytes-added (min (- end start) (length buffer))))
                                    (replace buffer array :start2 start :end2 (+ start bytes-added))
                                    (incf start bytes-added)
                                    (values buffer 0 bytes-added))
                                  nil))))))

(defun stream->buffer-stream (stream &key (buffer-size *default-buffer-size*))
  (let ((buffer (make-array buffer-size :element-type 'octet)))
    (make-buffer-stream :buffer buffer :start 0 :end 0
                        :refill-function
                        (lambda ()
                          (let ((end (read-sequence buffer stream)))
                            (if (zerop end)
                                nil
                                (values buffer 0 end)))))))

(defun try-refill (bs)
  (declare (type buffer-stream bs))
  (loop
    (when (< (buffer-stream-start bs) (buffer-stream-end bs))
      (return t))
    (multiple-value-bind (buffer start end)
        (funcall (buffer-stream-refill-function bs))
      (when (null buffer)
        (return nil))
      (assert (<= 0 start end (length buffer)))
      (setf (buffer-stream-buffer bs) buffer
            (buffer-stream-start  bs) start
            (buffer-stream-end    bs) end))))

;;; Beware that, like all EOF checks, this function can attempt a read.
(defun buffer-stream-check-eof (bs)
  (and (= (buffer-stream-start bs) (buffer-stream-end bs))
       (not (try-refill bs))))

(define-fast-function (bs-read-byte octet) ((source byte-source))
  (if (buffer-stream-p source)
      (locally (declare (type buffer-stream source)) ; help out dumber impls
        ;; ABCL's type/bound check overhead is outright obscene. It makes the
        ;; buffered version significantly slower than the `read-byte' variant!
        ;; Since the JVM has built-in bounds checking and we ensure that buffer
        ;; stream bounds are valid at all times, safety 0 is acceptable here.
        #+abcl (declare (optimize (safety 0)))
        (when (= (buffer-stream-start source) (buffer-stream-end source))
          (unless (try-refill source)
            (%eof)))
        (prog1 (aref (buffer-stream-buffer source) (buffer-stream-start source))
          (incf (buffer-stream-start source))))
      (let ((byte (read-byte source nil nil)))
        (when (null byte)
          (%eof))
        byte)))

(defun bs-read-sequence (sequence source &key start end eof-error-p)
  ;; No `normalize-bounds' here because `sequence' need not be an array.
  ;; `length' is expensive for lists, so we avoid it for streams.
  (setf start (or start 0))
  (etypecase source
    (stream (read-sequence sequence source :start start :end end))
    (buffer-stream
     (setf end (or end (length sequence)))
     (loop
       (let ((amount (min (- (buffer-stream-end source) (buffer-stream-start source))
                          (- end start))))
         (replace sequence (buffer-stream-buffer source)
                  :start1 start
                  :end1 (+ start amount)
                  :start2 (buffer-stream-start source)
                  :end2 (+ (buffer-stream-start source) amount))
         (incf start amount)
         (incf (buffer-stream-start source) amount))
       (if (= start end)
           (return end)
           (unless (try-refill source)
             (if eof-error-p
                 (%eof)
                 (return start))))))))

(defun bs-read-le (n source)
  (let ((result 0))
    (dotimes (i n result)
      (setf (ldb (byte 8 (* 8 i)) result) (bs-read-byte source)))))

(defun bs-read-be (n source)
  (let ((result 0))
    (dotimes (i n result)
      (setf result (logior (ash result 8) (bs-read-byte source))))))
