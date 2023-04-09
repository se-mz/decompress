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

(declaim (inline bs-buffer bs-start bs-end bs-refill-function buffer-stream-p))
(defstruct (buffer-stream (:conc-name bs-))
  (buffer +dummy-buffer+ :type buffer)
  (start 0 :type array-length)
  (end   0 :type array-length)
  ;; Returns either a replacement buffer and the start/end range of the newly
  ;; available bytes in said buffer, or nil if we ran out of input.
  (refill-function (lambda () nil)))

(deftype byte-source ()
  '(or stream buffer-stream))

(defun array->buffer-stream (array start end &key (buffer-size *default-buffer-size*))
  (if (typep array 'buffer)
      (make-buffer-stream :buffer array :start start :end end)
      (let ((buffer (make-array (min buffer-size (- end start)) :element-type 'octet)))
        (replace buffer array :start2 start :end2 (+ start (length buffer)))
        (incf start (length buffer))
        (make-buffer-stream :buffer buffer :start 0 :end (length buffer)
                            :refill-function
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
                                (values nil    0 0)
                                (values buffer 0 end)))))))

(defun try-refill (bs)
  (declare (type buffer-stream bs))
  (loop
    :until (< (bs-start bs) (bs-end bs)) :do
      (multiple-value-bind (buffer start end)
          (funcall (bs-refill-function bs))
        (if (null buffer)
            (return nil)
            (setf (bs-buffer bs) buffer
                  (bs-start  bs) start
                  (bs-end    bs) end)))
    :finally (return t)))

(define-fast-function (bs-read-byte octet) ((source byte-source))
  (if (buffer-stream-p source)
      (locally (declare (type buffer-stream source)) ; help out dumber impls
        (when (= (bs-start source) (bs-end source))
          (unless (try-refill source)
            (%eof)))
        (prog1 (aref (bs-buffer source) (bs-start source))
          (incf (bs-start source))))
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
       (let ((amount (min (- (bs-end source) (bs-start source))
                          (- end start))))
         (replace sequence (bs-buffer source)
                  :start1 start             :end1 (+ start amount)
                  :start2 (bs-start source) :end2 (+ (bs-start source) amount))
         (incf start amount)
         (incf (bs-start source) amount))
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
