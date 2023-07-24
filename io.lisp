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

(defun stream->buffer-stream (stream &key limit (buffer-size *default-buffer-size*))
  (when (and limit (< limit buffer-size))
    (setf buffer-size limit))
  (let ((buffer (make-array buffer-size :element-type 'octet)))
    (make-buffer-stream :buffer buffer :start 0 :end 0
                        :refill-function
                        (lambda ()
                          (let ((end (read-sequence buffer stream
                                                    :end (if limit
                                                             (min limit (length buffer))
                                                             (length buffer)))))
                            (when limit
                              (decf limit end))
                            (if (zerop end)
                                nil
                                (values buffer 0 end)))))))

;;; Converts a `next-decompressed-chunk'-like function to a buffer stream. A
;;; conversion in the other direction is also possible, which really suggests
;;; that these concepts should be merged...
(defun chunk-generator->buffer-stream (func)
  (let ((eofp nil))
    (make-buffer-stream :refill-function
                        (lambda ()
                          (if eofp
                              nil
                              (multiple-value-bind (buffer start end finalp)
                                  (funcall func)
                                (when finalp
                                  (setf eofp t))
                                (values buffer start end)))))))

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




;;; Counted byte sources
;;;
;;; Counted byte sources wrap a normal byte source and count how many bytes of
;;; input have been consumed. Additionally, they can enforce a hard limit on how
;;; much data is read before EOF is signalled (with an optional callback to
;;; handle attempted reads beyond the limit). This is necessary because certain
;;; formats like LZMA2 or XZ have requirements on block length or alignment.
;;;
;;; Similar to how byte sources are split between buffer streams and normal
;;; streams, we split counted byte sources into counted streams and counted
;;; buffer streams. Unfortunately, this means we wrap streams in our own Gray
;;; streams, killing off implementation-side optimizations for file streams and
;;; the like. This comes with serious (1.5x) performance penalties.
;;;
;;; However, often a limit on read bytes is actually a precise expectation of
;;; how many bytes are to be read; in this case, we can forcibly buffer the
;;; stream and get access to fast buffer stream I/O again. We do need to make
;;; sure that all data is really read though since the buffering could leave the
;;; stream in an indeterminate state otherwise.
;;;
;;; The interface to this is `make-counted-byte-source', `cbs-count',
;;; `cbs-limit' and `cbs-finish'. The byte source API works on this just fine.
;;; `cbs-finish' has to be called at the end once you're done and returns the
;;; original byte source.

;;; The stream version simply keeps the count accurate at all times.
(defclass counted-stream (fundamental-binary-input-stream)
  ((%source :accessor counted-stream-source :initarg :source)
   (%count :accessor counted-stream-count :initform 0)
   (%limit :accessor counted-stream-limit :initarg :limit :initform nil)
   (%on-eof :accessor counted-stream-on-eof :initarg :on-eof :initform (constantly nil))))

(defmethod cbs-count ((s counted-stream))
  (counted-stream-count s))
(defmethod (setf cbs-count) (new-value (s counted-stream))
  (setf (counted-stream-count s) new-value))
(defmethod cbs-limit ((s counted-stream))
  (counted-stream-limit s))
(defmethod cbs-finish ((s counted-stream))
  (counted-stream-source s))

(defmethod stream-element-type ((s counted-stream))
  'octet)

(defmethod stream-read-byte ((s counted-stream))
  (if (and (counted-stream-limit s)
           (<= (counted-stream-limit s) (counted-stream-count s)))
      (progn
        (funcall (counted-stream-on-eof s))
        :eof)
      (progn
        (incf (counted-stream-count s))
        (read-byte (counted-stream-source s) nil :eof))))

(defmethod stream-read-sequence ((s counted-stream) sequence start end &key &allow-other-keys)
  (setf start (or start 0))
  (setf end (or end (length sequence)))
  (let ((amount (if (counted-stream-limit s)
                    (min (- end start)
                         (- (counted-stream-limit s)
                            (counted-stream-count s)))
                    (- end start))))
    (when (< amount (- end start))
      (funcall (counted-stream-on-eof s)))
    (let ((real-end (read-sequence sequence (counted-stream-source s)
                                   :start start :end (+ start amount))))
      (incf (counted-stream-count s) (- real-end start))
      real-end)))

;;; The buffer stream version only updates the count during refills and
;;; `cbs-finish' since we want to reuse `bs-read-byte' and can keep the counting
;;; out of the hot path this way. At all times, the counted buffer stream and
;;; the original buffer stream are looking at the same buffer; `cbs-count' uses
;;; the read position to calculate the real count.
(defstruct (counted-buffer-stream (:include buffer-stream))
  (source (required-argument :source) :type buffer-stream)
  (count 0 :type unsigned-byte)
  (limit nil :type (or null unsigned-byte))
  (on-eof (constantly nil) :type function)
  ;; If `source' is a forcibly buffered version of a stream, then the underlying
  ;; stream is stored here. Relevant for `cbs-finish'.
  (unbuffered-source nil :type (or null byte-source)))

(defmethod cbs-limit ((cbs counted-buffer-stream))
  (counted-buffer-stream-limit cbs))

(defmethod cbs-count ((cbs counted-buffer-stream))
  (- (counted-buffer-stream-count cbs)
     (- (counted-buffer-stream-end cbs)
        (counted-buffer-stream-start cbs))))

(defmethod (setf cbs-count) (new-value (cbs counted-buffer-stream))
  (setf (counted-buffer-stream-count cbs)
        (+ new-value
           (- (counted-buffer-stream-end cbs)
              (counted-buffer-stream-start cbs)))))

(defmethod cbs-finish ((cbs counted-buffer-stream))
  (if (counted-buffer-stream-unbuffered-source cbs)
      ;; Forcibly buffered streams don't need setup since the buffer stream is a
      ;; throwaway object. We check that all data was consumed because otherwise
      ;; the stream is left in an indeterminate state; you can check this
      ;; manually before `cbs-finish' via `cbs-count' and `cbs-limit'.
      (progn
        (assert (= (cbs-count cbs) (cbs-limit cbs)))
        (counted-buffer-stream-unbuffered-source cbs))
      ;; Buffer streams need an update to `start' since we normally only update
      ;; that on refills.
      (let ((src (counted-buffer-stream-source cbs)))
        (assert (eq (buffer-stream-buffer src)
                    (counted-buffer-stream-buffer cbs)))
        (setf (buffer-stream-start src) (counted-buffer-stream-start cbs))
        src)))

;;; `limit', if non-nil, is the maximal number of readable bytes before EOF.
;;; `will-read-everything' asserts that you are going to read EXACTLY `limit'
;;; bytes, and results in buffering. `on-eof' is a callback that's called when
;;; someone attempts to read past the limit.
(defun make-counted-byte-source (source &key limit will-read-everything (on-eof (constantly nil))
                                 &aux unbuffered-source)
  (when (and limit will-read-everything (streamp source))
    (shiftf unbuffered-source source (stream->buffer-stream source :limit limit)))
  (etypecase source
    (stream
     (make-instance 'counted-stream :source source :limit limit :on-eof on-eof))
    (buffer-stream
     (let* ((cbs-end (if limit
                         (min (buffer-stream-end source)
                              (+ (buffer-stream-start source) limit))
                         (buffer-stream-end source)))
            (cbs (make-counted-buffer-stream
                  :buffer (buffer-stream-buffer source)
                  :start (buffer-stream-start source)
                  :end cbs-end
                  :source source
                  :limit limit
                  :count (- cbs-end (buffer-stream-start source))
                  :on-eof on-eof
                  :unbuffered-source unbuffered-source)))
       (setf (buffer-stream-refill-function cbs)
             (lambda ()
               (let ((limit (counted-buffer-stream-limit cbs))
                     (count (counted-buffer-stream-count cbs))
                     (src (counted-buffer-stream-source cbs)))
                 (if (or (null limit)
                         (< count limit))
                     (progn
                       (assert (= (buffer-stream-end src)
                                  (counted-buffer-stream-end cbs)))
                       (assert (= count (cbs-count cbs)))
                       ;; Sync first so `try-refill' has the right information.
                       (setf (buffer-stream-start src) (counted-buffer-stream-start cbs))
                       (if (try-refill src)
                           (let ((amount (if limit
                                             (min (- (buffer-stream-end src)
                                                     (buffer-stream-start src))
                                                  (- limit count))
                                             (- (buffer-stream-end src)
                                                (buffer-stream-start src)))))
                             (incf (counted-buffer-stream-count cbs) amount)
                             (values (buffer-stream-buffer src)
                                     (buffer-stream-start src)
                                     (+ (buffer-stream-start src) amount)))
                           ;; `try-refill' can update the source to (empty)
                           ;; buffers even when it fails, so synchronize first.
                           ;; Refill functions always return nil after returning
                           ;; it once, so this can't loop.
                           (if (eq (buffer-stream-buffer cbs)
                                   (buffer-stream-buffer src))
                               nil
                               (progn
                                 (assert (= (buffer-stream-start src)
                                            (buffer-stream-end src)))
                                 (values (buffer-stream-buffer src)
                                         (buffer-stream-start src)
                                         (buffer-stream-end src))))))
                     (progn
                       (funcall (counted-buffer-stream-on-eof cbs))
                       nil)))))
       cbs))))
