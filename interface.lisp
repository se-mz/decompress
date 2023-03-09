(cl:in-package #:semz.decompress)

(defun list-supported-formats ()
  "Returns a list of symbols that can be used as `format' arguments to
`make-decompression-stream' and `decompress' to specify a compression format."
  (copy-list *known-formats*))

(defclass decompression-stream (fundamental-binary-input-stream)
  ((%state :accessor decompression-stream-state :initarg :state)
   (%format :accessor decompression-stream-%format :initarg :format)
   (%header :accessor decompression-stream-%header :initarg :header)
   (%eof :accessor decompression-stream-eof :initform nil)
   ;; Rather than reimplement yet another in-memory stream, we reuse the one
   ;; from `io.lisp'.
   (%buffer-stream :accessor decompression-stream-buffer-stream :initarg :buffer-stream))
  (:documentation "Gray stream wrapper that can be used for complicated stream processing. The end
of file is considered reached when the underlying compressed data ends and all
associated uncompressed data has been read."))

;;; Non-generic read-only wrappers.
(defun decompression-stream-format (stream)
  "Returns the `format' argument used to create `stream'."
  (decompression-stream-%format stream))
(defun decompression-stream-header (stream)
  "Returns the header metadata of the data associated to `stream'."
  ;; This lets the user modify the header metadata, but we don't use it for
  ;; anything anyway, so no harm is done.
  (decompression-stream-%header stream))

(defmethod stream-element-type ((stream decompression-stream))
  'octet)

;;; This is a bit questionable performance-wise, but I doubt anyone who cares
;;; about performance would use a `stream-read-byte' loop.
(defmethod stream-read-byte ((stream decompression-stream))
  (handler-case (bs-read-byte (decompression-stream-buffer-stream stream))
    (eof () :eof)))

(defmethod stream-read-sequence ((stream decompression-stream) sequence start end
                                 &key &allow-other-keys)
  (bs-read-sequence sequence (decompression-stream-buffer-stream stream) :start start :end end))

(defun make-decompression-stream
    (format input &rest args &key (start 0) end allow-overreads-p &allow-other-keys)
  "Returns a `decompression-stream' whence the decompressed form of the
`format'-compressed data in `input' can be read. `input' should not be modified
or read from until `decompression-stream' has reached end of file. If `input' is
a stream, then the caller is responsible for closing it.

Calling this function will read header information from `input', but no
decompression will be performed until data is read from `decompression-stream'.

If `allow-overreads-p' is true and `input' is a stream, bytes beyond the end of
the compressed data might end up being read during stream creation and
decompression; enabling this option tends to significantly improve performance
on stream inputs.

This function can take further format-specific options."
  (check-type input (or stream (array * (*))))
  (when (arrayp input)
    (normalize-bounds input start end)
    (setf input (array->buffer-stream input start end)))
  (when (and allow-overreads-p (streamp input))
    (setf input (stream->buffer-stream input)))
  (remove-from-plistf args :start :end :allow-overreads-p)
  (multiple-value-bind (state header)
      (apply #'byte-source->decompression-state format input args)
    (let ((ds (make-instance 'decompression-stream :format format :state state :header header)))
      (setf (decompression-stream-buffer-stream ds)
            (make-buffer-stream
             :refill-function (lambda ()
                                (if (decompression-stream-eof ds)
                                    nil
                                    (multiple-value-bind (buffer start end finalp)
                                        (next-decompressed-chunk (decompression-stream-state ds))
                                      (setf (decompression-stream-eof ds) finalp)
                                      (values buffer start end))))))
      ds)))

(defun decompress
    (format input &rest args &key (start 0) end allow-overreads-p output-size &allow-other-keys)
  "Returns a fresh octet vector that contains the decompressed form of the
`format'-compressed data in `input'.

`output-size', if not `nil', should be the predicted size of the decompressed
data. If correct, this prevents unnecessary copying at the end.

If `allow-overreads-p' is true and `input' is a stream, bytes beyond the end of
the compressed data might end up being read during decompression; enabling this
option tends to significantly improve performance on stream inputs.

This function can take further format-specific options."
  (check-type output-size (or null array-length))
  (remove-from-plistf args :start :end :allow-overreads-p :output-size)
  (let ((dstream (apply #'make-decompression-stream
                        format input
                        :start start :end end
                        :allow-overreads-p allow-overreads-p
                        args)))
    (values (read-stream-content-into-byte-vector
             dstream :initial-size (if (and output-size (> output-size 0))
                                       output-size
                                       *default-buffer-size*))
            (decompression-stream-header dstream))))
