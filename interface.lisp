(cl:in-package #:semz.decompress)

(defun list-supported-formats ()
  "Returns a list of symbols that can be used as `format' arguments to
`make-decompression-stream' and `decompress' to specify a compression format."
  (copy-list *known-formats*))

(defclass decompression-stream (fundamental-binary-input-stream)
  ((%state :accessor decompression-stream-state :initarg :state)
   (%format :accessor decompression-stream-%format :initarg :format)
   (%header :accessor decompression-stream-%header :initarg :header)
   ;; Do we decompress all members (=> all data) or just the first one?
   (%all-members-p :accessor decompression-stream-all-members-p :initarg :all-members-p)
   ;; eof, has-member, needs-member
   (%control-state :accessor decompression-stream-control-state)
   ;; Rather than reimplement yet another in-memory stream, we reuse the one
   ;; from `io.lisp'.
   (%buffer-stream :accessor decompression-stream-buffer-stream :initarg :buffer-stream))
  (:documentation "Gray stream wrapper that can be used for complicated stream processing. The end
of file is considered reached when the underlying compressed data ends and all
associated uncompressed data has been read. Users need not close these streams."))

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
    (format input &rest args &key (start 0) end allow-overreads-p all-members-p &allow-other-keys)
  "Returns a `decompression-stream' whence the decompressed form of the
`format'-compressed data in `input' can be read. If the format allows multiple
members, only the first member is decompressed. Trailing data is ignored and
will not be read from stream inputs, so that it can be handled by other code.

`input' should not be modified or read from until the returned stream has
reached end of file. If `input' is a stream, then the caller is responsible for
closing it.

Calling this function will read header information from `input' and make it
available via `decompression-stream-header', but no decompression will be
performed until data is read from `decompression-stream'.

If `all-members-p' is true, the stream will decompress and concatenate all
compressed members from the stream (if the format defines multiple members) and
signal a `decompression-error' if any trailing data is detected, similar to
`decompress-all'. The provided header information is always that of the first
member. If the value of `all-members-p' is known to be constant and true, it is
recommended to use `make-full-decompression-stream' over
`make-decompression-stream' since forgetting to set `all-members-p' can result
in subtle bugs down the line.

If `allow-overreads-p' is true and `input' is a stream, trailing data may be
read, resulting in a minor speedup. This option rarely has to be specified since
it is implied by `all-members-p'.

This function can take format-specific options."
  (check-type input (or stream (array * (*))))
  (when (arrayp input)
    (normalize-bounds input start end)
    (setf input (array->buffer-stream input start end)))
  ;; If we exhaust the entire input anyway, we might as well fully buffer it.
  ;; This gives us an easy way to do EOF detection, too.
  (when all-members-p
    (setf allow-overreads-p t))
  (when (and allow-overreads-p (streamp input))
    (setf input (stream->buffer-stream input)))
  (remove-from-plistf args :start :end :allow-overreads-p :all-members-p)
  (let ((ds (make-instance 'decompression-stream
                           :format format
                           :state nil
                           :header nil
                           :all-members-p all-members-p)))
    (labels ((refill ()
               (ecase (decompression-stream-control-state ds)
                 (:eof nil)

                 (:has-member
                  (multiple-value-bind (buffer start end finalp)
                      (next-decompressed-chunk (decompression-stream-state ds))
                    (when finalp
                      (setf (decompression-stream-control-state ds)
                            (if (decompression-stream-all-members-p ds)
                                :needs-member
                                :eof)))
                    (values buffer start end)))

                 ;; Theoretically we could set up a new member right after
                 ;; reading the previous member's data, but if there's an error
                 ;; due to trailing data/etc, then that last chunk wouldn't be
                 ;; output, which would be extremely confusing for the user.
                 (:needs-member
                  (assert (buffer-stream-p input))
                  (assert (decompression-stream-all-members-p ds))
                  (if (buffer-stream-check-eof input)
                      (progn
                        (setf (decompression-stream-control-state ds) :eof)
                        nil)
                      (multiple-value-bind (new-state new-header)
                          (make-reset-state (decompression-stream-state ds))
                        ;; Deliberately do NOT update the header. We could
                        ;; `signal' a condition for this if someone really needs
                        ;; the headers, but I don't see the point of specifying
                        ;; this before anyone needs it.
                        (declare (ignore new-header))
                        ;; nil => single-member format. We already checked that
                        ;; this isn't EOF.
                        (when (null new-state)
                          ;; We could make this a separate error condition, but
                          ;; it would only be useful for single-member formats
                          ;; since otherwise trailing data will fail to parse.
                          ;; Probably simpler to just make it a generic error.
                          (die "Trailing data detected."))
                        (setf (decompression-stream-state ds) new-state
                              (decompression-stream-control-state ds) :has-member)
                        (values +dummy-buffer+ 0 0)))))))

      (multiple-value-bind (state header)
          (apply #'byte-source->decompression-state format input args)
        (setf (decompression-stream-control-state ds) :has-member
              (decompression-stream-state ds) state
              (decompression-stream-%header ds) header

              (decompression-stream-buffer-stream ds)
              (make-buffer-stream :refill-function #'refill))
        ds))))

(defun make-full-decompression-stream (format input &rest args)
  "Wrapper around `make-decompression-stream' that always passes `all-members-p'."
  (apply #'make-decompression-stream format input :all-members-p t args))

(defun decompress
    (format input &rest args &key (start 0) end allow-overreads-p output-size &allow-other-keys)
  "Returns a fresh octet vector that contains the decompressed form of the
`format'-compressed data in `input'. If the format allows multiple members, only
the first member is decompressed. Trailing data is ignored and will not be read
from stream inputs, so that it can be handled by other code.

The second return value is a property list containing the header information of
the decompressed member.

`output-size', if not nil, should be the predicted size of the decompressed
data. If correct, this prevents unnecessary copying at the end.

If `all-members-p' is true, act like `decompress-all' instead. If the value of
`all-members-p' is known to be constant and true, it is recommended to use
`decompress-all' over `decompress' since forgetting to set `all-members-p' can
result in subtle bugs down the line.

If `allow-overreads-p' is true and `input' is a stream, trailing data may be
read, resulting in a minor speedup. This option rarely has to be specified since
it is implied by `all-members-p'.

This function can take format-specific options.

To handle large data in a streaming fashion, use `make-decompression-stream'. To
handle all members at once, use `decompress-all'."
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

(defun decompress-all (format input &rest args &key (start 0) end output-size &allow-other-keys)
  "Returns a fresh octet vector that contains the decompressed form of the
`format'-compressed data in `input'. If the format allows multiple members, all
members are decompressed and concatenated. Trailing data results in a
`decompression-error'.

The second return value is a property list containing the header information of
the first member.

`output-size', if not nil, should be the predicted size of the decompressed
data. If correct, this prevents unnecessary copying at the end.

This function can take format-specific options.

This function is equivalent to calling `decompress' with `all-members-p' set; it
exists to prevent the subtle errors that result from a forgotten
`all-members-p'. If you want to decompress single members or preserve trailing
data, use `decompress' instead. To handle large data in a streaming fashion, use
`make-full-decompression-stream'."
  (declare (ignore start end output-size))
  (apply #'decompress format input :all-members-p t args))
