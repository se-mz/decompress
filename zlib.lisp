(cl:in-package #:semz.decompress)

(defclass zlib-state ()
  ((%deflate-state :accessor zs-deflate-state :initarg :deflate-state)
   (%checksum-state :accessor zs-checksum-state :initform 1)))

(define-condition unrecognized-zlib-dictionary (decompression-error)
  ((dictionary-id :reader unrecognized-zlib-dictionary-checksum :initarg :checksum))
  (:report (lambda (c s)
             (format s "Unrecognized zlib dictionary: ~8,'0X"
                     (unrecognized-zlib-dictionary-checksum c))))
  (:documentation "Signalled when zlib decompression involves a preset dictionary whose checksum
isn't recognized by the dictionary function.

Note: This condition is only signalled when preset dictionaries are enabled."))

(setf (documentation 'unrecognized-zlib-dictionary-checksum 'function)
      "Returns the unrecognized checksum that was encountered during zlib
decompression, in the form `adler-32' outputs.")

(defmethod byte-source->decompression-state ((type (eql :zlib)) byte-source &key dictionary)
  (check-type dictionary (or null function))
  (let* ((cmf (bs-read-byte byte-source))
         (flg (bs-read-byte byte-source))
         (compression-method (ldb (byte 4 0) cmf))
         (compression-info (ldb (byte 4 4) cmf))
         ;; The lowest 5 bits of `flg' exist for the flag checksum below.
         (preset-dictionary-p (logbitp 5 flg))
         (compression-level (ldb (byte 2 6) flg)))
    (unless (= compression-method 8)
      (die "Unsupported compression method: ~X" compression-method))
    (unless (<= 0 compression-info 7)
      (die "Invalid compression info (must be 0 - 7): ~X" compression-info))
    (unless (zerop (mod (+ (* cmf #x100) flg) 31))
      (die "Invalid flag checksum."))
    (let ((window-size (expt 2 (+ compression-info 8)))
          (checksum (if preset-dictionary-p
                        (bs-read-be 4 byte-source)
                        nil))
          dict-buffer dict-start dict-end)

      (when checksum
        (when (null dictionary)
          (die "Cannot use preset dictionaries without a dictionary function."))
        (setf (values dict-buffer dict-start dict-end)
              (funcall dictionary checksum))
        (when (null dict-buffer)
          (error 'unrecognized-zlib-dictionary :checksum checksum))
        (normalize-bounds dict-buffer dict-start dict-end))

      (values (make-instance 'zlib-state :deflate-state (byte-source->decompression-state
                                                         :deflate byte-source
                                                         :window-size window-size
                                                         :prefix dict-buffer
                                                         :prefix-start dict-start
                                                         :prefix-end dict-end))
              (list :window-size window-size :level compression-level :dictionary checksum)))))

(defmethod next-decompressed-chunk ((zs zlib-state))
  (multiple-value-bind (buffer start end finalp)
      ;; 32 extra bits due to the trailing checksum.
      (next-deflate-chunk (zs-deflate-state zs) 32)
    (setf (zs-checksum-state zs)
          (update-adler-32 buffer start end (zs-checksum-state zs)))

    (when finalp
      (let ((br (ds-bit-reader (zs-deflate-state zs))))
        (lbr-flush-byte br)
        ;; Big-endian number, little-endian bits. Sigh.
        (let ((checksum (logior (ash (lbr-read-bits br 8) 24)
                                (ash (lbr-read-bits br 8) 16)
                                (ash (lbr-read-bits br 8)  8)
                                (ash (lbr-read-bits br 8)  0))))
          (unless (= checksum (zs-checksum-state zs))
            (die "Invalid data checksum (wanted ~4,'0x, got ~4,'0x)."
                 checksum (zs-checksum-state zs))))))

    (values buffer start end finalp)))

(defun make-simple-zlib-dictionary (buffers)
  "Returns a function suitable to be passed as a `dictionary' argument for zlib
decompression which recognizes every octet vector in the sequence `buffers' and
no others. The vectors should not be modified afterwards. An error is signalled
if multiple vectors with distinct contents have the same checksum."
  (let ((h (make-hash-table)))
    (map nil (lambda (b)
               (check-type b (array * (*)))
               (let ((checksum (adler-32 b)))
                 (multiple-value-bind (old-entry foundp)
                     (gethash checksum h)
                   (when (and foundp (not (equalp b old-entry)))
                     (error "Unequal buffers have the same Adler-32 checksum: ~8,'0x" checksum))
                   (setf (gethash checksum h) b))))
         buffers)
    (lambda (checksum)
      (multiple-value-bind (b foundp)
          (gethash checksum h)
        (if foundp
            (values b nil nil)
            nil)))))

(pushnew :zlib *known-formats*)
