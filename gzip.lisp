(cl:in-package #:semz.decompress)

(defclass gzip-state ()
  ((%deflate-state :accessor gs-deflate-state :initarg :deflate-state)
   (%crc32 :accessor gs-crc32 :initform (start-crc-32))
   (%size :accessor gs-size :initform 0)))

;;; The extra fields are made up of a series of blocks of the following form:
;;; ID (2 Latin-1 chars), length (2 bytes, LE), data (`length' bytes).
(defun gzip-extra-fields-consistent-p (bytes)
  (loop :with i = 0
        :while (< i (length bytes))
        :do ;; Is there enough space for the length field?
            (unless (<= (+ i 2 2) (length bytes))
              (return nil))
            ;; Does the field go out of bounds?
            (unless (<= (+ i 2 2 (ub16ref/le bytes (+ i 2)))
                        (length bytes))
              (return nil))
            (incf i (+ 2 2 (ub16ref/le bytes (+ i 2))))
        :finally (return t)))

(defun parse-gzip-extra-fields (bytes)
  (unless (gzip-extra-fields-consistent-p bytes)
    (die "Inconsistent lengths for gzip extra fields."))
  (loop :for i = 0 :then (+ i 2 2 (ub16ref/le bytes (+ i 2)))
        :while (< i (length bytes))
        :collect (cons (map 'string #'code-char (subseq bytes i (+ i 2)))
                       (subseq bytes (+ i 2 2) (+ i 2 2 (ub16ref/le bytes (+ i 2)))))))

(defmethod byte-source->decompression-state ((type (eql :gzip)) src &key)
  (let ((header-checksum (start-crc-32)))
    (labels ((update-header-crc (buffer)
               (setf header-checksum (update-crc-32 buffer 0 (length buffer) header-checksum)))
             (read-header-buffer (length)
               (let ((buffer (make-array length :element-type 'octet)))
                 (bs-read-sequence buffer src :eof-error-p t)
                 (update-header-crc buffer)
                 buffer))
             (read-cstring ()
               (let ((buffer (make-array 256 :element-type 'octet :adjustable t :fill-pointer 0)))
                 (loop :for b = (bs-read-byte src)
                       :until (zerop b)
                       :do (vector-push-extend b buffer))
                 (let ((result (subseq buffer 0)))
                   (update-header-crc result)
                   (update-header-crc #.(coerce #(0) 'buffer))
                   ;; The encoding of these fields is explicitly Latin-1.
                   (map 'string #'code-char result)))))
      (let* ((head (read-header-buffer 10))
             (flg (aref head 3))
             (mtime (ub32ref/le head 4))
             (extra-flags (aref head 8))
             (os-info (aref head 9))
             (text-file-p       (logbitp 0 flg))
             (header-checksum-p (logbitp 1 flg))
             (extra-fields-p    (logbitp 2 flg))
             (file-name-p       (logbitp 3 flg))
             (comment-p         (logbitp 4 flg)))
        (unless (and (= (aref head 0) #x1F)
                     (= (aref head 1) #x8B))
          (die "Incorrect gzip magic bytes."))
        (unless (= (aref head 2) 8)
          (die "Unrecognized compression method: ~x" (aref head 2)))
        (unless (zerop (ldb (byte 3 5) flg))
          (die "Reserved flag bits are non-zero."))
        (let ((extra-fields (if extra-fields-p
                                (parse-gzip-extra-fields
                                 (read-header-buffer (ub16ref/le (read-header-buffer 2) 0)))
                                '()))
              (file-name (if file-name-p (read-cstring) nil))
              (comment   (if comment-p   (read-cstring) nil)))
          (when header-checksum-p
            (let ((checksum (bs-read-le 2 src))
                  (real-checksum (logand #xFFFF (finish-crc-32 header-checksum))))
              (unless (= checksum real-checksum)
                (die "Header checksum mismatch (required ~4,'0x, got ~4,'0x)."
                     checksum real-checksum))))
          (values (make-instance 'gzip-state :deflate-state (byte-source->decompression-state
                                                             :deflate src))
                  (list :textp text-file-p
                        :extra-fields extra-fields
                        :filename file-name
                        :comment comment
                        :modification-time mtime
                        :extra-flags extra-flags
                        :operating-system os-info)))))))

(defmethod next-decompressed-chunk ((gs gzip-state))
  (multiple-value-bind (buffer start end finalp)
      ;; 32-bit checksum and 32-bit reduced length at the end, so 64 bits.
      (next-deflate-chunk (gs-deflate-state gs) 64)
    (setf (gs-crc32 gs) (update-crc-32 buffer start end (gs-crc32 gs)))
    (incf (gs-size gs) (- end start))

    (when finalp
      (let ((br (ds-bit-reader (gs-deflate-state gs))))
        (lbr-flush-byte br)
        (let ((checksum (lbr-read-bits br 32))
              (real-checksum (finish-crc-32 (gs-crc32 gs))))
          (unless (= checksum real-checksum)
            (die "Invalid data checksum (wanted ~8,'0x, got ~8,'0x)." checksum real-checksum)))
        (let ((size-mod-2^32 (lbr-read-bits br 32))
              (real-size-mod-2^32 (mod (gs-size gs) (expt 2 32))))
          (unless (= size-mod-2^32 real-size-mod-2^32)
            (die "Invalid data length check (wanted ~d, got ~d)."
                 size-mod-2^32 real-size-mod-2^32)))))

    (values buffer start end finalp)))

(pushnew :gzip *known-formats*)
