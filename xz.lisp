;;;; XZ
;;;
;;; XZ has a spec, which can be found here:
;;; https://github.com/tukaani-project/xz/tree/master/doc/xz-file-format.txt
(cl:in-package #:semz.decompress)

;;; XZ has extensible checksums; if you REALLY need to add your own, rebind this
;;; variable. I don't want to make it part of the public API but I also have no
;;; reason to change how this works. States may be mutable but must be returned.
;;; The final result must be a LE integer. CRC-32 and SHA-256 are instructive.
;;; Keep in mind that XZ specifies the checksum sizes even for unassigned types.
(defparameter *xz-checksums*
  (vector
   ;; We use 0 as the null checksum since that lines up with a 0 byte read.
   (vector (constantly 0) (constantly 0) (constantly 0))
   ;; 4-byte checksums
   (vector 'start-crc-32 'update-crc-32 'finish-crc-32)
   nil nil
   ;; 8-byte checksums
   (vector 'start-crc-64 'update-crc-64 'finish-crc-64)
   nil nil
   ;; 16-byte checksums
   nil nil nil
   ;; 32-byte checksums
   (vector 'start-sha-256 'update-sha-256 'finish-sha-256)
   nil nil
   ;; 64-byte checksums
   nil nil nil))

(defparameter *xz-checksum-sizes*
  #(0 4 4 4 8 8 8 16 16 16 32 32 32 64 64 64))

(defun start-xz-checksum (info)
  (funcall (aref info 0)))

(defun update-xz-checksum (info buffer start end state)
  (funcall (aref info 1) buffer start end state))

(defun finish-xz-checksum (info state)
  (funcall (aref info 2) state))

(defclass xz-state ()
  ((%source :initarg :source :accessor xzs-source)
   ;; block/index, data, block-end, eof.
   (%control-state :accessor xzs-control-state)
   ;; `next-decompressed-chunk'-like function that generates decompressed data.
   ;; Used to chain filters.
   (%chunk-generator :accessor xzs-chunk-generator)

   (%lzma2-state :initform nil :accessor xzs-lzma2-state)
   ;; LZMA dictionaries can be really large, so reuse them if possible.
   (%dictionary :initform nil :accessor xzs-dictionary)

   ;; Object that describes how to calculate the checksum. See `*xz-checksums*'.
   (%checksum-info :initarg :checksum-info :accessor xzs-checksum-info)
   ;; Checksum size in bytes.
   (%checksum-size :initarg :checksum-size :accessor xzs-checksum-size)
   ;; Current intermediate checksum state.
   (%checksum :accessor xzs-checksum)

   ;; The first two header bytes as a LE integer. Must be stored because we
   ;; check them against the redundant copy in the footer.
   (%stream-flags :initarg :stream-flags :accessor xzs-stream-flags)
   ;; Decompressed/compressed sizes for encountered blocks, in reverse(!) order
   ;; since we push the values. Must be verified at the end via the "index".
   (%decompressed-sizes :initform '() :accessor xzs-decompressed-sizes)
   (%compressed-sizes :initform '() :accessor xzs-compressed-sizes)

   ;; Optional size expectations for the current block. Must be verified at the
   ;; end of the block.
   (%block-expected-compressed-size :accessor xzs-block-expected-compressed-size)
   (%block-expected-decompressed-size :accessor xzs-block-expected-decompressed-size)

   ;; Used to verify that the total decompressed size doesn't hit 2^63.
   (%total-decompressed-size :initform 0 :accessor xzs-total-decompressed-size)))

;;; The magic bytes are skippable to deal with multi-member files; see below.
(defmethod byte-source->decompression-state
    ((format (eql :xz)) source &key ((skip-magic skip-magic)))
  ;; Ensure that the compressed data isn't 2^63 bytes or more. When we hit EOF,
  ;; we recover the original source in `finish-xz-member' to be able to use it
  ;; for future `make-reset-state' calls.
  (setf source (make-counted-byte-source
                source
                :limit (- (expt 2 63) 1)
                :on-eof (lambda ()
                          (die "XZ stream is longer than 2^63 - 1 bytes."))))
  (if skip-magic
      (incf (cbs-count source) 6)
      (unless (= (bs-read-le 6 source) #x005A587A37FD)
        (die "Invalid XZ magic bytes.")))
  (unless (zerop (bs-read-byte source))
    (die "Reserved header byte isn't zero."))

  (let* ((header2 (bs-read-byte source))
         (raw-checksum-type (ldb (byte 4 0) header2))
         (checksum-info (aref *xz-checksums* raw-checksum-type))
         (header-crc (bs-read-le 4 source)))
    (unless (= header-crc (crc-32 (coerce (vector 0 header2) 'buffer) 0 2))
      (die "Incorrect header checksum."))
    (unless (zerop (ldb (byte 4 4) header2))
      (die "Reserved header flag bits aren't zero."))
    (when (null checksum-info)
      (die "Unsupported checksum type: ~X" raw-checksum-type))
    (let ((raw-state (make-instance 'xz-state :source source)))
      (setf (xzs-checksum-size raw-state)
            (elt *xz-checksum-sizes* raw-checksum-type)
            (xzs-checksum-info raw-state) checksum-info
            (xzs-stream-flags raw-state) (logior 0 (ash header2 8))
            (xzs-control-state raw-state) :block/index)
      (values raw-state
              (list :checksum-type raw-checksum-type)))))

;;; After each member, there may be 4*n zero bytes of padding, even if they're
;;; not followed by another member. To safely distinguish trailing padding from
;;; members, we consume 4 bytes at a time; if we see the start of the magic, we
;;; consume it entirely and then skip the magic bytes during state creation.
(defmethod make-reset-state ((state xz-state))
  (let ((buffer (make-array 4 :initial-element 0 :element-type 'octet))
        (source (xzs-source state)))
    (loop
      (let ((end (bs-read-sequence buffer source)))
        (case end
          ;; We didn't signal EOF yet, so a `nil' would mean "format does not
          ;; support multi-member files". The dummy state will signal EOF for us
          ;; and complain about trailing data if the user tries to read further.
          (0 (return (make-instance 'eof-dummy-state)))
          (4 (when (not (every #'zerop buffer))
               (if (and (equalp buffer #(#xFD #x37 #x7A #x58))
                        (= (bs-read-byte source) #x5A)
                        (= (bs-read-byte source) #x00))
                   (return (byte-source->decompression-state :xz (xzs-source state) 'skip-magic t))
                   (die "Trailing garbage data after XZ stream."))))
          (otherwise (die "XZ padding doesn't come in multiples of 4 bytes.")))))))

;;; XZ encodes certain large integers in little-endian, seven bits at a time,
;;; with the eigth most significant bit set if and only if further bytes follow.
;;; Overlong sequences are illegal; this is not explicitly mentioned in the spec
;;; but handled in the example code and explicitly tested by XZ's test suite. As
;;; a consequence, this representation is unique.
(defun decode-xz-multibyte-int (source)
  (let ((x0 (bs-read-byte source)))
    (if (< x0 #x80)
        x0
        (loop
          :with value = (ldb (byte 7 0) x0)
          :for i :from 7 :below 63 :by 7
          :for byte = (bs-read-byte source)
          :do (setf (ldb (byte 7 i) value) byte)
              (when (zerop byte)
                (die "Overlong multibyte integer encoding."))
              (when (not (logbitp 7 byte))
                (return value))
          :finally (die "Overlong multibyte integer.")))))

(defun push-xz-multibyte-int (int vector)
  (loop
    (vector-push-extend (ldb (byte 7 0) int) vector)
    (setf int (ash int -7))
    (if (zerop int)
        (return)
        (setf (ldb (byte 1 7) (aref vector (- (fill-pointer vector) 1))) 1))))

;;; Verifies the index and footer, which duplicate information from the stream
;;; header and block headers in order to support partial decompression.
(defun finish-xz-member (state)
  (with-accessors ((source xzs-source)) state
    ;; The index contains the number of blocks; for each block, its compressed
    ;; size (without padding!) and decompressed size; and a CRC-32 of the
    ;; preceding data. We reconstruct the index to be able to CRC it in one go,
    ;; abusing that XZ's multibyte integers have a unique representation.
    (let ((reconstructed-index (make-array 100 :element-type 'octet :adjustable t :fill-pointer 0)))
      ;; The index always starts with a zero byte, included in the CRC, which
      ;; distinguishes it from a block.
      (vector-push-extend 0 reconstructed-index)
      (flet ((read-int ()
               (let ((x (decode-xz-multibyte-int source)))
                 (push-xz-multibyte-int x reconstructed-index)
                 x)))
        ;; As noted in the spec, one might use SHA-256 to verify the block sizes
        ;; in constant memory. I'm not sure if this is worth it; due to gzip
        ;; filenames, the best we can do is worst case linear memory usage
        ;; anyway. Maybe I could add a constant memory mode that disables
        ;; certain format features, but this is something to think about once
        ;; it's actually needed.
        (let ((comp-decomp-pairs
                (loop :repeat (read-int) :collect (list (read-int) (read-int)))))
          (loop :repeat (mod (- (length reconstructed-index)) 4) :do
            (unless (zerop (bs-read-byte source))
              (die "Index padding contains non-zero bytes."))
            (vector-push-extend 0 reconstructed-index))

          (unless (= (length comp-decomp-pairs)
                     (length (xzs-compressed-sizes state))
                     (length (xzs-decompressed-sizes state)))
            (die "Index disagrees with the observed number of blocks."))

          (unless (every (lambda (r comp decomp)
                           (and (= (first r) comp) (= (second r) decomp)))
                         comp-decomp-pairs
                         (reverse (xzs-compressed-sizes state))
                         (reverse (xzs-decompressed-sizes state)))
            (die "Index disagrees with the observed block sizes."))

          (let ((index-crc (bs-read-le 4 source))
                (real-index-crc (crc-32 (subseq reconstructed-index 0)
                                        0 (length reconstructed-index))))
            (unless (= index-crc real-index-crc)
              (die "Incorrect index CRC (expected ~8,'0x, got ~8,'0x)."
                   index-crc real-index-crc)))

          ;; The footer consists of its CRC-32, the index length (4-byte LE,
          ;; interpreted as 4(n+1)), stream flags, and two magic bytes.
          (let ((footer (make-array 12 :element-type 'octet)))
            (bs-read-sequence footer source :eof-error-p t)
            (let ((footer-crc (ub32ref/le footer 0))
                  ;; The CRC deliberately does not include the magic bytes.
                  (real-footer-crc (crc-32 footer 4 (- (length footer) 2))))
              (unless (= footer-crc real-footer-crc)
                (die "Incorrect footer CRC (expected ~8,'0x, got ~8,'0x)."
                     footer-crc real-footer-crc)))
            (unless (= (* 4 (+ 1 (ub32ref/le footer 4)))
                       ;; The +4 accounts for the index CRC.
                       (+ 4 (length reconstructed-index)))
              (die "Incorrect backwards size field."))
            (unless (= (xzs-stream-flags state)
                       (ub16ref/le footer (- (length footer) 4)))
              (die "Inconsistent stream flags between header and footer."))
            (unless (= #x5A59 (ub16ref/le footer (- (length footer) 2)))
              (die "Invalid footer magic bytes."))
            ;; Recover the original unlimited source in case a call to
            ;; `make-reset-state' is coming up.
            (setf source (cbs-finish source))))))))

;;; This implementation is taken straight from the specification. Adding a delta
;;; filter to an XZ stream causes the same 1.33x decompression speed penalty for
;;; XZ Utils as it does for us, so the implementation should be fine.
(defun wrap-in-xz-delta-filter (chunk-generator distance)
  (let ((bs (chunk-generator->buffer-stream chunk-generator))
        (buffer (make-array *default-buffer-size* :element-type 'octet))
        (delta (make-array 256 :element-type 'octet :initial-element 0))
        (pos 0))
    (lambda ()
      (declare (type buffer buffer delta)
               (type octet pos)
               (type (integer 1 256) distance)
               (optimize . #.*optimize-decls*))
      (let ((end (bs-read-sequence buffer bs)))
        (declare (type array-length end))
        (if (zerop end)
            (values +dummy-buffer+ 0 0 t)
            (dotimes (i end (values buffer 0 end nil))
              (let ((tmp (logand #xFF (+ (aref delta (logand #xFF (+ distance pos)))
                                         (aref buffer i)))))
                (declare (type octet tmp))
                (setf (aref delta pos) tmp
                      (aref buffer i) tmp)
                (setf pos (logand #xFF (- pos 1))))))))))

(defun handle-xz-block (state block-header)
  (let* ((flags (aref block-header 1))
         (filter-count (+ 1 (ldb (byte 2 0) flags)))
         (reserved (ldb (byte 4 2) flags))
         (compressed-size-p (logbitp 6 flags))
         (decompressed-size-p (logbitp 7 flags)))
    (unless (zerop reserved)
      (die "Reserved block header bits aren't zero."))

    (let ((header-source (array->buffer-stream block-header 2 (length block-header)))
          (compressed-size nil)
          (decompressed-size nil)
          (filter-flags (make-array filter-count :initial-element nil)))
      (handler-case
          (progn
            (when compressed-size-p
              (setf compressed-size (decode-xz-multibyte-int header-source)))
            (when decompressed-size-p
              (setf decompressed-size (decode-xz-multibyte-int header-source)))
            (map-into filter-flags
                      (lambda ()
                        (let ((id (decode-xz-multibyte-int header-source))
                              (props (make-array
                                      (decode-xz-multibyte-int header-source)
                                      :element-type 'octet)))
                          (bs-read-sequence props header-source :eof-error-p t)
                          (list id props)))))
        (eof ()
          (die "Block header is truncated.")))

      (when (position-if-not #'zerop block-header :start (buffer-stream-start header-source))
        (die "Block header padding contains non-zero bytes."))

      ;; 4 extra bytes for the header CRC
      (push (+ 4 (length block-header)) (xzs-compressed-sizes state))
      (push 0 (xzs-decompressed-sizes state))

      (setf (xzs-block-expected-compressed-size state) compressed-size)
      (setf (xzs-block-expected-decompressed-size state) decompressed-size)

      ;; This has to be set even without a declared compressed size since we
      ;; need to count the input bytes for the multiple-of-4 padding. When the
      ;; block ends, we switch back to the original source.
      (setf (xzs-source state)
            (make-counted-byte-source
             (xzs-source state)
             :limit compressed-size
             :will-read-everything t
             :on-eof (lambda ()
                       (die "Embedded compressed data goes beyond declared XZ block size."))))

      (loop :for index :from (length filter-flags) :downto 1
            :for (id props) = (aref filter-flags (- index 1))
            :do (case id
                  (#x03
                   (when (= index (length filter-flags))
                     (die "The Delta filter must not come last."))
                   (unless (= 1 (length props))
                     (die "Invalid property length for Delta filter: ~d" (length props)))
                   (setf (xzs-chunk-generator state)
                         (wrap-in-xz-delta-filter (xzs-chunk-generator state)
                                                  (+ 1 (aref props 0)))))

                  ((#x04 #x05 #x06 #x07 #x08 #x09 #x0A)
                   (when (= index (length filter-flags))
                     (die "BCJ filters must not come last."))
                   (let ((offset (case (length props)
                                   (0 0)
                                   (4 (ub32ref/le props 0))
                                   (otherwise
                                    (die "Invalid property length for BCJ filter: ~d"
                                         (length props)))))
                         (alignment (aref #(1 4 16 4 2 4 4) (- id #x04)))
                         (filter (aref #(wrap-in-xz-x86-filter
                                         wrap-in-xz-powerpc-filter
                                         wrap-in-xz-ia64-filter
                                         wrap-in-xz-arm-filter
                                         wrap-in-xz-armthumb-filter
                                         wrap-in-xz-sparc-filter
                                         wrap-in-xz-arm64-filter)
                                       (- id #x04))))
                     (unless (integerp (/ offset alignment))
                       (die "Offset ~8,0x is not aligned to ~d" offset alignment))
                     (setf (xzs-chunk-generator state)
                           (funcall filter (xzs-chunk-generator state) offset))))

                  (#x21
                   (unless (= index (length filter-flags))
                     (die "The LZMA2 filter must always come last."))
                   (unless (= 1 (length props))
                     (die "Invalid property length for LZMA2 filter: ~d" (length props)))
                   (unless (zerop (ldb (byte 2 6) (aref props 0)))
                     (die "Reserved LZMA property bits aren't zero."))
                   (let ((dict-size (parse-lzma2-dict-size (ldb (byte 6 0) (aref props 0)))))
                     (setf (xzs-lzma2-state state)
                           (byte-source->decompression-state
                            ;; We could use `lzma2' here if we hadn't read the
                            ;; property byte in a generic way, but I might add
                            ;; delta filter support later.
                            :raw-lzma2 (xzs-source state)
                            ;; EOF is explicitly not allowed in XZ's LZMA2. The
                            ;; test suite checks for that.
                            :eof-mode :never
                            ;; We could reuse buffers more aggressively by
                            ;; tracking the original declared size and reusing
                            ;; buffers whenever the new dict-size is smaller,
                            ;; but generally files stick to a single size.
                            :buffer (if (and (xzs-lzma2-state state)
                                             (= (lz2s-dict-size (xzs-lzma2-state state))
                                                dict-size))
                                        (lz2s-buffer (xzs-lzma2-state state))
                                        nil)
                            :window-size dict-size))
                     ;; LZMA2 is always the last filter, so setf is fine.
                     (setf (xzs-chunk-generator state)
                           (lambda ()
                             (next-decompressed-chunk (xzs-lzma2-state state))))))
                  (otherwise (die "Unrecognized filter type: ~2,'0x" id))))
      (setf (xzs-checksum state) (start-xz-checksum (xzs-checksum-info state))
            (xzs-control-state state) :data))))

(defmethod next-decompressed-chunk ((state xz-state))
  (with-accessors ((lzma2-state xzs-lzma2-state)
                   (source xzs-source))
      state
    (ecase (xzs-control-state state)
      (:eof
       (error "Called `next-decompressed-chunk' on a finished XZ stream."))

      (:block/index
       (let ((first-byte (bs-read-byte source)))
         (if (zerop first-byte)
             (progn
               (finish-xz-member state)
               (setf (xzs-control-state state) :eof)
               (values +dummy-buffer+ 0 0 t))
             ;; The size does not include the trailing CRC.
             (let* ((block-header-size (* 4 first-byte))
                    (block-header (make-array block-header-size :element-type 'octet)))
               (setf (aref block-header 0) first-byte)
               (bs-read-sequence block-header source :start 1 :eof-error-p t)
               (let ((header-crc (bs-read-le 4 source))
                     (real-header-crc (crc-32 block-header 0 (length block-header))))
                 (unless (= header-crc real-header-crc)
                   (die "Invalid block header CRC (expected ~8,'0x, got ~8,'0x)."
                        header-crc real-header-crc)))
               (handle-xz-block state block-header)
               (values +dummy-buffer+ 0 0 nil)))))

      (:data
       (multiple-value-bind (buffer start end finalp)
           (funcall (xzs-chunk-generator state))
         (setf (xzs-checksum state)
               (update-xz-checksum (xzs-checksum-info state)
                                   buffer start end
                                   (xzs-checksum state)))
         (incf (first (xzs-decompressed-sizes state))
               (- end start))
         (incf (xzs-total-decompressed-size state) (- end start))
         (when (>= (xzs-total-decompressed-size state)
                   (expt 2 63))
           (die "Total decompressed size exceeds 2^63 - 1 bytes."))
         (when finalp
           (setf (xzs-control-state state) :block-end))
         (values buffer start end nil)))

      (:block-end
       (when (xzs-block-expected-compressed-size state)
         (unless (= (cbs-count source) (cbs-limit source))
           (assert (< (cbs-count source) (cbs-limit source)))
           (die "XZ block is smaller than its declared size.")))

       (when (xzs-block-expected-decompressed-size state)
         (unless (= (first (xzs-decompressed-sizes state))
                    (xzs-block-expected-decompressed-size state))
           (die "Decompressed size doesn't match declared decompressed size.")))

       (let ((counted-source source)
             (real-compressed-size (cbs-count source)))
         (setf source (cbs-finish counted-source))
         (loop :repeat (mod (- real-compressed-size) 4) :do
           (unless (zerop (bs-read-byte source))
             (die "Block padding doesn't consist of null bytes.")))

         (let* ((checksum-size (xzs-checksum-size state))
                (checksum (bs-read-le checksum-size source))
                (real-checksum (finish-xz-checksum (xzs-checksum-info state)
                                                   (xzs-checksum state))))
           (incf (first (xzs-compressed-sizes state))
                 ;; XZ deliberately omits the padding in this calculation.
                 (+ real-compressed-size checksum-size))
           (unless (= checksum real-checksum)
             (die "Incorrect block checksum (expected ~v,'0x, got ~v,'0x)."
                  (* 2 checksum-size) checksum
                  (* 2 checksum-size) real-checksum)))

         (setf (xzs-control-state state) :block/index)
         (values +dummy-buffer+ 0 0 nil))))))

(pushnew :xz *known-formats*)
