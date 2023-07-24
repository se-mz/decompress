;;;; Bzip2
;;;
;;; Based on the reference implementation, as well as this document by Joe Tsai:
;;; https://github.com/dsnet/compress/blob/master/doc/bzip2-format.pdf
;;;
;;; Instead of the refimpl's tangled state machine, we implement the
;;; decompression steps separately (with one exception).
(cl:in-package #:semz.decompress)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +bzip2-max-block-size+ 900000))

;;; Normally, the algorithm to calculate bzip2's CRC uses
;;;
;;;     state := (state << 8) ^ table[(state>>24) ^ byte];
;;;
;;; if we reverse the byte order for `state' and all `table' entries, this gives
;;;
;;;     state := (state >> 8) ^ table[(state & 0xFF) ^ byte],
;;;
;;; which is the same formula we use for CRC-32. Therefore, a little
;;; preprocessing lets us reuse the code for the CRC-32 implementation.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (declaim (type (simple-array (unsigned-byte 32) (256))
                 +bzip2-preprocessed-crc-table+))
  (define-constant +bzip2-preprocessed-crc-table+
      (map '(simple-array (unsigned-byte 32) (*))
           #'reverse-ub32-byte-order
           +bzip2-crc-table+)
    :test 'equalp))

(define-update-crc update-bzip2-crc +bzip2-preprocessed-crc-table+)

(defun start-bzip2-crc ()
  #xFFFFFFFF)
(defun finish-bzip2-crc (state)
  (reverse-ub32-byte-order (logxor #xFFFFFFFF state)))
(defun bzip2-crc (data start end)
  (finish-bzip2-crc (update-bzip2-crc data start end (start-bzip2-crc))))

;;; This is used to combine all the block CRCs into one stream CRC at the end.
(defun start-bzip2-stream-crc ()
  #x00000000)
(defun update-bzip2-stream-crc (state new-block-crc)
  (logxor (logior (ash (ldb (byte 31 0) state) 1)
                  (ldb (byte 1 31) state))
          new-block-crc))
(defun finish-bzip2-stream-crc (state)
  state)


;;; Bzip2 compression starts with a simple RLE, where 4 <= n <= 259 consecutive
;;; copies of the same character X may be replaced with XXXX followed by n-4.
;;;
;;; Since we only know the buffer size of the RLE-compressed data (rather than
;;; the final decompressed data), this is the only step that is interruptible.
;;; Otherwise, we only allow interruptions between blocks.

(defstruct (bzip2-rle1-state (:conc-name rle1-))
  (src-i 0) (reps 0) (last-b nil))

(defun decode-bzip2-rle1 (src src-end dest state)
  (declare (type buffer src dest)
           (type array-length src-end)
           (type bzip2-rle1-state state)
           (optimize speed))
  (let ((src-i  (rle1-src-i state))
        (reps   (rle1-reps state))
        (last-b (rle1-last-b state))

        (dest-i 0)
        ;; For simplicity, we interrupt once we can no longer guarantee that all
        ;; possible expansions will fit.
        (dest-end (- (length dest) 255)))
    (declare (type array-length src-i src-end dest-i dest-end)
             (type (or null octet) last-b)
             (type (integer 0 3) reps))

    (loop :while (and (< src-i src-end) (< dest-i dest-end)) :do
      (let ((b (aref src src-i)))
        (declare (type octet b))
        (if (< reps 3)
            (progn
              (if (eql b last-b)
                  (incf reps)
                  (setf reps 0))
              (setf (aref dest dest-i)
                    (aref src src-i))
              (incf src-i)
              (incf dest-i)
              (setf last-b b))
            (progn
              (loop :repeat b :do
                (setf (aref dest dest-i) last-b)
                (incf dest-i))
              (setf last-b nil
                    reps 0)
              (incf src-i)))))
    (setf (rle1-src-i  state) src-i
          (rle1-reps   state) reps
          (rle1-last-b state) last-b)
    dest-i))


;;; To work around a historical performance issue in bzip2's implementation of
;;; the (upcoming) BWT, the format allows randomizing highly repetitive blocks.
;;; Essentially, there is a fixed list of Random™ indices where we flip the
;;; lowest order bit. If you want test files for this feature, you will have to
;;; grab an old version of bzip2; the current encoder no longer outputs such
;;; blocks. Compressing lots of /dev/zero output tends to produce them.

(defun derandomize-bzip2-block (data data-end)
  (declare (type buffer data)
           (type array-length data-end))
  (loop :for rand-i :from 0
        :for skip = (aref +bzip2-random-numbers+
                          (mod rand-i (length +bzip2-random-numbers+)))
        ;; The -2 is an artifact of the weird loop shape bzip2 uses for this.
        :for data-i = (- skip 2) :then (+ data-i skip)
        :while (< data-i data-end)
        :do (setf (aref data data-i) (logxor 1 (aref data data-i)))))


;;; Next up is the Burrows-Wheeler transform, the centerpiece of bzip2. This
;;; implementation is based on the one in the document by Joe Tsai, which in
;;; turn is based on the reference implementation. If you want to compare the
;;; two, note that `cumm' corresponds to `unzftab', `perm' corresponds to the
;;; upper 24 bits of `tt', and `data' corresponds to the lower 8 bits of `tt'.
;;;
;;; This step takes up the majority (~40%) of the total decompression runtime.

(deftype bzip2-block-index ()
  `(integer 0 ,+bzip2-max-block-size+))

;;; `data' is the input, `result' the output, `perm' is an auxillary array that
;;; can be preallocated.
(defun decode-bzip2-bwt (data data-end origin-pointer perm result)
  (declare (type buffer data result)
           (type (simple-array bzip2-block-index (*)) perm)
           (type array-length data-end origin-pointer)
           (optimize speed))
  (let ((cumm (make-array 256 :element-type 'array-length :initial-element 0))
        (n 0))
    (declare (type (simple-array array-length (*)) cumm)
             (type array-length n))

    (dotimes (i data-end)
      (incf (aref cumm (aref data i))))
    (dotimes (i 256)
      (shiftf (aref cumm i) n (+ n (aref cumm i))))

    (dotimes (i data-end)
      (let ((v (aref data i)))
        (setf (aref perm (aref cumm v)) i)
        (incf (aref cumm v))))

    (let ((i (aref perm origin-pointer)))
      (declare (type bzip2-block-index i))
      (dotimes (j data-end)
        (declare (type array-length j))
        (setf (aref result j) (aref data i)
              i (aref perm i))))))


;;; The data then goes through a move-to-front transform, which replaces the
;;; elements with indices into a maintained stack of the most recently used
;;; symbols. This transform is also used later to encode some metadata, but in
;;; either case there are at most 256 distinct symbols, letting us revert this
;;; operation in place on octet buffers.
;;;
;;; This step takes up about 25% of the runtime. The refimpl uses a less naive
;;; implementation which may be worth investigating at a later point.

(defun decode-bzip2-mtf-in-place (data data-end symbols)
  (declare (type buffer data symbols)
           (type array-length data-end)
           (optimize speed))
  ;; We don't need `symbols' after this, but mutating it seems counterintuitive.
  (let ((stack (make-array 256 :element-type 'octet :initial-element 0)))
    (declare (dynamic-extent stack)
             (type buffer stack))
    (replace stack symbols)
    (dotimes (i data-end)
      (let* ((index (aref data i))
             (x (aref stack index)))
        (setf (aref data i) x)
        ;; `stack' is small enough for a simple loop to beat `replace'.
        (loop :for j :from index :downto 1 :do
          (setf (aref stack j) (aref stack (- j 1))))
        (setf (aref stack 0) x)))))


;;; Finally, we RLE runs of zero octets and Huffman encode the result. This RLE
;;; stage expands the alphabet, so if we were to revert these two stages
;;; separately, we might need a non-octet intermediate buffer. It ends up being
;;; simpler to just revert both stages at once. The refimpl goes even further
;;; and performs the MTF transform in one go as well.
;;;
;;; A run of zeroes is represented by a sequence of new symbols A and B; if
;;; there are `n' zeroes in a row, then write n+1 as a k-bit little endian
;;; number, strip off the trailing one bit, and respectively replace 0 with A
;;; and 1 with B. The data is also terminated by a new end of block marker EOB.
;;; Note that we no longer need a symbol for the zero octet after this, so the
;;; alphabet size increases by 2, not 3. We order the new alphabet as follows:
;;; A, B, 1, 2, 3, ..., K, EOB, where K is the largest index from the preceding
;;; MTF stage.
;;;
;;; The Huffman encoding is then pretty standard, but note that the tree may be
;;; changed every 50 symbols to any tree from a predefined group of up to six.
;;;
;;; This step takes up about 20% of the runtime.

;;; `n' A/B codes in a row expand to at least 2^n - 1 zeroes. We weed out
;;; obviously overlong A/B sequences by ensuring that 2^n - 1 <= 900000, or
;;; equivalently n <= log_2(900001).
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +bzip2-ab-bound+
    (floor (log (+ +bzip2-max-block-size+ 1) 2))))

;;; Returns the number of elements written to `dest'.
(defun decode-bzip2-huffman+rle2 (mbr dest trees selectors symbol-count)
  (declare (type msb-bit-reader mbr)
           (type buffer dest selectors)
           (type simple-vector trees)
           ;; Blocks without symbols are necessarily empty. It makes no sense to
           ;; generate these because an empty file doesn't require any blocks at
           ;; all; the refimpl rejects blocks without symbols and so do we.
           (type (integer 1 256) symbol-count)
           (optimize speed))
  (let ((dest-i 0)
        ;; How many A/B codes we read in a row so far.
        (ab-length 0)
        ;; Little endian number where A=0 and B=1, without the trailing 1.
        (ab-value 0)
        (eob-symbol (+ symbol-count 1)))
    (declare (type array-length dest-i)
             (type (integer 0 #.+bzip2-ab-bound+) ab-length)
             (type (unsigned-byte #.+bzip2-ab-bound+) ab-value)
             (type (integer 2 257) eob-symbol))
    (loop
      :named main
      ;; The RLE cannot increase the number of elements (although it obviously
      ;; increases the alphabet size): Non-zero octets are kept and zero octets
      ;; are either replaced by an A or compressed. Since there is exactly one
      ;; way to perform RLE compression in this scheme, `n' octets result in at
      ;; most n+1 Huffman codes (+1 for the EOB).
      :for selector-i :from 0 :to (ceiling (+ +bzip2-max-block-size+ 1) 50) :do
        (unless (< selector-i (length selectors))
          (die "Ran out of selectors before end of block."))
        ;; We check that tree selectors are in bounds during header parsing.
        (let ((ht (svref trees (aref selectors selector-i))))
          (declare (type huffman-tree ht))
          (loop :repeat 50 :do
            ;; The codes can't go beyond symbol-count + 1 due to the way the
            ;; trees are constructed in `read-bzip2-trees' and the fact that we
            ;; reject underfull Huffman trees.
            (let ((code (ht-read-be-code mbr ht)))
              (if (< code 2)
                  (progn
                    (unless (< ab-length +bzip2-ab-bound+)
                      (die "A/B run cannot possibly stay in bounds."))
                    (setf (ldb (byte 1 ab-length) ab-value) code)
                    (incf ab-length))
                  (progn
                    ;; EOB or non-A/B symbol => finish any pending RLE expansion
                    (unless (zerop ab-length)
                      (let ((expansion-size (- (logior ab-value (ash 1 ab-length))
                                               1)))
                        (declare (type (unsigned-byte #.(+ 1 +bzip2-ab-bound+))))
                        (unless (<= dest-i (- (length dest) expansion-size))
                          (die "A/B run expands beyond block size."))
                        (loop :repeat expansion-size :do
                          (setf (aref dest dest-i) 0)
                          (incf dest-i)))
                      (setf ab-length 0
                            ab-value 0))

                    (when (= code eob-symbol)
                      (return-from main))

                    (unless (< dest-i (length dest))
                      (die "Too many codes/expansions."))
                    (setf (aref dest dest-i) (- code 1))
                    (incf dest-i))))))
      :finally (error "Incorrect selector count bound."))
    dest-i))


;;; Tree selectors are Huffman encoded after an MTF transform; trees are
;;; specified via code lengths like in Deflate. The code lengths are Huffman
;;; encoded after a type of delta encoding.

;;; Stream footer magic bytes + CRC
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +bzip2-trailing-bits+ (+ 48 32)))

(defparameter *bzip2-selector-tree*
  (lengths->ht (coerce #(1 2 3 4 5 6 6) 'ht-codelen-vector)
               +bzip2-trailing-bits+ :be))

(defun read-bzip2-selectors (mbr selector-count tree-count)
  (let ((selectors (make-array selector-count :element-type 'octet)))
    (dotimes (i (length selectors))
      (let ((sel (ht-read-be-code mbr *bzip2-selector-tree*)))
        (unless (< sel tree-count)
          (die "Invalid selector: ~d" sel))
        (setf (aref selectors i) sel)))
    (decode-bzip2-mtf-in-place selectors (length selectors)
                               (load-time-value (coerce #(0 1 2 3 4 5) 'buffer)))
    selectors))

(defparameter *bzip2-trees-tree*
  (lengths->ht (coerce #(2 2 1) 'ht-codelen-vector)
               +bzip2-trailing-bits+ :be))

(defun read-bzip2-trees (mbr tree-count symbol-count &key tree-vector)
  (let ((result (or tree-vector (make-array 6 :initial-element nil))))
    (dotimes (i tree-count result)
      (setf (aref result i)
            ;; The reference implementation accepts underfull Huffman trees; we
            ;; don't because it simplifies the code. Afaict the only reason to
            ;; output such trees is rank laziness; whenever you have a branch
            ;; with one child, it'd be more efficient to just make the code for
            ;; the unique child one bit shorter.
            (lengths->ht
             (let ((codelens (make-array (+ 2 symbol-count) :element-type 'ht-codelen))
                   (current-codelen (mbr-read-bits mbr 5)))
               (dotimes (i (length codelens) codelens)
                 (setf (aref codelens i)
                       (loop
                         ;; The refimpl hereby enforces that all code lengths
                         ;; are used. While we already remove the unused octets
                         ;; anyway, this also means that we can't elide the A/B
                         ;; symbols and EOB marker from the tree. Convenient.
                         (unless (<= 1 current-codelen 20)
                           (die "Code length goes out of bounds."))
                         (ecase (ht-read-be-code mbr *bzip2-trees-tree*)
                           (0 (incf current-codelen))
                           (1 (decf current-codelen))
                           (2 (return current-codelen)))))))
             +bzip2-trailing-bits+ :be
             :reuse-ht (aref result i))))))


;;; And at the very end, we have the usual header management.

(defstruct (bzip2-block-info (:conc-name bbi-))
  expected-crc crc randomizedp origin-pointer symbols selectors trees)

(defun parse-bzip2-block-header (mbr &key tree-vector)
  (let ((crc (mbr-read-bits mbr 32))
        (randomizedp (= 1 (mbr-read-bits mbr 1)))
        (origin-pointer (mbr-read-bits mbr 24))
        (l1-map (reverse-small-integer (mbr-read-bits mbr 16) 16))
        (symbol-map (make-array 256 :element-type 'bit :initial-element 0)))
    ;; The refimpl rejects this case as well.
    (when (zerop l1-map)
      (die "Block declares no used symbols."))

    (dotimes (i 16)
      (when (logbitp i l1-map)
        (let ((l2-map (reverse-small-integer (mbr-read-bits mbr 16) 16)))
          (dotimes (j 16)
            (when (logbitp j l2-map)
              (setf (aref symbol-map (+ (* 16 i) j)) 1))))))

    (let ((symbols (make-array (count 1 symbol-map) :element-type 'octet))
          (next-free-symbol 0))
      (dotimes (i (length symbol-map))
        (when (= 1 (aref symbol-map i))
          (setf (aref symbols next-free-symbol) i)
          (incf next-free-symbol)))

      (let ((tree-count (mbr-read-bits mbr 3))
            (selector-count (mbr-read-bits mbr 15)))
        ;; The refimpl rejects blocks with a single tree; this is probably to
        ;; simplify the format, since a lack of tree choice obsoletes selectors
        ;; and making selectors optional complicates things. I'm thankful.
        (unless (<= 2 tree-count 6)
          (die "Illegal tree count: ~d" tree-count))
        ;; Blocks need at the very least an EOB code.
        (unless (> selector-count 0)
          (die "Block defines no selectors."))

        (let ((selectors (read-bzip2-selectors mbr selector-count tree-count))
              (trees (read-bzip2-trees mbr tree-count (length symbols)
                                       :tree-vector tree-vector)))
          (make-bzip2-block-info :expected-crc crc
                                 :crc (start-bzip2-crc)
                                 :randomizedp randomizedp
                                 :origin-pointer origin-pointer
                                 :symbols symbols
                                 :selectors selectors
                                 :trees trees))))))

(defclass bzip2-state ()
  ((bit-reader :accessor bz-bit-reader :initarg :bit-reader :type msb-bit-reader)
   (block-size :accessor bz-block-size :initarg :block-size :type (integer 100000 900000))
   (stream-crc :accessor bz-stream-crc :initform (start-bzip2-stream-crc))

   ;; This is block-local, but we want to reuse the Huffman trees. This means we
   ;; always need to provide six slots.
   (trees :accessor bz-trees :initarg :trees :type simple-vector)

   ;; The various temporary buffers used to decode a block. Since we reuse them,
   ;; we need a length field.
   (bwt-size :accessor bz-bwt-size)
   (pre-bwt-buffer  :accessor bz-pre-bwt-buffer  :initarg :pre-bwt-buffer
                    :type buffer)
   (temp-bwt-buffer :accessor bz-temp-bwt-buffer :initarg :temp-bwt-buffer
                    :type (simple-array bzip2-block-index (*)))
   (post-bwt-buffer :accessor bz-post-bwt-buffer :initarg :post-bwt-buffer
                    :type buffer)
   ;; This buffer doesn't use `bwt-size'; it exists to deal with the first RLE.
   (output-buffer :accessor bz-output-buffer :initarg :output-buffer
                  :type buffer)

   ;; Valid keyword values: block-boundary, rle1, eof. The rest is required to
   ;; interrupt during the first RLE.
   (state :accessor bz-state :initform :block-boundary)
   (block-info :accessor bz-block-info)
   (rle1-state :accessor bz-rle1-state)))

(defmethod byte-source->decompression-state ((format (eql :bzip2)) source &key)
  (let ((mbr (make-msb-bit-reader :source source)))
    (let ((magic1 (mbr-read-bits mbr 8))
          (magic2 (mbr-read-bits mbr 8)))
      (unless (and (= magic1 #x42) (= magic2 #x5a))
        (die "Incorrect bzip2 magic bytes: ~2,'0x ~2,'0x" magic1 magic2)))

    (let ((version (mbr-read-bits mbr 8))
          (level   (mbr-read-bits mbr 8)))
      (unless (= version #x68) ;; "h"
        (die "Unrecognized bzip version: ~2,'0x" version))
      (unless (<= #x31 level #x39) ;; "1" - "9"
        (die "Invalid bzip2 compression level: ~2,'0x" level))

      (let ((block-size (* 100000 (- level #x30))))
        (values
         (make-instance 'bzip2-state
                        :bit-reader (make-msb-bit-reader :source source)
                        :block-size block-size
                        :trees (make-array 6 :initial-element nil)
                        :pre-bwt-buffer  (make-array block-size :element-type 'octet)
                        :temp-bwt-buffer (make-array block-size :element-type 'bzip2-block-index)
                        :post-bwt-buffer (make-array block-size :element-type 'octet)
                        :output-buffer (make-array (expt 2 17) :element-type 'octet))
         (list :block-size block-size))))))

;;; Bzip2 multi-member files are concatenations. Bzip2 buffer sizes are at the
;;; point where reuse could be worth it, but it's not urgent.
(defmethod make-reset-state ((bz bzip2-state))
  (byte-source->decompression-state :bzip2 (mbr-source (bz-bit-reader bz))))

(defmethod next-decompressed-chunk ((state bzip2-state))
  (let ((mbr (bz-bit-reader state)))
    (ecase (bz-state state)
      (:block-boundary
       (let ((magic (mbr-read-bits mbr 48)))
         (case magic
           ;; Block header
           (#x314159265359
            (let* ((bbi (parse-bzip2-block-header mbr :tree-vector (bz-trees state)))
                   (bwt-size (decode-bzip2-huffman+rle2 mbr
                                                        (bz-pre-bwt-buffer state)
                                                        (bbi-trees bbi)
                                                        (bbi-selectors bbi)
                                                        (length (bbi-symbols bbi)))))
              (decode-bzip2-mtf-in-place (bz-pre-bwt-buffer state)
                                         bwt-size
                                         (bbi-symbols bbi))
              (decode-bzip2-bwt (bz-pre-bwt-buffer state)
                                bwt-size
                                (bbi-origin-pointer bbi)
                                (bz-temp-bwt-buffer state)
                                (bz-post-bwt-buffer state))
              (when (bbi-randomizedp bbi)
                (derandomize-bzip2-block (bz-post-bwt-buffer state) bwt-size))

              (setf (bz-block-info state) bbi
                    (bz-bwt-size state) bwt-size
                    (bz-rle1-state state) (make-bzip2-rle1-state)
                    (bz-state state) :rle1)
              ;; Just tail call because we know the next state can't recurse.
              (next-decompressed-chunk state)))

           ;; Stream footer
           (#x177245385090
            (let ((expected-stream-crc (mbr-read-bits mbr 32))
                  (real-stream-crc (finish-bzip2-stream-crc (bz-stream-crc state))))
              (unless (= expected-stream-crc real-stream-crc)
                (die "Incorrect stream CRC (expected ~8,'0x, got ~8,'0x)"
                     expected-stream-crc real-stream-crc)))

            ;; Sanity check
            (mbr-flush-byte mbr)
            (assert (mbr-byte-source-usable-p mbr))

            (setf (bz-state state) :eof)
            (values +dummy-buffer+ 0 0 t))
           (otherwise
            (die "Unrecognized magic bytes on block boundary.")))))

      (:eof (error "Called `next-decompressed-chunk' on a finished bzip2 stream."))

      (:rle1
       (let* ((rle1 (bz-rle1-state state))
              (bbi (bz-block-info state))
              (dest-i (decode-bzip2-rle1 (bz-post-bwt-buffer state)
                                         (bz-bwt-size state)
                                         (bz-output-buffer state)
                                         rle1)))
         (setf (bbi-crc bbi)
               (update-bzip2-crc (bz-output-buffer state) 0 dest-i (bbi-crc bbi)))

         (when (= (rle1-src-i rle1) (bz-bwt-size state))
           (let ((crc (finish-bzip2-crc (bbi-crc bbi))))
             (unless (= crc (bbi-expected-crc bbi))
               (die "Invalid block CRC (expected ~8,'0x, got ~8,'0x)."
                    (bbi-expected-crc bbi) crc))
             (setf (bz-stream-crc state)
                   (update-bzip2-stream-crc (bz-stream-crc state) crc)))
           (setf (bz-state state) :block-boundary))

         (values (bz-output-buffer state) 0 dest-i nil))))))

(pushnew :bzip2 *known-formats*)
