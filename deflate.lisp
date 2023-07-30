(cl:in-package #:semz.decompress)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +min-deflate-block-bitsize+
    (min
     ;; Uncompressed block: Block header, no byte padding, zero length,
     ;; checksum, no content.
     (+ 3 0 16 16 0)
     ;; Fixed block: Block header, end of block marker.
     (+ 3 7)
     ;; Dynamic block (underestimate): Block header, hlit, hdist, hclen.
     (+ 3 5 5 4)))

  (define-constant +deflate-length-bases+
      #(3   4   5   6   7    8   9   10  11  13
        15  17  19  23  27   31  35  43  51  59
        67  83  99  115 131  163 195 227 258)
    :test 'equalp)
  (define-constant +deflate-length-extra-bits+
      #(0 0 0 0 0  0 0 0 1 1
        1 1 2 2 2  2 3 3 3 3
        4 4 4 4 5  5 5 5 0)
    :test 'equalp)

  (define-constant +deflate-dist-bases+
      #(1    2    3    4    5     7    9    13    17    25
        33   49   65   97   129   193  257  385   513   769
        1025 1537 2049 3073 4097  6145 8193 12289 16385 24577)
    :test 'equalp)
  (define-constant +deflate-dist-extra-bits+
      #(0 0 0  0  1   1  2  2  3  3
        4 4 5  5  6   6  7  7  8  8
        9 9 10 10 11  11 12 12 13 13)
    :test 'equalp)

  (defun base+bits (base bits)
    (+ base (expt 2 bits) -1))

  (defconstant +largest-deflate-expansion+
    (reduce #'max (map 'list #'base+bits +deflate-length-bases+ +deflate-length-extra-bits+)))

  (defconstant +largest-deflate-distance+
    (reduce #'max (map 'list #'base+bits +deflate-dist-bases+ +deflate-dist-extra-bits+))))




;;;; Dynamic Huffman trees

(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; The data needed to decode fixed/dynamic compressed blocks.
  (defclass deflate-huffman-info ()
    ((litlen-tree :accessor dhi-litlen-tree :initform nil)
     (dist-tree :accessor dhi-dist-tree :initform nil)
     ;; Special case for the distance tree. See `lengths->dist-ht'.
     (special-mode :accessor dhi-special-mode :initform nil)
     ;; The auxillary tree used for dynamic blocks. We only keep it around for
     ;; reuse as it's the only thing we'd repeatedly allocate otherwise.
     (codelen-tree :accessor dhi-codelen-tree :initform nil)))

  ;; Dummy code length vector whose associated Huffman tree will always trigger
  ;; an error since 30 and 31 are invalid distance codes.
  (define-constant +illegal-deflate-dist-lengths+
      (coerce #(0 0 0 0 0  0 0 0 0 0
                0 0 0 0 0  0 0 0 0 0
                0 0 0 0 0  0 0 0 0 0
                1 1)
              'ht-codelen-vector)
    :test 'equalp)

  ;; If all lengths are 0, except one which is 1, returns the latter's position.
  ;; Otherwise returns nil.
  (defun find-singular-one (lengths start end)
    (declare (type ht-codelen-vector lengths)
             (type array-length start end))
    (loop :with index = nil
          :for i :from start :below end
          :do (unless (zerop (aref lengths i))
                (if index
                    (return nil)
                    (if (= 1 (aref lengths i))
                        (setf index i)
                        (return nil))))
          :finally (return index)))

  ;; Like `lengths->ht', but allows the special cases of §3.2.7. Returns two
  ;; values: The Huffman tree and a symbol that identifies the special case.
  ;; Possible special cases: `nil', `:literals-only', `:single-code'.
  ;;
  ;; Does not hold onto `lengths', just like `lengths->ht'.
  (defun lengths->dist-ht (lengths max-overread-bits
                           &key (start 0) (end (length lengths))
                             ((:reuse-ht ht) nil))
    (declare (type ht-codelen-vector lengths)
             (type array-length start end)
             (optimize speed))
    ;; One code of zero means that no distance codes are ever used. We actually
    ;; detect this before reading distance codes; the illegal tree is insurance.
    (if (and (= (+ start 1) end)
             (zerop (aref lengths start)))
        (values (lengths->ht +illegal-deflate-dist-lengths+
                             max-overread-bits :le
                             :reuse-ht ht)
                :literals-only)
        ;; If all code lengths are 0 except for one length of 1, then only one
        ;; distance code can appear, which must be encoded as a zero bit. We map
        ;; the one bit to an illegal code (30/31, whichever wasn't used) and
        ;; correct the error message later.
        (let ((the-one-pos (find-singular-one lengths start end)))
          (if the-one-pos
              (let ((a (make-array 32 :element-type 'ht-codelen :initial-element 0))
                    (the-one-code (- the-one-pos start)))
                (declare (dynamic-extent a)) ; `lengths->ht' doesn't hold onto lengths
                (setf (aref a the-one-code) 1
                      (aref a (if (= the-one-code 31) 30 31)) 1)
                (values (lengths->ht a max-overread-bits :le
                                     :reuse-ht ht)
                        :single-code))
              ;; Otherwise this is a normal code length vector.
              (values (lengths->ht lengths max-overread-bits :le
                                   :start start :end end :reuse-ht ht)
                      nil)))))

  ;; `lengths' contains the litlen codes and then the dist codes. Again, doesn't
  ;; hold onto `lengths'.
  (defun lengths->dhi (lengths litlen-count dist-count max-overread-bits
                       &key ((:reuse-dhi dhi) nil))
    (setf dhi (or dhi (make-instance 'deflate-huffman-info))
          (dhi-litlen-tree dhi) (lengths->ht lengths max-overread-bits :le
                                             :start 0 :end litlen-count
                                             :reuse-ht (dhi-litlen-tree dhi))
          (values (dhi-dist-tree dhi) (dhi-special-mode dhi))
          (lengths->dist-ht lengths max-overread-bits
                            :start litlen-count :end (+ litlen-count dist-count)
                            :reuse-ht (dhi-dist-tree dhi)))
    dhi)

  ;; The attentive reader might notice that we later make use of the number of
  ;; trailing bits to optimize dynamic DHIs and wonder why don't we do this for
  ;; fixed DHIs here. Answer: The fixed DHI can only overread by at most 9-7=2
  ;; bits, so the minimum block bit size of 10 ensures that all blocks except
  ;; the final one can use overreading HTs. The slightly slower final block
  ;; doesn't really matter.
  (assert (>= +min-deflate-block-bitsize+ (- 9 7)))

  (flet ((repeat (x from to)
           (loop :for i :from from :to to :collect x)))
    (let ((lengths (coerce (append (repeat 8 0 143)
                                   (repeat 9 144 255)
                                   (repeat 7 256 279)
                                   (repeat 8 280 287)
                                   ;; This just reads 5-bit BE numbers.
                                   (repeat 5 0 31))
                           'ht-codelen-vector)))
      (defparameter *fixed-dhi-for-final-block*
        (lengths->dhi lengths 288 32 0))
      (defparameter *fixed-dhi-for-nonfinal-block*
        (lengths->dhi lengths 288 32 +min-deflate-block-bitsize+)))))

(defun read-dynamic-dhi (dhi lbr max-overread-bits)
  (let* ((litlen-count     (+ 257 (lbr-read-bits lbr 5)))
         (dist-count       (+   1 (lbr-read-bits lbr 5)))
         (codelen-count    (+   4 (lbr-read-bits lbr 4)))
         (total-code-count (+ litlen-count dist-count))
         (clen-lengths (make-array 19 :element-type 'ht-codelen :initial-element 0))
         ;; Codes 16/17/18 may explicitly expand across the boundary between
         ;; literals and distance codes, so we put both codes into one array.
         ;; Giving it the max size makes stack allocation easier.
         (codelens (make-array (+ 257 31 1 31) :element-type 'ht-codelen)))
    ;; Only passed to `lengths->dh[ti]', which don't hold onto their arguments.
    (declare (dynamic-extent clen-lengths codelens))

    (dotimes (i codelen-count)
      (setf (aref clen-lengths (svref #(16 17 18 0 8 7 9 6 10 5 11 4 12 3 13 2 14 1 15) i))
            (lbr-read-bits lbr 3)))
    (setf dhi (or dhi (make-instance 'deflate-huffman-info))
          (dhi-codelen-tree dhi) (lengths->ht clen-lengths max-overread-bits :le
                                              :reuse-ht (dhi-codelen-tree dhi)))
    (loop :with i = 0 :while (< i total-code-count) :do
      (let ((raw-code (ht-read-le-code lbr (dhi-codelen-tree dhi))))
        (if (<= 16 raw-code 18)
            (let ((expanded-size (ecase raw-code
                                   (16 (+ 3 (lbr-read-bits lbr 2)))
                                   (17 (+ 3 (lbr-read-bits lbr 3)))
                                   (18 (+ 11 (lbr-read-bits lbr 7))))))
              (unless (<= (+ i expanded-size) total-code-count)
                (die "Code lengths expand beyond bounds."))
              (fill codelens (if (= raw-code 16)
                                 (if (zerop i)
                                     (die "Tried to repeat non-existent last code length.")
                                     (aref codelens (- i 1)))
                                 0)
                    :start i :end (+ i expanded-size))
              (incf i expanded-size))
            (progn
              (setf (aref codelens i) raw-code)
              (incf i)))))
    ;; I considered banning codes without end-of-block markers here because
    ;; they're a blatant spec oversight, but they don't really change anything;
    ;; Deflate blocks can be arbitrarily long anyway.
    (lengths->dhi codelens litlen-count dist-count max-overread-bits :reuse-dhi dhi)))




;;;; Decompression
;;;
;;; Deflate naturally has a concept of `blocks' - regions of data that follow a
;;; particular compression scheme - but these may be of arbitrary size. We
;;; define chunks to be sections of a certain fixed size, with some wiggle room
;;; to avoid having to suspend/resume decompression during expansions.
(defclass deflate-state ()
  ((final-block-p :accessor ds-final-block-p
                  :initform nil
                  :type boolean)
   (bit-reader :accessor ds-bit-reader
               :initarg :bit-reader
               :type lsb-bit-reader)
   ;; This is the result buffer and window in one to simplify copying. Its size
   ;; is w + n + `+largest-deflate-expansion+' - 1, where `w' is the window size
   ;; and `n' is some arbitrary number that effectively controls chunk size. The
   ;; first `w' bytes are the window section and the rest is the result section.
   ;; Until the window is filled for the first time, we write directly into it
   ;; to simplify checks whether references are in bounds.
   ;;
   ;; The buffer must be emptied as soon as it contains w+n bytes since at that
   ;; point Huffman codes may expand to more bytes than the buffer can take.
   (buffer :accessor ds-buffer
           :initarg :buffer
           :type buffer)
   (fill-pointer :accessor ds-fill-pointer
                 :initarg :fill-pointer
                 :type array-length)
   ;; Init-time parameter, required to tell where the result buffer begins.
   ;; Bounded by 2^15 since references can't go further back anyway.
   (window-size :accessor ds-window-size
                :initarg :window-size
                :type (integer 0 #.(expt 2 15)))
   ;; The rest is an algebraic data type with `block-type' as its discriminant;
   ;; it implements suspension between and inside blocks.
   (block-type :accessor ds-block-type
               :initarg :block-type
               :initform :block-boundary
               :type (member
                      ;; We are about to start a block. Needs no data, the
                      ;; Deflate format gives us everything we need at the
                      ;; beginning of each block.
                      :block-boundary
                      ;; Uncompressed block; needs remaining number of bytes.
                      :uncompressed
                      ;; Fixed block; needs no data since we can decide which
                      ;; DHI to use via `final-block-p'.
                      :fixed
                      ;; Dynamic block; needs the DHI from the beginning of the
                      ;; block, but nothing otherwise.
                      :dynamic))
   (uncompressed-remaining-bytes :accessor ds-uncompressed-remaining-bytes
                                 :initform nil)
   ;; DHI for dynamic blocks. This is preserved even after the block ends so
   ;; that we can reuse it for later dynamic blocks.
   (dhi :accessor ds-dhi
        :initform nil
        :type (or null deflate-huffman-info))))

;;; If `buffer' contains this many elements, further Deflate expansions risk
;;; overrunning `buffer', so we should finish the chunk.
(defun deflate-buffer-fill-threshold (buffer)
  (- (length buffer) (- +largest-deflate-expansion+ 1)))

;;; Writes decompressed data into the buffer and returns the new fill pointer
;;; (but doesn't update it yet).
(defun decode-huffman-data (ds dhi)
  (declare (type deflate-state ds)
           (type deflate-huffman-info dhi)
           (optimize speed))
  (let* ((litlen-tree  (dhi-litlen-tree  dhi))
         (dist-tree    (dhi-dist-tree    dhi))
         (special-mode (dhi-special-mode dhi))
         (lbr          (ds-bit-reader   ds))
         (buffer       (ds-buffer       ds))
         (pointer      (ds-fill-pointer ds))
         (wsize        (ds-window-size  ds))
         (threshold    (deflate-buffer-fill-threshold buffer)))
    (declare (type buffer buffer)
             (type array-length pointer wsize threshold)
             (type huffman-tree litlen-tree dist-tree)
             (type lsb-bit-reader lbr))
    (flet ((decode-length (index)
             (declare (type (index-for +deflate-length-bases+) index)
                      (optimize speed))
             (+ (csvref +deflate-length-bases+ index)
                (lbr-read-bits lbr (csvref +deflate-length-extra-bits+ index))))

           (decode-distance (dist-code)
             (declare (type (integer 0 31) dist-code)
                      (optimize speed))
             (when (> dist-code 29)
               ;; See the remark before `lengths->dist-ht'.
               (ecase special-mode
                 ((nil)
                  (die "Distance code out of bounds (0-29): ~d" dist-code))
                 ((:single-code)
                  ;; The message is ambiguous because we can't distinguish a one
                  ;; bit (resolves to 30/31 by our hack) from a zero bit that
                  ;; just happens to resolve to 30/31. Doesn't really matter
                  ;; since either is invalid, but let's not lie in the error.
                  (die "Unique distance code is out of bounds (0-29) or is not ~
                        encoded as a zero bit."))))
             (+ (csvref +deflate-dist-bases+ dist-code)
                (lbr-read-bits lbr (csvref +deflate-dist-extra-bits+ dist-code)))))
      (declare (ftype (function ((index-for +deflate-length-bases+))
                                (integer 0 #.+largest-deflate-expansion+))
                      decode-length)
               (ftype (function ((integer 0 31)) (integer 0 #.+largest-deflate-distance+))
                      decode-distance))
      (loop
        (let ((code (ht-read-le-code lbr litlen-tree)))
          (cond
            ((<= 0 code 255)
             (setf (aref buffer pointer) code)
             (incf pointer))
            ((= code 256)
             (setf (ds-block-type ds) :block-boundary)
             (return pointer))
            ((<= 257 code 285)
             (when (eq :literals-only special-mode)
               (die "Length code in literal-only block: ~d" code))
             (let ((length (decode-length (- code 257)))
                   (distance (decode-distance (ht-read-le-code lbr dist-tree))))
               (declare (type (integer 0 #.+largest-deflate-expansion+) length)
                        (type (integer 0 #.+largest-deflate-distance+) distance))
               (unless (<= distance (min pointer wsize))
                 (die "Reference points back further (~d) than the window allows (~d)."
                      distance (min pointer wsize)))
               (copy-match buffer (- pointer distance) pointer length)
               (incf pointer length)))
            ;; It is possible to hit this branch! Codes 286 & 287 may feature in
            ;; the Huffman code construction and can therefore be encoded.
            (t (die "Invalid literal/length code: ~d" code))))
        (when (>= pointer threshold)
          (return pointer))))))

;;; Similarly returns the new fill pointer without setting it yet.
(defun decode-uncompressed-data (ds)
  (let* ((lbr    (ds-bit-reader   ds))
         (buffer (ds-buffer       ds))
         (start  (ds-fill-pointer ds))
         (amount (min (- (length buffer) start)
                      (ds-uncompressed-remaining-bytes ds)))
         (end    (+ start amount)))
    ;; We've read 32 bits of lengths before, so byte I/O should be available.
    (assert (lbr-byte-source-usable-p lbr))
    (bs-read-sequence buffer (lbr-source lbr) :start start :end end :eof-error-p t)
    (if (= amount (ds-uncompressed-remaining-bytes ds))
        (setf (ds-block-type ds) :block-boundary
              (ds-uncompressed-remaining-bytes ds) nil)
        (decf (ds-uncompressed-remaining-bytes ds) amount))
    end))




;;;; Interface

;;; The interface used by various `next-decompressed-chunk' methods. Has the
;;; same return values. `trailing-bits' tells us how many bits are expected
;;; after the Deflate data; we use this to use more overread optimizations.
(defun next-deflate-chunk (ds trailing-bits)
  (check-type ds deflate-state)
  (check-type trailing-bits integer)
  (setf (ds-fill-pointer ds)
        (flush-dict-buffer (ds-buffer ds) (ds-fill-pointer ds) (ds-window-size ds)))

  (let ((lbr (ds-bit-reader ds))
        (start (ds-fill-pointer ds)))
    (loop
      (when (eq :block-boundary (ds-block-type ds))
        (assert (not (ds-final-block-p ds)))
        (setf (ds-final-block-p ds) (= 1 (lbr-read-bits lbr 1)))
        (ecase (lbr-read-bits lbr 2)
          (#b00
           (lbr-flush-byte lbr)
           (let* ((len (lbr-read-bits lbr 16))
                  (checksum (lbr-read-bits lbr 16))
                  (required (logxor #xFFFF len)))
             (unless (= checksum required)
               (die "Checksum mismatch in uncompressed block (required ~4,'0x, got ~4,'0x)."
                    required checksum))
             (setf (ds-block-type ds) :uncompressed
                   (ds-uncompressed-remaining-bytes ds) len)))
          (#b01
           (setf (ds-block-type ds) :fixed))
          (#b10
           (setf (ds-block-type ds) :dynamic
                 (ds-dhi ds) (read-dynamic-dhi (ds-dhi ds) lbr
                                               (+ (if (ds-final-block-p ds)
                                                      0
                                                      +min-deflate-block-bitsize+)
                                                  trailing-bits))))
          (#b11 (die "Block uses reserved BTYPE."))))

      (let* ((buffer (ds-buffer ds))
             (end (ecase (ds-block-type ds)
                    (:uncompressed (decode-uncompressed-data ds))
                    (:fixed        (decode-huffman-data ds (if (ds-final-block-p ds)
                                                               *fixed-dhi-for-final-block*
                                                               *fixed-dhi-for-nonfinal-block*)))
                    (:dynamic      (decode-huffman-data ds (ds-dhi ds)))))
             (finalp (and (ds-final-block-p ds)
                          (eq :block-boundary (ds-block-type ds)))))
        (setf (ds-fill-pointer ds) end)
        (when (or finalp (>= end (deflate-buffer-fill-threshold buffer)))
          (return (values buffer start end finalp)))))))

(defmethod byte-source->decompression-state
    ((type (eql :deflate)) byte-source
     &key (window-size (expt 2 15)) prefix prefix-start prefix-end)
  (check-type window-size (integer 0 *))
  (let ((buffer (make-array (+ window-size (expt 2 15) +largest-deflate-expansion+ -1)
                            :element-type 'octet))
        (pointer 0))
    (unless (null prefix)
      (normalize-bounds prefix prefix-start prefix-end)
      (let ((amount (min window-size (- prefix-end prefix-start))))
        (replace buffer prefix
                 :start1 0 :end1 amount
                 :start2 (- prefix-end amount) :end2 prefix-end)
        (setf pointer amount)))
    (make-instance 'deflate-state
                   :window-size window-size
                   :buffer buffer
                   :fill-pointer pointer
                   :bit-reader (make-lsb-bit-reader :source byte-source))))

(defmethod next-decompressed-chunk ((ds deflate-state))
  (next-deflate-chunk ds 0))

(pushnew :deflate *known-formats*)
