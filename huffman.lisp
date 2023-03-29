;;;; Deflate Huffman codes
;;;
;;; Consider a Huffman tree whose codes are at most `n' bits long. Since Huffman
;;; codes are prefixless and minimal, any sequence of `n' bits starts with a
;;; unique valid code; the idea behind our Huffman code reader is to make a
;;; table that can map any sequence of `n' bits to a pair (i,l), where `i' is
;;; the item encoded by the code in front and `l' is the length of said code. We
;;; can then ensure `n' bits, look up the pair, discard `l' bits, and return the
;;; item `i' very quickly.
;;;
;;; If reading all `n' bits is not possible (e.g. because overreads are disabled
;;; and we're working with a format like raw Deflate that doesn't have enough
;;; trailing data), we can still use the lookup table with the bits we have
;;; currently buffered, padded with zero bits; while this will possibly give us
;;; a different code's data, we will nevertheless be able to tell that we don't
;;; have enough bits yet (since Huffman codes are prefixless, `l' is necessarily
;;; larger than our bit count) and can then retry after reading another byte.
;;;
;;; Since bit reading is naturally done in LSB-first order, we convert the
;;; table's indices from their natural MSB-first form to LSB-first. This
;;; tradeoff seems worth it in practice.
;;;
;;; Example: The Huffman code with n = 2 on the left would result in the table
;;; on the right.
;;;
;;; | item | code |  | index | length | item |
;;; |------+------|  |-------+--------+------|
;;; | 0    | 0    |  | #b00  | 1      | 0    |
;;; | 1    | 1,0  |  | #b01  | 2      | 1    |
;;; | 2    | 1,1  |  | #b10  | 1      | 0    |
;;;                  | #b11  | 2      | 2    |
;;;
;;; In Deflate, lengths are at most 15 and items are at most 287, so we store
;;; the (l,i) pair as (i << 4) | l and require 13 bits for table entries.
;;;
;;; In the end, table preprocessing makes up ~12% of the runtime, most of it for
;;; redundant entries of short codes. Since short codes are supposed to be
;;; frequent (assuming the encoder does its job correctly), this suggests that a
;;; hybrid approach may be better.
;;;
;;; For instance, one could use a lookup table for the first 12 bits (this
;;; roughly accounts for 95% of all codes). Indices that correspond to longer
;;; codes then resolve to a smaller second lookup table, where we repeat the
;;; process with the remaining bits. It's easy to just concatenate these smaller
;;; tables into one and resolve to an offset.
;;;
;;; I've actually tried this but decided it wasn't worth it; while it speeds up
;;; decompression by ~1.1x, the code becomes significantly messier. It might be
;;; worth reviving once the rest is faster or once we support other formats that
;;; require longer codes.
(cl:in-package #:semz.decompress)

(deftype dht-code-length ()
  '(integer 0 15))

(deftype dht-code-length-vector ()
  '(simple-array dht-code-length (*)))

(deftype dht-item ()
  '(integer 0 287))

(deftype dht-entry ()
  '(unsigned-byte 13))

(declaim (inline dht-table dht-min-code-length dht-max-code-length dht-full-read-p))
(defstruct (deflate-huffman-tree (:conc-name dht-))
  (table (required-argument :table) :type (simple-array dht-entry (*)))
  (min-code-length (required-argument :min-code-length) :type (integer 1 15))
  (max-code-length (required-argument :max-code-length) :type (integer 1 15))
  ;; If true, we can always safely read `max-code-length' bits at once to speed
  ;; up the decoding process, rather than having to go byte by byte.
  full-read-p)

(declaim (ftype (function (lsb-bit-reader deflate-huffman-tree) dht-item) dht-read-code)
         (inline dht-read-code))
(defun dht-read-code (lbr dht)
  (declare (type lsb-bit-reader lbr)
           (type deflate-huffman-tree dht)
           (optimize speed))
  (if (dht-full-read-p dht)
      (let ((max-code-length (dht-max-code-length dht)))
        (lbr-ensure-bits lbr max-code-length)
        (let* ((index (ldb (byte max-code-length 0) (lbr-buffer lbr)))
               (entry (aref (dht-table dht) index))
               (code-length (ldb (byte 4 0) entry)))
          (lbr-dump-bits lbr code-length)
          (ash entry -4)))
      (loop :for len :from (dht-min-code-length dht) :to (dht-max-code-length dht)
            :do (lbr-ensure-bits lbr len)
                (let* ((entry (aref (dht-table dht) (ldb (byte len 0) (lbr-buffer lbr))))
                       (code-length (ldb (byte 4 0) entry)))
                  (when (<= code-length len)
                    (lbr-dump-bits lbr code-length)
                    (return (ash entry -4))))
            :finally (error "Corrupt Huffman tree."))))

(declaim (ftype (function ((unsigned-byte 16) (integer 0 16)) (unsigned-byte 16))
                reverse-small-integer)
         (inline reverse-small-integer))
(defun reverse-small-integer (x n)
  (declare (type (unsigned-byte 16) x)
           (type (integer 0 16) n)
           (optimize speed))
  ;; Reverse as 16-bit integer first using a standard trick, then fix up for n.
  (setf x (logior (ash (logand x #b1111111100000000) -8)
                  (ash (logand x #b0000000011111111) +8)))
  (setf x (logior (ash (logand x #b1111000011110000) -4)
                  (ash (logand x #b0000111100001111) +4)))
  (setf x (logior (ash (logand x #b1100110011001100) -2)
                  (ash (logand x #b0011001100110011) +2)))
  (setf x (logior (ash (logand x #b1010101010101010) -1)
                  (ash (logand x #b0101010101010101) +1)))
  (ash x (- (- 16 n))))

;;; From the Deflate spec:
;;;
;;; - All codes of a given length have lexicographically consecutive values, in
;;;   the same order as the symbols they represent. This corresponds to
;;;   numerical ordering after MSB-first bit-sequence-to-integer conversion.
;;;
;;; - Shorter codes lexicographically precede longer codes.
;;;
;;; As a result, a Huffman tree is uniquely determined by the sequence of code
;;; lengths. However, not every sequence determines a Huffman tree; see below.
;;; Distance code trees admit two special cases that have to be handled
;;; separately, so they get their own conversion function. Neither conversion
;;; function holds onto `lengths' in order to allow `dynamic-extent'
;;; declarations in `deflate.lisp'.
(defun lengths->dht (lengths max-overread-bits
                     &key (start 0) (end (length lengths))
                     ;; If non-nil, write data into this existing DHT instead.
                       ((:reuse-dht dht) nil))
  (declare (type dht-code-length-vector lengths)
           (type integer max-overread-bits)
           (type array-length start end)
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note)
           (optimize speed))
  (assert (<= 1 (- end start) 288))
  (let* ((max-code-length
           (reduce #'max lengths :start start :end end :initial-value 1))
         (min-code-length
           (reduce #'min lengths :start start :end end :initial-value 15
                                 :key (lambda (x)
                                        (declare (type dht-code-length x))
                                        (if (zerop x)
                                            15
                                            x))))
         (2^max (expt 2 max-code-length))
         ;; True about 2/3 of the time in practice when `max-overread-bits' = 0.
         (full-read-p (>= max-overread-bits (- max-code-length min-code-length))))
    (declare (type dht-code-length max-code-length min-code-length)
             (type (integer 0 #.(expt 2 15)) 2^max))
    ;; If codes are at most `n' bits long, then the fact that Huffman coding is
    ;; prefixless implies that each k-bit code will block the use of 2^(n-k)
    ;; n-bit codes. A length sequence determines a Huffman tree if and only if
    ;; exactly 2^n codes are made unusable in total; if less, then some codes
    ;; remain unassigned, and if more, some codes are can't have the prescribed
    ;; length (and would be ambiguous even when extended).
    (let ((unusable-codes (reduce #'+ lengths :start start :end end
                                              :key (lambda (len)
                                                     (declare (type dht-code-length len))
                                                     (if (zerop len)
                                                         0
                                                         (expt 2 (- max-code-length len)))))))
      ;; Very liberal bound, but trivial to prove correct.
      (declare (type (integer 0 #.(* 288 (expt 2 14))) unusable-codes))
      (cond
        ((< unusable-codes 2^max) (die "Underfull Huffman tree."))
        ((> unusable-codes 2^max) (die "Overfull Huffman tree."))))
    (setf dht (or dht (make-deflate-huffman-tree
                       :max-code-length max-code-length
                       :min-code-length min-code-length
                       :table (make-array 2^max :element-type 'dht-entry)
                       :full-read-p full-read-p)))
    (check-type dht deflate-huffman-tree)
    ;; Especially smaller Deflate buffers don't use the maximum length of 15
    ;; bits, so allocating the table as needed makes decompression of many small
    ;; buffers noticeably faster. For large buffers, it amortizes.
    (let ((table (if (> 2^max (length (dht-table dht)))
                     (make-array 2^max :element-type 'dht-entry)
                     (dht-table dht))))
      (declare (type (simple-array dht-entry (*)) table)
               (optimize speed))
      (loop
        ;; Next Huffman code to be assigned, represented as MSB of length `len'.
        ;; This can hit 2^n due to the final `incf'.
        :with next-code :of-type (integer 0 #.(expt 2 15)) = 0
        :for len :from min-code-length :to max-code-length
        :do ;; Extend code to `len' bits. For the first code this is a no-op.
            (setf next-code (ash next-code 1))
            (loop :for src-index :from start :below end
                  :for item :from 0 :to 287 ; bound helps type inference
                  :when (= len (aref lengths src-index)) :do
                    ;; `item' is represented by the code stored MSB-first in
                    ;; `next-code' now, but we want to index using LSB-first.
                    (let ((le-code (reverse-small-integer next-code len))
                          (entry (logior (ash item 4) len)))
                      ;; This loop takes up all the preprocessing time.
                      (loop :for dest-index :from le-code :below 2^max :by (expt 2 len)
                            :do (setf (aref table dest-index) entry)))
                    (incf next-code)))
      (setf (dht-max-code-length dht) max-code-length
            (dht-min-code-length dht) min-code-length
            (dht-table dht) table
            (dht-full-read-p dht) full-read-p)
      dht)))

;;; Dummy code length vector whose associated Huffman tree will always trigger
;;; an error since 30 and 31 are invalid distance codes.
(define-constant +illegal-deflate-dist-lengths+
    (coerce #(0 0 0 0 0  0 0 0 0 0
              0 0 0 0 0  0 0 0 0 0
              0 0 0 0 0  0 0 0 0 0
              1 1)
            'dht-code-length-vector)
  :test 'equalp)

;;; If all lengths are 0, except one which is 1, returns the latter's position.
;;; Otherwise returns nil.
(defun find-singular-one (lengths start end)
  (declare (type dht-code-length-vector lengths)
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

;; Like `lengths->dht', but allows the special cases of §3.2.7. Returns two
;; values: The Huffman tree and a symbol that identifies the special case.
;; Possible special cases: `nil', `:literals-only', `:single-code'.
;;
;; Does not hold onto `lengths', just like `lengths->dht'.
(defun lengths->dist-dht (lengths max-overread-bits
                          &key (start 0) (end (length lengths))
                            ((:reuse-dht dht) nil))
  (declare (type dht-code-length-vector lengths)
           (type array-length start end)
           (optimize speed))
  ;; One code of zero means that no distance codes are ever used. We actually
  ;; detect this before reading distance codes; the illegal tree is insurance.
  (if (and (= (+ start 1) end)
           (zerop (aref lengths start)))
      (values (lengths->dht +illegal-deflate-dist-lengths+ max-overread-bits :reuse-dht dht)
              :literals-only)
      ;; If all code lengths are 0 except for one length of 1, then only one
      ;; distance code can appear, which must be encoded as a zero bit. We map
      ;; the one bit to an illegal code (30/31, whichever wasn't used) and
      ;; correct the error message later.
      (let ((the-one-pos (find-singular-one lengths start end)))
        (if the-one-pos
            (let ((a (make-array 32 :element-type 'dht-code-length :initial-element 0))
                  (the-one-code (- the-one-pos start)))
              (declare (dynamic-extent a)) ; `lengths->dht' doesn't hold onto lengths
              (setf (aref a the-one-code) 1
                    (aref a (if (= the-one-code 31) 30 31)) 1)
              (values (lengths->dht a max-overread-bits :reuse-dht dht)
                      :single-code))
            ;; Otherwise this is a normal code length vector.
            (values (lengths->dht lengths max-overread-bits :start start :end end :reuse-dht dht)
                    nil)))))
