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
;;; For MSB-first readers, we simply left shift the code to the correct length.
;;; For LSB-first readers, since bit reading is naturally done in LSB-first
;;; order, we simply convert the table's indices from their natural MSB-first
;;; form to LSB-first. This tradeoff seems worth it in practice.
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
;;; We store the (l,i) pair as (i << s) | l for some suitable constant `s'.
;;;
;;; In the end, table preprocessing makes up ~12% of the Deflate runtime, most
;;; of it for redundant entries of short codes. Since short codes are supposed
;;; to be frequent (assuming the encoder does its job correctly), this suggests
;;; that a hybrid approach may be better.
;;;
;;; For instance, one could use a lookup table for the first 12 bits (this
;;; roughly accounts for 95% of all codes). Indices that correspond to longer
;;; codes then resolve to a smaller second lookup table, where we repeat the
;;; process with the remaining bits. It's easy to just concatenate these smaller
;;; tables into one and resolve to an offset into the resulting array.
;;;
;;; I've actually tried this but decided it wasn't worth it; while it speeds up
;;; decompression by ~1.1x, the code becomes significantly messier. It might be
;;; worth reviving once the rest is faster or once we support other formats that
;;; require longer codes and create a large amount of Huffman trees.
(cl:in-package #:semz.decompress)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +huffman-max-codelen+ (max 15 20))
  (defconstant +huffman-max-item+ (max 287 257))
  (defconstant +huffman-shift+ (integer-length +huffman-max-codelen+)))

(deftype ht-codelen ()
  `(integer 0 ,+huffman-max-codelen+))

(deftype ht-codelen-vector ()
  '(simple-array ht-codelen (*)))

(deftype ht-item ()
  `(integer 0 ,+huffman-max-item+))

(deftype ht-entry ()
  `(unsigned-byte ,(+ +huffman-shift+ (integer-length +huffman-max-item+))))

(declaim (inline ht-table ht-min-codelen ht-max-codelen ht-full-read-p))
(defstruct (huffman-tree (:conc-name ht-))
  (table (required-argument :table) :type (simple-array ht-entry (*)))
  (min-codelen (required-argument :min-codelen)
   :type (integer 1 #.+huffman-max-codelen+))
  (max-codelen (required-argument :max-codelen)
   :type (integer 1 #.+huffman-max-codelen+))
  ;; If true, we can always safely read `max-codelen' bits at once to speed
  ;; up the decoding process, rather than having to go byte by byte.
  full-read-p)

(defmacro define-huffman-reader-function
    (function-name bit-reader-type prefix endianness)
  (with-prefixed-names (ensure-bits dump-bits peek-bits) prefix
    `(define-fast-inline-function (,function-name ht-item)
         ((br ,bit-reader-type) (ht huffman-tree))
       (macrolet ((with-entry ((index len) &body body)
                    (with-gensyms (entry)
                      `(let* ((,entry (aref (ht-table ht)
                                            ,(ecase ,endianness
                                               (:le index)
                                               (:be `(ash ,index (- max-codelen ,len))))))
                              (length (ldb (byte ,+huffman-shift+ 0) ,entry))
                              (item (ash ,entry ,(- +huffman-shift+))))
                         (declare (type (unsigned-byte ,+huffman-shift+) length)
                                  (type ht-entry item))
                         ,@body))))
         (let ((max-codelen (ht-max-codelen ht)))
           (if (ht-full-read-p ht)
               (progn
                 (,ensure-bits br max-codelen)
                 (with-entry ((,peek-bits br max-codelen) max-codelen)
                   (,dump-bits br length)
                   item))
               (loop :for ensured-len :from (ht-min-codelen ht) :to max-codelen
                     :do (,ensure-bits br ensured-len)
                         (with-entry ((,peek-bits br ensured-len) ensured-len)
                           (when (<= length ensured-len)
                             (,dump-bits br length)
                             (return item)))
                     :finally (error "Corrupt Huffman tree."))))))))

(define-huffman-reader-function ht-read-le-code lsb-bit-reader lbr- :le)
(define-huffman-reader-function ht-read-be-code msb-bit-reader mbr- :be)

(define-fast-inline-function (reverse-small-integer (unsigned-byte 16))
    ((x (unsigned-byte 16)) (n (integer 0 16)))
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
(defun lengths->ht (lengths max-overread-bits endianness
                    &key (start 0) (end (length lengths))
                    ;; If non-nil, write data into this existing HT instead.
                      ((:reuse-ht ht) nil))
  (declare (type ht-codelen-vector lengths)
           (type integer max-overread-bits)
           (type array-length start end))
  (assert (<= 1 (- end start) (+ 1 +huffman-max-item+)))
  (assert (or (eq endianness :le)
              (eq endianness :be)))
  (let* ((max-codelen
           (reduce #'max lengths :start start :end end :initial-value 1))
         (min-codelen
           (reduce #'min lengths :start start :end end :initial-value +huffman-max-codelen+
                                 :key (lambda (x)
                                        (declare (type ht-codelen x))
                                        (if (zerop x)
                                            +huffman-max-codelen+
                                            x))))
         (2^max (expt 2 max-codelen))
         ;; True about 2/3 of the time in practice when `max-overread-bits' = 0.
         (full-read-p (>= max-overread-bits (- max-codelen min-codelen))))
    (declare (type ht-codelen max-codelen min-codelen)
             (type (integer 0 #.(expt 2 +huffman-max-codelen+)) 2^max))
    ;; If codes are at most `n' bits long, then the fact that Huffman coding is
    ;; prefixless implies that each k-bit code will block the use of 2^(n-k)
    ;; n-bit codes. A length sequence determines a Huffman tree if and only if
    ;; exactly 2^n codes are made unusable in total; if less, then some codes
    ;; remain unassigned, and if more, some codes are can't have the prescribed
    ;; length (and would be ambiguous even when extended).
    (let ((unusable-codes (reduce #'+ lengths :start start :end end
                                              :key (lambda (len)
                                                     (declare (type ht-codelen len))
                                                     (if (zerop len)
                                                         0
                                                         (expt 2 (- max-codelen len)))))))
      ;; Very liberal bound, but trivial to prove correct.
      (declare (type (integer 0 #.(* (+ 1 +huffman-max-item+)
                                     (expt 2 (- +huffman-max-codelen+ 1))))
                     unusable-codes))
      (cond
        ((< unusable-codes 2^max) (die "Underfull Huffman tree."))
        ((> unusable-codes 2^max) (die "Overfull Huffman tree."))))
    (setf ht (or ht (make-huffman-tree :max-codelen max-codelen
                                       :min-codelen min-codelen
                                       :table (make-array 2^max :element-type 'ht-entry)
                                       :full-read-p full-read-p)))
    (check-type ht huffman-tree)
    ;; Especially smaller Deflate buffers don't use the maximum length of 15
    ;; bits, so allocating the table as needed makes decompression of many small
    ;; buffers noticeably faster. For large buffers, it amortizes.
    (let ((table (if (> 2^max (length (ht-table ht)))
                     (make-array 2^max :element-type 'ht-entry)
                     (ht-table ht)))
          ;; Next Huffman code to be assigned, represented as MSB of length
          ;; `len'. This can hit 2^n due to the final `incf'.
          (next-code 0))
      (declare (type (simple-array ht-entry (*)) table)
               (type (integer 0 #.(expt 2 +huffman-max-codelen+)) next-code)
               (optimize . #.*optimize-decls*))
      (loop :for len :from min-codelen :to max-codelen :do
        ;; Extend code to `len' bits. For the first code this is a no-op.
        (setf next-code (ash next-code 1))
        (loop :for src-index :from start :below end
              :for item :from 0 :to +huffman-max-item+ ; bound helps type inference
              :when (= len (aref lengths src-index)) :do
                ;; `item' is represented by the `len'-bit code stored MSB-first
                ;; in `next-code' now.
                (let ((entry (logior (ash item +huffman-shift+) len)))
                  ;; This loop takes up all the preprocessing time.
                  (if (eq endianness :le)
                      (loop :for i :from (reverse-small-integer next-code len)
                              :below 2^max :by (expt 2 len)
                            :do (setf (aref table i) entry))
                      (let ((unused-bits (- max-codelen len)))
                        (loop :for i :from (ash next-code unused-bits)
                                :below (ash (+ 1 next-code) unused-bits)
                              :do (setf (aref table i) entry)))))
                (incf next-code)))
      (setf (ht-max-codelen ht) max-codelen
            (ht-min-codelen ht) min-codelen
            (ht-table ht) table
            (ht-full-read-p ht) full-read-p)
      ht)))
