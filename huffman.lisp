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
  (defconstant +huffman-max-code-length+ (max 15 20))
  (defconstant +huffman-max-item+ (max 287 257))
  (defconstant +huffman-shift+ (integer-length +huffman-max-code-length+)))

(deftype dht-code-length ()
  `(integer 0 ,+huffman-max-code-length+))

(deftype dht-code-length-vector ()
  '(simple-array dht-code-length (*)))

(deftype dht-item ()
  `(integer 0 ,+huffman-max-item+))

(deftype dht-entry ()
  `(unsigned-byte ,(+ +huffman-shift+ (integer-length +huffman-max-item+))))

(declaim (inline dht-table dht-min-code-length dht-max-code-length dht-full-read-p))
(defstruct (deflate-huffman-tree (:conc-name dht-))
  (table (required-argument :table) :type (simple-array dht-entry (*)))
  (min-code-length (required-argument :min-code-length)
   :type (integer 1 #.+huffman-max-code-length+))
  (max-code-length (required-argument :max-code-length)
   :type (integer 1 #.+huffman-max-code-length+))
  ;; If true, we can always safely read `max-code-length' bits at once to speed
  ;; up the decoding process, rather than having to go byte by byte.
  full-read-p)

(defmacro define-huffman-reader-function
    (function-name bit-reader-type prefix endianness)
  (with-prefixed-names (ensure-bits dump-bits peek-bits) prefix
    `(define-fast-function (,function-name dht-item)
         ((br ,bit-reader-type) (dht deflate-huffman-tree))
       (macrolet ((with-entry ((index len) &body body)
                    (with-gensyms (entry)
                      `(let* ((,entry (aref (dht-table dht)
                                            ,(ecase ,endianness
                                               (:le index)
                                               (:be `(ash ,index (- max-code-length ,len))))))
                              (length (ldb (byte ,+huffman-shift+ 0) ,entry))
                              (item (ash ,entry ,(- +huffman-shift+))))
                         (declare (type (unsigned-byte ,+huffman-shift+) length)
                                  (type dht-entry item))
                         ,@body))))
         (let ((max-code-length (dht-max-code-length dht)))
           (if (dht-full-read-p dht)
               (progn
                 (,ensure-bits br max-code-length)
                 (with-entry ((,peek-bits br max-code-length) max-code-length)
                   (,dump-bits br length)
                   item))
               (loop :for ensured-len :from (dht-min-code-length dht) :to max-code-length
                     :do (,ensure-bits br ensured-len)
                         (with-entry ((,peek-bits br ensured-len) ensured-len)
                           (when (<= length ensured-len)
                             (,dump-bits br length)
                             (return item)))
                     :finally (error "Corrupt Huffman tree."))))))))

(define-huffman-reader-function dht-read-code lsb-bit-reader lbr- :le)
(define-huffman-reader-function bzip-read-code msb-bit-reader mbr- :be)

(define-fast-function (reverse-small-integer (unsigned-byte 16))
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
(defun lengths->dht (lengths max-overread-bits
                     &key (start 0) (end (length lengths))
                     ;; If non-nil, write data into this existing DHT instead.
                       ((:reuse-dht dht) nil)
                       (endianness :le))
  (declare (type dht-code-length-vector lengths)
           (type integer max-overread-bits)
           (type array-length start end)
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note)
           (optimize speed))
  (assert (<= 1 (- end start) (+ 1 +huffman-max-item+)))
  (assert (or (eq endianness :le)
              (eq endianness :be)))
  (let* ((max-code-length
           (reduce #'max lengths :start start :end end :initial-value 1))
         (min-code-length
           (reduce #'min lengths :start start :end end :initial-value +huffman-max-code-length+
                                 :key (lambda (x)
                                        (declare (type dht-code-length x))
                                        (if (zerop x)
                                            +huffman-max-code-length+
                                            x))))
         (2^max (expt 2 max-code-length))
         ;; True about 2/3 of the time in practice when `max-overread-bits' = 0.
         (full-read-p (>= max-overread-bits (- max-code-length min-code-length))))
    (declare (type dht-code-length max-code-length min-code-length)
             (type (integer 0 #.(expt 2 +huffman-max-code-length+)) 2^max))
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
      (declare (type (integer 0 #.(* (+ 1 +huffman-max-item+)
                                     (expt 2 (- +huffman-max-code-length+ 1))))
                     unusable-codes))
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
                     (dht-table dht)))
          ;; Next Huffman code to be assigned, represented as MSB of length
          ;; `len'. This can hit 2^n due to the final `incf'.
          (next-code 0))
      (declare (type (simple-array dht-entry (*)) table)
               (type (integer 0 #.(expt 2 +huffman-max-code-length+)) next-code)
               (optimize speed))
      (loop :for len :from min-code-length :to max-code-length :do
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
                      (let ((unused-bits (- max-code-length len)))
                        (loop :for i :from (ash next-code unused-bits)
                                :below (ash (+ 1 next-code) unused-bits)
                              :do (setf (aref table i) entry)))))
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
