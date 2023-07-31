;;;; LZMA - Lempel-Ziv-Markov (-Chain) Algorithm
;;;
;;; LZMA has a spec, but it's basically just a lightly commented refimpl, so we
;;; use the LZMA spec/refimpls from the LZMA SDK (https://7-zip.org/sdk.html)
;;; and XZ Utils' implementation (https://git.tukaani.org/?p=xz.git;a=summary).
;;;
;;; LZMA is very ad hoc and leaves little to the implementation. We try to
;;; describe the format throughout, but it's bound to be messy.
;;;
;;; Generally, LZMA is a slightly more sophisticated Lempel-Ziv underneath a
;;; layer of range encoding, i.e. it represents the data as a massive MSB-first
;;; integer and assigns output bits to specific subranges, based on a prediction
;;; of how likely that bit is going to occur. However, the devil is in the
;;; details and even the range encoding scheme is highly LZMA-specific.
(cl:in-package #:semz.decompress)

;;; Probabilities are specified as P(X = 0) = p/2048, where 0 <= p < 2048, and
;;; always begin at 1/2. After a bit is observed, the prediction is updated by
;;; multiplying the probability for the event that didn't happen by (1 - 2^-6),
;;; rounded towards its previous value. As a result of the rounding, we obtain
;;; tighter bounds 31 <= p <= 2017 (see code below); in particular, the range is
;;; symmetric and excluding p=2048 doesn't matter.
(let ((reachable (make-array 2048 :initial-element nil))
      (dirty     (make-array 2048 :initial-element nil)))
  (flet ((witness (p)
           (when (not (aref reachable p))
             (setf (aref dirty p) t))
           (setf (aref reachable p) t)))
    (witness 1024)
    (loop :for p = (position t dirty) :while p :do
      (witness (- p (ash p -5)))
      (witness (+ p (ash (- 2048 p) -5)))
      (setf (aref dirty p) nil)))
  (assert (equalp reachable (map 'vector (lambda (i) (<= 31 i 2017)) (iota 2048)))))

(deftype lzma-probability ()
  `(unsigned-byte 11))

(deftype lzma-probability-array ()
  `(simple-array lzma-probability (*)))

(defun make-lzma-probs (length)
  (make-array length :initial-element 1024 :element-type 'lzma-probability))

;;; The range decoding itself is pretty standard, but has to deal with rounding
;;; issues in some way; afaict there is no general principle behind the way LZMA
;;; does it beyond "this was easy to implement and fast". We implement it almost
;;; literally as in the spec, with one difference in `lrd-decode-fixed-bits'.
(declaim (inline lrd-code lrd-range lrd-source))
(defstruct (lzma-range-decoder (:conc-name lrd-))
  (code 0 :type (unsigned-byte 32))
  (range #xFFFFFFFF :type (unsigned-byte 32))
  (source (required-argument :source) :type byte-source))

(defun byte-source->lzma-range-decoder (bs)
  ;; "This simplifies the encoder logic" says the spec, and I'll believe it.
  (unless (zerop (bs-read-byte bs))
    (die "LZMA data doesn't begin with a zero octet."))
  (let ((lrd (make-lzma-range-decoder :range #xFFFFFFFF :code (bs-read-be 4 bs) :source bs)))
    (unless (< (lrd-code lrd) (lrd-range lrd))
      (die "Code starts out of range."))
    lrd))

(define-fast-inline-function lrd-normalize ((lrd lzma-range-decoder))
  ;; It is enough to read a single byte since only `lrd-decode-predicted-bit'
  ;; can lower `range'; see the comments in that function.
  (when (< (lrd-range lrd) (ash 1 24))
    (setf (lrd-range lrd) (ash (lrd-range lrd) 8)
          (lrd-code lrd) (logior (ash (lrd-code lrd) 8)
                                 (bs-read-byte (lrd-source lrd))))
    (unless (< (lrd-code lrd) (lrd-range lrd))
      (die "Code goes out of range."))))

;;; Reads a bit using a prediction state and then updates that state. This
;;; function makes up the core of LZMA and takes up some 40%-50% of total time.
;;; Note that XZ Utils normalizes before reading, rather than after reading,
;;; which afaict has no real effect except complicating the EOF handling. We
;;; stick to the refimpl's scheme of normalizing after reading.
(define-fast-inline-function (lrd-decode-predicted-bit bit)
    ((lrd lzma-range-decoder)
     (zero-prob-array lzma-probability-array)
     (index array-length))
  (let* ((zero-prob (aref zero-prob-array index))
         ;; Stays within 32 bits because zero-prob < 2^11; the lowest possible
         ;; value is 31 * 2^13. As a result, the lowest possible value for
         ;; `range' after updating is 31 * 2^13 = 2^18 - 2^13 >= 2^16, so a
         ;; single `lrd-normalize' call is enough to get above 2^24 again.
         (first-1-code (* zero-prob (ash (lrd-range lrd) -11))))
    (declare (type (unsigned-byte 32) first-1-code)
             (type lzma-probability zero-prob))
    (prog1 (if (>= (lrd-code lrd) first-1-code)
               (progn
                 (decf (lrd-range lrd) first-1-code)
                 (decf (lrd-code lrd) first-1-code)
                 (decf (aref zero-prob-array index)
                       (ash zero-prob -5))
                 1)
               (progn
                 (setf (lrd-range lrd) first-1-code)
                 (incf (aref zero-prob-array index)
                       (ash (- (ash 1 11) zero-prob) -5))
                 0))
      (lrd-normalize lrd))))

;;; When reading multiple bits at a time, we have a prediction state for each
;;; partial input, resulting in a total of 1 + 2 + 4 + ... + 2^(n-1) = 2^n - 1
;;; states. Padding with a dummy state at the begining simplifies addressing;
;;; the state for partial input xxxx is at index #b1xxxx.
(define-fast-inline-function (lrd-decode-predicted-be-bits (unsigned-byte 8))
    ((lrd lzma-range-decoder)
     (zero-prob-array lzma-probability-array)
     (index array-length)
     (count (integer 1 8)))
  ;; Similar to the refimpl, we abuse that `count' is encoded in the bit length
  ;; of the intermediate result to save a counter.
  (let ((bound (ash 1 count))
        (m 1))
    (declare (type (unsigned-byte 9) bound m))
    (loop :while (< m bound) :do
      (setf m (logior (lrd-decode-predicted-bit lrd zero-prob-array (+ index m))
                      (ash m 1))))
    (- m bound)))

;;; The refimpl implements this separately, but it makes little difference.
(define-fast-inline-function (lrd-decode-predicted-le-bits (unsigned-byte 5))
    ((lrd lzma-range-decoder)
     (zero-prob-array lzma-probability-array)
     (index array-length)
     (count (integer 1 5)))
  (reverse-small-integer
   (lrd-decode-predicted-be-bits lrd zero-prob-array index count)
   count))

;;; Certain rare bits do not get a prediction state; they're almost but not
;;; quite handled like bits with a predicted probability of 1/2. Note that in
;;; the refimpl code,
;;;
;;;   Range >>= 1;
;;;   Code -= Range;
;;;   UInt32 t = 0 - ((UInt32)Code >> 31);
;;;   Code += Range & t;
;;;
;;; is really just a branchless way to say
;;;
;;;   Range >>= 1;
;;;   if (Code >= Range)
;;;       Code -= Range;
;;;
;;; because the fact that Code < Range holds between reads implies that
;;;
;;;   |Code - (Range>>1)| <= Range/2 < 0x80000000,
;;;
;;; so that t = 0 if Code >= Range and t = 0xFFFFFFFF if Code < Range.
;;;
;;; The two major differences to `lrd-decode-predicted-bit' are that this
;;; version only rounds off one bit of `range' while the general version rounds
;;; off 11 to determine the bound, and that Range >>= 1 and Range -= Range >> 1
;;; are different operations in the case where Range is odd.
;;;
;;; We use the branching version because it's clearer and about the same speed.
(define-fast-inline-function (lrd-decode-fixed-bits (unsigned-byte 26))
    ((lrd lzma-range-decoder)
     (count (integer 1 26)))
  (let ((res 0))
    (declare (type (unsigned-byte 26) res))
    (loop :repeat count :do
      (let ((bound (ash (lrd-range lrd) -1)))
        (declare (type (unsigned-byte 31) bound))
        (setf (lrd-range lrd) bound)
        (if (>= (lrd-code lrd) bound)
            (progn
              (decf (lrd-code lrd) bound)
              ;; Can happen if `range' was odd and `code' = `range' - 1.
              (when (= (lrd-code lrd) bound)
                (die "Code goes out of range."))
              (setf res (logior (ash res 1) 1)))
            (setf res (ash res 1)))
        (lrd-normalize lrd)))
    res))

;;; The decoder has to end up in this state. Note however that this can also be
;;; a legitimate state representing a lot of zero bits, so you can't just check
;;; this condition over and over; you need another way to signal EOF.
(defun lrd-can-finish-p (lrd)
  (zerop (lrd-code lrd)))




;;;; The Lempel-Ziv part of LZMA
;;;
;;; Lengths in LZMA can be encoded in the following three forms:
;;;
;;; 0xxx - value of X + 2,
;;;
;;; 10yyy - value of Y + 8 + 2,
;;;
;;; 11zzzzzzzz - value of Z + 16 + 2,
;;;
;;; where the numbers X, Y, Z are the MSB-first interpretation of the bits x, y,
;;; z, respectively. Note that while this is always at least 2, it is possible
;;; to specify a length of 1 in a different way.
;;;
;;; The bits for X, Y, Z, as well as the two choice bits are all separately
;;; predicted. The bits for X and Y additionally depend on the least significant
;;; bits of the output position (the count is a parameter, 0 <= `pb' <= 4).
(declaim (inline lld-choices lld-low lld-mid lld-high))
(defstruct (lzma-length-decoder (:conc-name lld-))
  (choices (make-lzma-probs 2) :type lzma-probability-array)
  (low (map-into (make-array (ash 1 4))
                 (lambda ()
                   (make-lzma-probs (ash 1 3))))
   :type simple-vector)
  (mid (map-into (make-array (ash 1 4))
                 (lambda ()
                   (make-lzma-probs (ash 1 3))))
   :type simple-vector)
  (high (make-lzma-probs (ash 1 8)) :type lzma-probability-array))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +lzma-max-expansion-length+
    (+ 2 (- (max (+ 0 (expt 2 3))
                 (+ 8 (expt 2 3))
                 (+ 16 (expt 2 8)))
            1))))

;;; Since these lengths are at least 2, they're often represented as n-2.
(deftype lzma-raw-length ()
  `(integer 0 ,(- +lzma-max-expansion-length+ 2)))

(deftype lzma-length ()
  `(integer 1 ,+lzma-max-expansion-length+))

(define-fast-inline-function (decode-lzma-length lzma-raw-length)
    ((lld lzma-length-decoder)
     (lrd lzma-range-decoder)
     (output-alignment (unsigned-byte 4)))
  (cond
    ((zerop (lrd-decode-predicted-bit lrd (lld-choices lld) 0))
     (lrd-decode-predicted-be-bits lrd (aref (lld-low lld) output-alignment) 0 3))
    ((zerop (lrd-decode-predicted-bit lrd (lld-choices lld) 1))
     (+ 8 (lrd-decode-predicted-be-bits lrd (aref (lld-mid lld) output-alignment) 0 3)))
    (t
     (+ 16 (lrd-decode-predicted-be-bits lrd (lld-high lld) 0 8)))))

;;; Distances are classified by their "slot" - a 6-bit number encoding their bit
;;; length and two most significant bits. The slot is encoded MSB-first with its
;;; own prediction state, which depends on whether the length of the match is 2,
;;; 3, 4, or 5+. A distance `n' is represented by the code n-1; a distance of
;;; 2^32 (i.e. code #xFFFFFFFF) represents EOF.
;;;
;;; Distances are encoded like this:
;;;
;;; Slot | Distance - 1 (binary, MSB-first)
;;; -----+---------------------------------
;;; 0    | 0
;;; 1    | 1
;;; 2    | 10
;;; 3    | 11
;;; 4    | 10x
;;; 5    | 11x
;;; 6    | 10xx
;;; 7    | 11xx
;;; ...
;;; 13   | 11xxxxx
;;; 14   | 10yyzzzz
;;; 15   | 11yyzzzz
;;; 16   | 10yyyzzzz
;;; 17   | 11yyyzzzz
;;; ...
;;; 62   | 10yyyyyyyyyyyyyyyyyyyyyyyyyyzzzz (26 times y)
;;; 63   | 11yyyyyyyyyyyyyyyyyyyyyyyyyyzzzz
;;;
;;; The x-bits of each slot have separate prediction states and are encoded
;;; LSB-first; the y-bits are fixed and are encoded MSB-first; the z-bits are
;;; encoded LSB-first and share prediction states across all slots.
;;;
;;; The idea is that the bits of the common shorter distances get their own
;;; prediction states whereas only the alignment bits of the rare longer
;;; distances are worth predicting.
(declaim (inline ldd-slot ldd-mid ldd-alignment))
(defstruct (lzma-distance-decoder (:conc-name ldd-))
  (slot (map-into (make-array 4)
                  (lambda ()
                    (make-lzma-probs (ash 1 6))))
   :type simple-vector)
  ;; As in the refimpl, this is set up so that we can index the prediction
  ;; states for the x-bits via D - s, where 4 <= s <= 13 is a slot and `D' is
  ;; the smallest distance code that slot `s' can encode. A manual verification
  ;; shows that this causes no overlaps and requires 115 states:
  ;;
  ;; D           |  4  6  8 12 16 24 32 48 64  96
  ;; s           |  4  5  6  7  8  9 10 11 12  13
  ;; # x-bits    |  1  1  2  2  3  3  4  4  5   5
  ;; ------------+-------------------------------
  ;; index (D-s) |  0  1  2  5  8 15 22 37 52  83
  ;; first used  |  1  2  3  6  9 16 23 38 53  84
  ;; last used   |  1  2  5  8 15 22 37 52 83 114
  (mid (make-lzma-probs 115) :type lzma-probability-array)
  (alignment (make-lzma-probs (ash 1 4)) :type lzma-probability-array))

;;; The highest encodable distance code is #xFFFFFFFF, but that's used as an EOF
;;; marker. The next highest is #xFFFFFFFE, representing distance #xFFFFFFFF.
(deftype lzma-distance ()
  '(integer 1 #xFFFFFFFF))

(deftype lzma-distance-code ()
  '(integer 0 #xFFFFFFFF))

(define-fast-inline-function (decode-lzma-distance lzma-distance-code)
    ((lrd lzma-range-decoder)
     (ldd lzma-distance-decoder)
     (raw-len lzma-raw-length))
  (let* ((slot (lrd-decode-predicted-be-bits lrd (aref (ldd-slot ldd) (min raw-len 3)) 0 6)))
    (declare (type (unsigned-byte 6) slot))
    (if (< slot 4)
        slot
        (let* ((bit-count (- (ash slot -1) 1))
               ;; 1*00...0. Bit length is always `bit-count' + 2.
               (min-dist (ash (logior 2 (ldb (byte 1 0) slot)) bit-count)))
          (declare (type (integer 1 30) bit-count)
                   (type (unsigned-byte 32) min-dist))
          (if (< slot 14)
              (+ min-dist
                 (lrd-decode-predicted-le-bits lrd (ldd-mid ldd) (- min-dist slot) bit-count))
              (+ min-dist
                 (ash (lrd-decode-fixed-bits lrd (- bit-count 4)) 4)
                 (lrd-decode-predicted-le-bits lrd (ldd-alignment ldd) 0 4)))))))




;;;; Lempel-Ziv symbol types
;;;
;;; LZMA is parameterized over three numbers 0 <= `lc' <= 8, 0 <= `lp' <= 4 and
;;; 0 <= `pb' <= 4, usually called "properties", as well as a dictionary size.
;;; It admits the following 7 symbols, whose types are also predicted:
;;;
;;; - "Literal": An octet to output. Prediction depends on many factors, see
;;;   `lzma-properties->lzma-state-vars' for details. Notably depends on the
;;;   `lp' least significant bits of the output position.
;;;
;;; - "Simple match" / EOF: A typical (length,distance) pair; if the distance is
;;;   2^32, signifies EOF. Lengths and distances are both predicted based on the
;;;   `pb' least significant bits of the output position, similar to literals.
;;;   This is the only symbol that can introduce new distances.
;;;
;;; - "Short repetition": Stands for (1, most recently used distance). If this
;;;   is the first non-literal symbol, the distance is 1.
;;;
;;; - Four "long repetition" symbols rep0, rep1, rep2, rep3 that repeat multiple
;;;   octets at one of the four most recently used distances. The length is
;;;   encoded like it is for simple matches, but simple matches and long
;;;   repetitions have separate copies of the length prediction machinery.
;;;
;;; The symbols are respectively identified by the bit sequences 0, 10, 1100,
;;; 1101, 1110, 11110, 11111. Each branch split has its own separate prediction
;;; state, which depends on the types of the four most recent symbols. The bits
;;; that distinguish between literal/not-literal and simple match/short rep
;;; additionally use the `pb' least significant bits of the output position.
;;;
;;; Prediction of the symbol type is influenced by an abstract 12-state variable
;;; that influences symbol type decoding and literal decoding. It turns out to
;;; essentially track the last four symbol types. Starting at 0, the variable is
;;; updated as follows depending on the encountered symbol:
;;;
;;; type\state   | 0  1  2  3  4  5  6  7  8  9  10 11
;;; -------------+------------------------------------
;;; literal      | 0  0  0  0  1  2  3  4  5  6  4  5
;;; simple match | 7  7  7  7  7  7  7  10 10 10 10 10
;;; short rep    | 9  9  9  9  9  9  9  11 11 11 11 11
;;; long rep     | 8  8  8  8  8  8  8  11 11 11 11 11
;;;
;;; XZ Utils offers the following interpretation of these states:
;;;
;;;  0                 literal      -> literal (*)
;;;  1 simple match -> literal      -> literal
;;;  2 any rep      -> literal      -> literal (*)
;;;  3 short rep    -> literal      -> literal (*)
;;;  4                 simple match -> literal
;;;  5                 any rep      -> literal (*)
;;;  6                 short rep    -> literal (*)
;;;  7                 literal      -> simple match
;;;  8                 literal      -> long rep
;;;  9                 literal      -> short rep
;;; 10                 non-literal  -> simple match
;;; 11                 non-literal  -> any rep
;;;
;;; However, the (*) marked states have an incorrect description. It's actually:
;;;
;;;  0                 literal      -> literal      -> literal
;;;  1                 simple match -> literal      -> literal
;;;  2 non-literal  -> any rep      -> literal      -> literal
;;;    literal      -> long rep     -> literal      -> literal
;;;  3 literal      -> short rep    -> literal      -> literal
;;;  4                                 simple match -> literal
;;;  5                 non-literal  -> any rep      -> literal
;;;                    literal      -> long rep     -> literal
;;;  6                 literal      -> short rep    -> literal
;;;  7                                 literal      -> simple match
;;;  8                                 literal      -> long rep
;;;  9                                 literal      -> short rep
;;; 10                                 non-literal  -> simple match
;;; 11                                 non-literal  -> any rep
;;;
;;; Reeks of an implementation quirk/bug leaking into the spec.
(deftype lzma-symbol-history ()
  '(integer 0 11))

(defstruct lzma-properties
  (lc (required-argument :lc) :type (integer 0 8))
  (lp (required-argument :lp) :type (integer 0 4))
  (pb (required-argument :pb) :type (integer 0 4)))

(defstruct (lzma-state-vars (:conc-name lzsv-))
  (symbol-history 0 :type lzma-symbol-history)

  (literal-probs (required-argument :literal-probs) :type lzma-probability-array)

  ;; Prediction state for symbol types. We adjust the original names to
  ;; consistently refer to the predicate safisfied for a zero bit. Two of these
  ;; states can also rely on the output alignment.
  (is-literal (make-lzma-probs (ash 12 4)) :type lzma-probability-array)
  (is-simple-match (make-lzma-probs 12) :type lzma-probability-array)
  (uses-rep0 (make-lzma-probs 12) :type lzma-probability-array)
  (is-short-rep (make-lzma-probs (ash 12 4)) :type lzma-probability-array)
  (is-rep1 (make-lzma-probs 12) :type lzma-probability-array)
  (is-rep2 (make-lzma-probs 12) :type lzma-probability-array)

  (simple-len-decoder (make-lzma-length-decoder) :type lzma-length-decoder)
  (rep-len-decoder    (make-lzma-length-decoder) :type lzma-length-decoder)
  (dist-decoder (make-lzma-distance-decoder) :type lzma-distance-decoder)

  ;; These are distance codes because we store the EOF marker in them too, just
  ;; like the refimpl. Whether this is necessary is hard to say - LZMA2 can
  ;; reuse the old LZMA state, but our current implementation of LZMA2 (based on
  ;; XZ Utils) does not allow EOF markers in underlying LZMA data anyway.
  (rep0 0 :type lzma-distance-code)
  (rep1 0 :type lzma-distance-code)
  (rep2 0 :type lzma-distance-code)
  (rep3 0 :type lzma-distance-code)

  ;; Keeps track of the output alignment. Since `lp' and `pb' are at most 4,
  ;; four bits suffice. Note that in LZMA and LZMA2, this variable is considered
  ;; part of the _dictionary_ state, not the LZMA state; this has no effects on
  ;; our implementation of LZMA, but creates an edge case for LZMA2.
  (total-i-mod-16 0 :type (unsigned-byte 4)))

;;; Predictions of literals depend on the following data:
;;;
;;; - The `lp' least significant bits of the output position (alignment info).
;;;
;;; - The `lc' most significant bits of the previous output byte (or zero if
;;;   there is none). These often correlate, e.g. in text.
;;;
;;; - Which one of the following three conditions is true:
;;;
;;;   - The previous symbol was either a literal, or it was a match and the most
;;;     significant bits of the first byte of that match do not agree with the
;;;     bits we have read so far.
;;;
;;;   - The previous symbol was a match, the most significant bits of its first
;;;     byte agree with the bits we have read so far, and the next bit of that
;;;     match byte is zero.
;;;
;;;   - The previous symbol was a match, the most significant bits of its first
;;;     byte agree with the bits we have read so far, and the next bit of that
;;;     match byte is one.
;;;
;;;   I would guess that this deals with data that contains repetitive segments
;;;   with slightly changing prefixes/suffixes, like 0001, 0002, 0003, ...; the
;;;   back-off logic should prevent expensive mispredictions.
;;;
;;; - The bits we have read so far, as usual for multi-bit values. As before, we
;;;   pad with a dummy state.
;;;
;;; Our addressing scheme, taken from the refimpl, goes from most significant to
;;; least significant in the above order.
(defun lzma-properties->lzma-state-vars (props)
  (make-lzma-state-vars :literal-probs (make-lzma-probs (* (ash 1 (lzma-properties-lp props))
                                                           (ash 1 (lzma-properties-lc props))
                                                           3 #x100))))

(define-fast-inline-function (decode-lzma-literal/match-case octet)
    ((lrd lzma-range-decoder)
     (probs lzma-probability-array)
     (base-index array-length)
     (match-byte octet))
  (let ((match-offset (+ base-index #x100))
        (symbol 1))
    (declare (type array-length match-offset)
             (type (unsigned-byte 9) symbol))
    (loop :for bit-i :from 7 :downto 0 :do
      (let* ((match-bit (ldb (byte 1 bit-i) match-byte))
             (bit (lrd-decode-predicted-bit
                   lrd probs
                   (+ match-offset (ash match-bit 8) symbol))))
        (declare (type bit match-bit bit))
        (setf symbol (logior (ash symbol 1) bit))
        (when (/= match-bit bit)
          (return))))
    (loop :until (>= symbol #x100) :do
      (setf symbol (logior (ash symbol 1)
                           (lrd-decode-predicted-bit lrd probs (+ base-index symbol)))))
    (logand #xFF symbol)))

;;; We need to track the total output size to deal with LZMA's EOF modes:
;;;
;;; 1. The decompressed size is unknown and EOF is determined by a marker.
;;;
;;; 2. The decompressed size is known and an EOF marker is mandatory.
;;;
;;; 3. The decompressed size is known and an EOF marker is not mandatory, but
;;;    may appear anyway.
;;;
;;; 4. The decompressed size is known and an EOF marker is illegal. (required by
;;;    XZ Utils)
;;;
;;; Adjust the fill threshold so that even a maximal length match cannot fill up
;;; the entire buffer. Now define P as follows:
;;;
;;; - If the decompressed size is unknown, let P be the end of the buffer.
;;;
;;; - If the decompressed size is known and the expected remaining data cannot
;;;   fit into the buffer, let P be the end of the buffer.
;;;
;;; - If the decompressed size is known and the expected remaining data can fit
;;;   into the buffer, let P be the output position we'd be in after all that
;;;   data was written to the buffer.
;;;
;;; Since the fill threshold is set up so that we cannot fill up the full
;;; buffer, the declared end is reached if and only if we reach P, so it now
;;; suffices to check the output position against P; both of these are array
;;; lengths, so we only need fixnum arithmetic in the hot path.
(defun lzma-max-buffer-i (length current-i total)
  (if total
      (min length (+ current-i total))
      length))

(defun lzma-fill-threshold (length)
  (- length
     (max
      ;; Ensures that expansions need not be interrupted.
      +lzma-max-expansion-length+
      ;; Ensures that `total-i' in `decode-lzma' always stays an `array-length'
      ;; since it can start at 15 and go across the entire buffer. Irrelevant in
      ;; practice since the expansion length is higher.
      15)
     ;; Ensures that we can distinguish early EOF from a full buffer even if the
     ;; largest possible match fills up the buffer perfectly.
     1))

(define-fast-function decode-lzma
    ((lrd lzma-range-decoder)
     (props lzma-properties)
     (vars lzma-state-vars)
     (dict-size (unsigned-byte 32))
     (buffer buffer)
     (buffer-i array-length)
     ;; The variable P described above.
     (max-buffer-i array-length)
     ;; When size is known: `always', `never' or `maybe' have an EOF marker.
     ;; Ignored when size is unknown since that always needs an EOF marker.
     (eof-mode (member :always :never :maybe)))
  (let* ((rep0 (lzsv-rep0 vars))
         (rep1 (lzsv-rep1 vars))
         (rep2 (lzsv-rep2 vars))
         (rep3 (lzsv-rep3 vars))
         (symbol-history (lzsv-symbol-history vars))
         ;; We only need the lowest max(pb,lp) <= 4 bits.
         (total-i (lzsv-total-i-mod-16 vars))
         (threshold (lzma-fill-threshold (length buffer)))

         (lc (lzma-properties-lc props))
         (lp-mask (- (ash 1 (lzma-properties-lp props)) 1))
         (pb-mask (- (ash 1 (lzma-properties-pb props)) 1))

         (eofp nil))
    (declare (type lzma-distance-code rep0 rep1 rep2 rep3)
             (type lzma-symbol-history symbol-history)
             ;; We only reduce `total-i' at the end; the fill threshold is
             ;; chosen so that even the largest dictionaries cannot cause
             ;; `total-i' to violate its `array-length' type.
             (type array-length total-i threshold)
             (type (integer 0 8) lc)
             (type (unsigned-byte 4) lp-mask pb-mask))
    (labels ((handle-match (length distance)
               (declare (type lzma-distance distance)
                        (type lzma-length length)
                        (optimize . #.*optimize-decls*))
               (unless (<= distance dict-size)
                 (die "Match extends beyond dictionary size."))
               (unless (<= distance buffer-i)
                 (die "Match extends beyond available data."))
               (unless (<= buffer-i (- max-buffer-i length))
                 (die "Match extends beyond declared decompressed size."))
               (copy-match buffer (- buffer-i distance) buffer-i length)
               (incf buffer-i length)
               (incf total-i length))

             (update-history/literal ()
               (setf symbol-history (svref #(0 0 0 0 1 2 3 4 5 6 4 5) symbol-history)))
             (update-history/simple-match ()
               (setf symbol-history (if (< symbol-history 7) 7 10)))
             (update-history/long-rep ()
               (setf symbol-history (if (< symbol-history 7) 8 11)))
             (update-history/short-rep ()
               (setf symbol-history (if (< symbol-history 7) 9 11)))

             (probe-eof ()
               (let ((pos-state (logand total-i pb-mask)))
                 (and (= 1 (lrd-decode-predicted-bit lrd (lzsv-is-literal vars)
                                                     (logior (ash symbol-history 4) pos-state)))
                      (zerop (lrd-decode-predicted-bit lrd (lzsv-is-simple-match vars)
                                                       symbol-history))
                      (let ((len (decode-lzma-length (lzsv-simple-len-decoder vars)
                                                     lrd pos-state)))
                        ;; This is necessary in case LZMA2 allows LZMA-level EOF
                        ;; markers and reuses our state. Right now our LZMA2
                        ;; implementation doesn't allow that anyway, but I don't
                        ;; want to have to fix this once it does.
                        (update-history/simple-match)
                        (shiftf rep3 rep2 rep1 rep0
                                (decode-lzma-distance lrd (lzsv-dist-decoder vars) len))
                        (= #xFFFFFFFF rep0)))))

             (handle-eof-insanity ()
               (ecase eof-mode
                 (:always (or (probe-eof)
                              (die "Didn't find mandatory EOF marker in LZMA data.")))
                 (:never (or (lrd-can-finish-p lrd)
                             (if (probe-eof)
                                 (die "Illegal EOF marker in LZMA data.")
                                 (die "LZMA data continues beyond declared size."))))
                 ;; The range decoder can accidentally end up in an all-zeroes
                 ;; state even if EOF is not reached yet; however, the resulting
                 ;; symbol would be a zero literal, not an EOF marker, so the
                 ;; stream would necessarily have to be corrupt. Hence there is
                 ;; no ambiguity here. If this doesn't satisfy you, consider
                 ;; that XZ Utils finishes early in this case as well:
                 ;;
                 ;; https://git.tukaani.org/?p=xz.git;a=blob;f=src/liblzma/lzma/lzma_decoder.c;h=26c148a95e259e46f256f1425fb3c417a281ee4a;hb=HEAD#l360
                 (:maybe
                  (or (lrd-can-finish-p lrd)
                      (probe-eof)
                      (die "Neither range decoder nor marker denote an end.")))))

             (decode-literal ()
               (declare (optimize . #.*optimize-decls*))
               (let* ((literal-probs (lzsv-literal-probs vars))
                      (previous-byte (if (zerop buffer-i)
                                         0
                                         (aref buffer (- buffer-i 1))))
                      (base-index
                        (* (logior (ash (logand total-i lp-mask) lc)
                                   (ash previous-byte (- (- 8 lc))))
                           3 #x100)))
                 (declare (type lzma-probability-array literal-probs)
                          (type octet previous-byte)
                          (type array-length base-index))
                 (if (< symbol-history 7) ;; last symbol was a literal
                     (lrd-decode-predicted-be-bits lrd literal-probs base-index 8)
                     (decode-lzma-literal/match-case
                      lrd literal-probs base-index
                      ;; The assertion below cannot fail normally since this
                      ;; branch cannot be taken for the first symbol and
                      ;; non-zero distances must be used in a simple match
                      ;; before they end up in `rep0'. While LZMA2 allows you to
                      ;; transplant prediction states and reset dictionaries,
                      ;; you cannot reset the dictionary without resetting the
                      ;; state. Hence this assertion only protects against
                      ;; programmer error.
                      (progn
                        (assert (<= 0 (- buffer-i (+ 1 rep0))))
                        (aref buffer (- buffer-i (+ 1 rep0)))))))))
      (declare (ftype (function (lzma-length lzma-distance)) handle-match)
               (ftype (function () octet) decode-literal)
               (inline update-history/literal update-history/simple-match
                       update-history/short-rep update-history/long-rep
                       handle-match decode-literal))
      (assert (< dict-size threshold (length buffer)))
      (loop
        (unless (< buffer-i threshold)
          (return))
        ;; Since `threshold' is strictly smaller than the buffer length, this
        ;; check can only be reached if `max-buffer-i' is smaller than the
        ;; buffer length, i.e. when there is a declared decompressed size.
        (when (= buffer-i max-buffer-i)
          ;; XZ Utils performs a normalization here (and before reading an EOF)
          ;; because its LRD gets normalized _before_ updating the LRD state. We
          ;; normalize after updating, so this is not necessary for us.
          (handle-eof-insanity)
          (setf eofp t)
          (return))
        (let ((pos-state (logand total-i pb-mask)))
          (declare (type (unsigned-byte 4) pos-state))
          (cond
            ;; 0 - literal
            ((zerop (lrd-decode-predicted-bit
                     lrd (lzsv-is-literal vars) (logior (ash symbol-history 4) pos-state)))
             (setf (aref buffer buffer-i) (decode-literal))
             (incf buffer-i)
             (incf total-i)
             (unless (<= buffer-i max-buffer-i)
               (die "Decompressed data goes beyond declared size."))
             (update-history/literal))

            ;; 10 - simple match or EOF
            ((zerop (lrd-decode-predicted-bit lrd (lzsv-is-simple-match vars) symbol-history))
             (let ((len (decode-lzma-length (lzsv-simple-len-decoder vars) lrd pos-state)))
               (declare (type lzma-raw-length len))
               (update-history/simple-match)
               (shiftf rep3 rep2 rep1 rep0 (decode-lzma-distance lrd (lzsv-dist-decoder vars) len))
               (when (= #xFFFFFFFF rep0)
                 ;; As mentioned above, XZ Utils normalizes here; we need not.
                 (when (eq eof-mode :never)
                   (die "Illegal EOF marker in LZMA data."))
                 (setf eofp t)
                 (return))
               (handle-match (+ 2 len) (+ 1 rep0))))

            ;; 11* - rep match
            (t
             (handle-match
              (if (zerop (lrd-decode-predicted-bit lrd (lzsv-uses-rep0 vars) symbol-history))
                  ;; 110* - distance is rep0
                  (if (zerop (lrd-decode-predicted-bit lrd (lzsv-is-short-rep vars)
                                                       (logior (ash symbol-history 4) pos-state)))
                      ;; 1100 - short rep match
                      (progn
                        (update-history/short-rep)
                        1)
                      ;; 1101 - rep match 0
                      (progn
                        (update-history/long-rep)
                        (+ 2 (decode-lzma-length (lzsv-rep-len-decoder vars) lrd pos-state))))
                  ;; 111* - rep match 1/2/3
                  (progn
                    (cond
                      ;; 1110 - rep1
                      ((zerop (lrd-decode-predicted-bit lrd (lzsv-is-rep1 vars) symbol-history))
                       (rotatef rep1 rep0))
                      ;; 11110 - rep2
                      ((zerop (lrd-decode-predicted-bit lrd (lzsv-is-rep2 vars) symbol-history))
                       (rotatef rep2 rep1 rep0))
                      ;; 11111 - rep3
                      (t (rotatef rep3 rep2 rep1 rep0)))
                    (update-history/long-rep)
                    (+ 2 (decode-lzma-length (lzsv-rep-len-decoder vars)
                                             lrd pos-state))))
              ;; `rep0' is always the relevant distance after the above code.
              (+ rep0 1))))))
      (setf (lzsv-rep0 vars) rep0
            (lzsv-rep1 vars) rep1
            (lzsv-rep2 vars) rep2
            (lzsv-rep3 vars) rep3
            (lzsv-symbol-history vars) symbol-history
            (lzsv-total-i-mod-16 vars) (mod total-i 16))
      (when eofp
        (unless (lrd-can-finish-p lrd)
          (die "Range decoder finishes in invalid state.")))
      (values buffer-i eofp))))




;;;; General interface

(defclass lzma-state ()
  ((%lrd :initarg :lrd :accessor lzs-lrd)
   (%properties :initarg :properties :accessor lzs-properties)
   (%vars :initarg :vars :accessor lzs-vars)
   (%buffer :initform nil :initarg :buffer :accessor lzs-buffer)
   (%buffer-i :initform 0 :initarg :buffer-i :accessor lzs-buffer-i)

   (%dict-size :initarg :dict-size :accessor lzs-dict-size)
   (%eof-mode :initarg :eof-mode :accessor lzs-eof-mode)
   ;; Used to handle decompressed size declarations; nil if no expectation.
   (%expected-remaining-data :initarg :expected-remaining-data
                             :accessor lzs-expected-remaining-data)))

;;; This function is also used by LZMA2. It could probably be handled more
;;; cleanly, maybe once the Lempel-Ziv stuff is factored out. The `max' call
;;; ensures that LZMA2 stored blocks need not be interruptible. The +1 is there
;;; to prevent false positives during EOF detection.
(defun make-lzma-buffer (dict-size)
  (make-array (max (+ dict-size (expt 2 16) 1)
                   (* 2 dict-size))
              :element-type 'octet))

(defmethod initialize-instance :after ((state lzma-state) &key &allow-other-keys)
  (when (null (lzs-buffer state))
    (setf (lzs-buffer state) (make-lzma-buffer (lzs-dict-size state))))
  (assert (< -1 (lzs-buffer-i state) (length (lzs-buffer state)))))

(defmethod byte-source->decompression-state
    ((format (eql :raw-lzma)) byte-source
     &key lc lp pb window-size decompressed-size eof-mode
       ;; Hack options that allow reusing the (potentially very large)
       ;; dictionary buffers when using embedded LZMA in e.g. XZ. Uses internal
       ;; symbols since options to `make-decompression-stream' are forwarded to
       ;; this function.
       ((buffer buffer))
       ((buffer-i buffer-i) 0))
  (check-type lc (integer 0 8))
  (check-type lp (integer 0 4))
  (check-type pb (integer 0 4))
  (check-type window-size unsigned-byte)
  (setf window-size (min window-size (1- (expt 2 32))))
  (check-type decompressed-size (or null unsigned-byte))
  (setf eof-mode (or eof-mode :maybe))
  (check-type eof-mode (member :always :never :maybe))
  (make-instance 'lzma-state
                 :lrd (byte-source->lzma-range-decoder byte-source)
                 :properties (make-lzma-properties :lc lc :lp lp :pb pb)
                 :buffer buffer
                 :buffer-i buffer-i
                 :dict-size window-size
                 :expected-remaining-data decompressed-size
                 :eof-mode eof-mode
                 :vars (lzma-properties->lzma-state-vars
                        (make-lzma-properties :lc lc :lp lp :pb pb))))

(defun parse-lzma-props (octet)
  (let ((lc (mod octet 9))
        (lp (mod (floor octet 9) 5))
        (pb (floor octet (* 9 5))))
    (unless (<= 0 pb 4)
      (die "Property `pb' is out of bounds (0-4): ~d" pb))
    (make-lzma-properties :lc lc :lp lp :pb pb)))

(defmethod byte-source->decompression-state ((format (eql :lzma)) byte-source &key)
  (let* ((props (parse-lzma-props (bs-read-byte byte-source)))
         (dict-size (bs-read-le 4 byte-source))
         (decompressed-size (bs-read-le 8 byte-source)))
    (when (= decompressed-size (- (expt 2 64) 1))
      (setf decompressed-size nil))
    (let ((result (byte-source->decompression-state
                   :raw-lzma byte-source
                   :lc (lzma-properties-lc props)
                   :lp (lzma-properties-lp props)
                   :pb (lzma-properties-pb props)
                   :window-size dict-size
                   :expected-remaining-data decompressed-size
                   ;; See commit 9595a3119b9faf0ce01375329cad8bbf85c35ea2 in XZ Utils.
                   :eof-mode :maybe)))
      (values result
              (list :lc (lzma-properties-lc props)
                    :lp (lzma-properties-lp props)
                    :pb (lzma-properties-pb props)
                    :window-size dict-size
                    :decompressed-size decompressed-size)))))

(defmethod next-decompressed-chunk ((state lzma-state))
  (let ((old-buffer-i (lzs-buffer-i state))
        (buffer (lzs-buffer state))
        (dict-size (lzs-dict-size state)))
    ;; Embedded LZMA often will not fill the entire dictionary, so we should
    ;; only flush when it's really necessary.
    (unless (< old-buffer-i (lzma-fill-threshold (length buffer)))
      ;; Ensure there's going to be at least some progress
      (assert (> (lzma-fill-threshold (length buffer)) dict-size))
      (setf (lzs-buffer-i state)
            (flush-dict-buffer (lzs-buffer state) (lzs-buffer-i state) (lzs-dict-size state)))
      (setf old-buffer-i dict-size))

    (multiple-value-bind (new-buffer-i eofp)
        (decode-lzma (lzs-lrd state) (lzs-properties state) (lzs-vars state) dict-size
                     buffer old-buffer-i
                     (lzma-max-buffer-i (length buffer)
                                        old-buffer-i
                                        (lzs-expected-remaining-data state))
                     (lzs-eof-mode state))
      (when (lzs-expected-remaining-data state)
        (decf (lzs-expected-remaining-data state) (- new-buffer-i old-buffer-i)))
      (setf (lzs-buffer-i state) new-buffer-i)
      ;; This branch can be reached when there's an early EOF marker.
      (when (and eofp
                 (lzs-expected-remaining-data state)
                 (not (zerop (lzs-expected-remaining-data state))))
        (die "Decompressed data ends before declared size."))
      (values buffer old-buffer-i new-buffer-i eofp))))

(pushnew :raw-lzma *known-formats*)
(pushnew :lzma *known-formats*)
