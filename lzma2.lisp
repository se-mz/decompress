;;;; LZMA2
;;;
;;; LZMA2 is mostly a thin wrapper over LZMA that adds EOF handling,
;;; uncompressed blocks, flush points, and the ability to reset aspects of the
;;; LZMA state on the fly. It doesn't seem to have an actual specification; the
;;; LZMA spec only mentions how to parse the LZMA2 properties. I based this
;;; implementation on the one in XZ Utils for several reasons:
;;;
;;; 1. XZ Utils is significantly more readable than the LZMA SDK code.
;;;
;;; 2. The XZ Utils implementation is the stricter of the two and avoids certain
;;;    edge cases around LZMA-level EOF handling entirely.
;;;
;;; 3. The LZMA SDK code segfaulted on most of the edge cases I wanted to test.
(cl:in-package #:semz.decompress)

(defclass lzma2-state ()
  ((%source :initarg :source :accessor lz2s-source)
   (%control-state :initform :control-byte :accessor lz2s-control-state)
   (%needed-control :initform :dictionary :accessor lz2s-needed-control)

   (%lzma-state :initform nil :accessor lz2s-lzma-state)
   (%buffer :initform nil :initarg :buffer :accessor lz2s-buffer)
   (%buffer-i :initform 0 :initarg :buffer-i :accessor lz2s-buffer-i)
   (%dict-size :initarg :dict-size :accessor lz2s-dict-size)))

(defmethod initialize-instance :after ((state lzma2-state) &key)
  (when (null (lz2s-buffer state))
    (setf (lz2s-buffer state) (make-lzma-buffer (lz2s-dict-size state)))))

(defun parse-lzma2-props (octet)
  (let ((props (parse-lzma-props octet)))
    (when (> (+ (lzma-properties-lc props)
                (lzma-properties-lp props))
             4)
      (die "Property lc+lp out of bounds (0-4): ~d"
           (+ (lzma-properties-lc props) (lzma-properties-lp props))))
    props))

(defun parse-lzma2-dict-size (octet)
  (cond
    ((> octet 40) (die "Unrecognized LZMA2 dictionary size byte."))
    ((= octet 40) #xFFFFFFFF)
    ;; Results in 2<<11, 3<<11, 2<<12, 3<<12, ...
    (t (ash (logior 2 (logand octet 1))
            (+ 11 (floor octet 2))))))

;;; Quoth the C implementation in the LZMA SDK on the meaning of control bytes:
;;;
;;; 00000000  -  End of data
;;; 00000001 U U  -  Uncompressed, reset dic, need reset state and set new prop
;;; 00000010 U U  -  Uncompressed, no reset
;;; 100uuuuu U U P P  -  LZMA, no reset
;;; 101uuuuu U U P P  -  LZMA, reset state
;;; 110uuuuu U U P P S  -  LZMA, reset state + set new prop
;;; 111uuuuu U U P P S  -  LZMA, reset state + set new prop, reset dic
;;;
;;; where u/U are the decompressed size, P is the compressed size, and S is an
;;; LZMA2 property byte. Upper case letters are full bytes and multibyte numbers
;;; are in big-endian / MSB-first order. A size `n' is stored as n-1.
;;;
;;; By tracing through the XZ Utils implementation, we observe that there are
;;; essentially three states, depending on whether we require a full dictionary
;;; & LZMA state reset (D), new LZMA properties and an LZMA state reset (P) or
;;; no reset at all (N). A - marks an error state and an E marks the end of
;;; file. Control bytes 3 <= x <= #x7F are illegal.
;;;
;;; state \ byte | 0 | 1 | 2 | 100 | 101 | 110 | 110
;;; -------------+---+---+---+-----+-----+-----+-----
;;;      D       | E | P | - |  -  |  -  |  -  |  N
;;;      P       | E | P | P |  -  |  -  |  N  |  N
;;;      N       | E | P | N |  N  |  N  |  N  |  N
;;;
;;; XZ Utils supports preset dictionaries; if one is provided, the initial state
;;; is P rather than D. We don't support this at the moment.

(defmethod next-decompressed-chunk ((state lzma2-state))
  (with-accessors ((control-state lz2s-control-state)
                   (source lz2s-source)
                   (lzma-state lz2s-lzma-state)
                   (buffer lz2s-buffer)
                   (buffer-i lz2s-buffer-i)
                   (dict-size lz2s-dict-size)
                   (needed-control lz2s-needed-control))
      state
    (ecase control-state
      (:eof (error "LZMA2 state is already expired."))
      (:control-byte
       (let ((control (bs-read-byte source)))
         (cond
           ;; LZMA block
           ((>= control #b10000000)
            (let ((decompressed-size (+ 1 (dpb control (byte 5 16) (bs-read-be 2 source))))
                  (compressed-size (+ 1 (bs-read-be 2 source))))
              (setf control-state :lzma)

              (when (and (eq needed-control :dictionary) (< control #b11100000))
                (die "Didn't get required dictionary reset."))
              (when (and (eq needed-control :properties) (< control #b11000000))
                (die "Didn't get required property reset."))
              (setf needed-control nil)

              (let ((props (if (>= control #b11000000)
                               (parse-lzma2-props (bs-read-byte source))
                               ;; Only reachable if there was an old LZMA state
                               ;; by the preceding checks.
                               (lzs-properties lzma-state))))
                (let ((old-state lzma-state))
                  (when (>= control #b11100000)
                    (setf buffer-i 0))
                  (setf source (make-counted-byte-source
                                source
                                :limit compressed-size
                                :will-read-everything t
                                :on-eof (lambda ()
                                          (die "Embedded LZMA data goes beyond LZMA2 block size."))))
                  (setf lzma-state
                        (byte-source->decompression-state
                         :raw-lzma source
                         :lc (lzma-properties-lc props)
                         :lp (lzma-properties-lp props)
                         :pb (lzma-properties-pb props)
                         :window-size dict-size
                         :decompressed-size decompressed-size
                         ;; XZ's implementation explicitly bans LZMA-level EOF
                         ;; markers since LZMA2 does its own EOF handling. The
                         ;; LZMA SDK doesn't seem to do that, which raises
                         ;; questions about what to do when the LZMA EOF marker
                         ;; comes before the end of the LZMA data. When testing
                         ;; this, the SDK code kept segfaulting, and at some
                         ;; point I grew so sick of that thing that I stopped
                         ;; bothering with it.
                         :eof-mode :never
                         'buffer buffer
                         'buffer-i buffer-i))
                  ;; Recall that the `total-i-mod-16' field is considered to be
                  ;; a part of the dictionary state, not the LZMA state. Despite
                  ;; this, it can be reset together with the LZMA state: The
                  ;; prediction states for different values of `total-i-mod-16'
                  ;; do not overlap and are all 1/2 after a reset, so a
                  ;; different starting value of `total-i-mod-16' just amounts
                  ;; to shuffling prediction states around in memory. However,
                  ;; see the note for uncompressed blocks further below.
                  (when (< control #b10100000)
                    (setf (lzs-vars lzma-state) (lzs-vars old-state)))
                  (values +dummy-buffer+ 0 0 nil)))))

           ((> control 2)
            (die "Illegal LZMA2 control byte: ~2,'0x" control))

           ;; Uncompressed block
           ((>= control 1)
            (let ((decompressed-size (+ 1 (bs-read-be 2 source))))
              ;; Flush buffer if necessary so that we can fill in the data in
              ;; one go. `make-lzma-buffer' ensures that the buffer is always
              ;; large enough for this.
              (ecase control
                ((2)
                 (when (eq needed-control :dictionary)
                   (die "Didn't get required dictionary reset."))
                 (setf needed-control nil)
                 (unless (<= (+ buffer-i decompressed-size) (length buffer))
                   (setf buffer-i (flush-dict-buffer buffer buffer-i dict-size))))
                ((1)
                 (setf needed-control :properties)
                 (setf buffer-i 0)))

              (assert (<= (+ buffer-i decompressed-size) (length buffer)))
              (bs-read-sequence buffer source
                                :start buffer-i
                                :end (+ buffer-i decompressed-size)
                                :eof-error-p t)
              (incf buffer-i decompressed-size)

              ;; This update is necessary in case an LZMA block is followed by a
              ;; bunch of uncompressed blocks that don't reset the dictionary
              ;; and then an LZMA block that doesn't reset the LZMA state.
              ;; Base64'd .xz test file:
              ;;
              ;; /Td6WFoAAAD/EtlBAgAhAQoAAABTxyq54AAAAAUJACX//AAAAgAAT4AAAAAFACfRR0AAAAABKAM7StLkBnKeegEAAAAAAFla
              ;;
              ;; Decompresses to "LOL" if `total-i-mod-16' is advanced
              ;; correctly, and fails to decompress otherwise.
              (when lzma-state
                (setf (lzsv-total-i-mod-16 (lzs-vars lzma-state))
                      (mod (+ (lzsv-total-i-mod-16 (lzs-vars lzma-state))
                              decompressed-size)
                           16)))
              (values buffer (- buffer-i decompressed-size) buffer-i nil)))

           ;; EOF
           (t (setf control-state :eof)
              (values +dummy-buffer+ 0 0 t)))))

      (:lzma
       (multiple-value-bind (buf start end finalp)
           (next-decompressed-chunk lzma-state)
         (when finalp
           (setf control-state :control-byte)
           (unless (= (cbs-count source) (cbs-limit source))
             (die "Embedded LZMA data is shorter than declared."))
           (setf source (cbs-finish source)))
         (setf buffer-i end)
         (values buf start end nil))))))

(defmethod byte-source->decompression-state
    ((format (eql :raw-lzma2)) byte-source
     &key window-size
       ;; Same hack as for `lzma-state'.
       ((buffer buffer))
       ((buffer-i buffer-i) 0))
  (check-type window-size unsigned-byte)
  (setf window-size (min window-size (1- (expt 2 32))))
  (make-instance 'lzma2-state
                 :source byte-source
                 :dict-size window-size
                 :buffer buffer
                 :buffer-i buffer-i))

;; It would have been possible to use this format for XZ, but we parse filter
;; parameters separately in anticipation of support for other filters.
(defmethod byte-source->decompression-state ((format (eql :lzma2)) byte-source &key)
  (let ((result (byte-source->decompression-state
                 :raw-lzma2 byte-source
                 :dict-size (parse-lzma2-dict-size (bs-read-byte byte-source)))))
    (values result
            (list :window-size (lz2s-dict-size result)))))

(pushnew :raw-lzma2 *known-formats*)
(pushnew :lzma2 *known-formats*)
