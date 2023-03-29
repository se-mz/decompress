;;;; Bit reading
;;;
;;; This is a pretty standard bit reader, although the declarations make it look
;;; messier than it is. It considers a byte as a LSB-first bitstream; thereforex
;;; reading little endian numbers is much faster than big endian numbers and the
;;; main interface is in little endian as well. Byte sources can be either byte
;;; streams or the `buffer-stream' from `io.lisp'.
;;;
;;; The obvious interface is `lbr-read-bits', but similar to the gzip reference
;;; implementation, a combination of `lbr-ensure-bits' and `lbr-dump-bits' can
;;; be used for higher performance, especially when you don't mind overreads and
;;; only have an upper bound for the needed number of bits, as is the case for
;;; our Huffman code reader.
(cl:in-package #:semz.decompress)

;;; We want to ensure/dump the longest Deflate Huffman codes, so `max-ensure'
;;; must be at least 15. Since bytes are read as needed, at least 8-1=7 extra
;;; bits might end up being buffered. The restriction on `lbr-read-bits' is not
;;; essential and only exists for cheap optimization.
(onetime-macrolet ((max-ensure 15)
                   (max-buffer (+ max-ensure 8 -1))
                   (max-read 32))
  ;; We rely on the fact that we can return to byte I/O after 32 bits.
  (assert (<= max-buffer 32))
  ;; We currently read up to 32 bits at a time.
  (assert (>= max-read 32))
  `(progn
     (declaim (inline lbr-source lbr-buffer lbr-bits-left))
     (defstruct (lsb-bit-reader (:conc-name lbr-))
       (source (required-argument :source) :type byte-source)
       ;; Leftover bits are stored LSB-first. The buffer always ends on a byte
       ;; boundary of the source because we only read full bytes.
       (buffer    0 :type (unsigned-byte ,max-buffer))
       (bits-left 0 :type (integer 0 ,max-buffer)))

     (define-fast-function lbr-ensure-bits
         ((lbr lsb-bit-reader) (n (integer 0 ,max-ensure)))
       "Ensures that at least `n' bits are buffered in `lbr'."
       (loop :while (< (lbr-bits-left lbr) n) :do
         (setf (ldb (byte 8 (lbr-bits-left lbr)) (lbr-buffer lbr))
               (bs-read-byte (lbr-source lbr)))
         (incf (lbr-bits-left lbr) 8)))

     (define-fast-function lbr-dump-bits
         ((lbr lsb-bit-reader) (n (integer ,0 ,max-ensure)))
       "Removes up to the next `n' bits from the buffer in `lbr'."
       (assert (>= (lbr-bits-left lbr) n))
       (setf (lbr-buffer lbr) (ash (lbr-buffer lbr) (- n)))
       (decf (lbr-bits-left lbr) n))

     (define-fast-function (lbr-read-bits (unsigned-byte ,max-read))
         ((lbr lsb-bit-reader) (n (integer 0 ,max-read)))
       "Returns and consumes the next `n' bits in `lbr'."
       (if (<= n ,max-ensure)
           ;; Fast path for decoders
           (progn
             (lbr-ensure-bits lbr n)
             (prog1 (ldb (byte n 0) (lbr-buffer lbr))
               (lbr-dump-bits lbr n)))
           (let ((result 0)
                 (result-length 0))
             (declare (type (integer 0 ,max-read) result-length)
                      (type (unsigned-byte ,max-read) result))
             (loop :while (< result-length n) :do
               (let ((amount (min (- n result-length) 15)))
                 (declare (type (integer 1 15) amount))
                 (lbr-ensure-bits lbr amount)
                 (setf (ldb (byte amount result-length) result)
                       (lbr-buffer lbr))
                 (incf result-length amount)
                 (lbr-dump-bits lbr amount)))
             result)))

     (define-fast-function lbr-flush-byte ((lbr lsb-bit-reader))
       "Discards buffered bits in `lbr' before the next byte boundary. This function
does NOT guarantee that bytewise I/O will be usable afterwards."
       ;; The buffer ends on a byte boundary, so skipping to the next byte boundary
       ;; just means discarding bits until the remaining bits are a multiple of 8.
       (let ((dropped (ldb (byte 3 0) (lbr-bits-left lbr))))
         (declare (type (integer 0 7) dropped))
         (decf (lbr-bits-left lbr) dropped)
         (setf (lbr-buffer lbr) (ash (lbr-buffer lbr) (- dropped)))
         nil))

     (define-fast-function lbr-byte-source-usable-p ((lbr lsb-bit-reader))
       ,(format nil
                "Returns whether the underlying byte source can be safely used. This can be
guaranteed by consuming at least ~d bits without an `lbr-ensure-bits' call."
                max-buffer)
       (zerop (lbr-bits-left lbr)))))
