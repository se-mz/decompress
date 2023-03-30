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

;;; Since bytes are read as needed, at least 8-1=7 extra bits might end up being
;;; buffered. The restriction on the number of bits read by `read-bits' is not
;;; essential and only exists for cheap optimization.
(defmacro define-bit-reader (type-name prefix max-ensure max-read)
  (let ((max-buffer (+ max-ensure 8 -1)))
    (with-prefixed-names
        (source buffer bits-left ensure-bits dump-bits read-bits flush-byte byte-source-usable-p)
        prefix
      `(progn
         (declaim (inline ,source ,buffer ,bits-left))
         (defstruct (,type-name (:conc-name ,prefix))
           (source (required-argument :source) :type byte-source)
           ;; Leftover bits are stored LSB-first. The buffer always ends on a byte
           ;; boundary of the source because we only read full bytes.
           (buffer    0 :type (unsigned-byte ,max-buffer))
           (bits-left 0 :type (integer 0 ,max-buffer)))

         (define-fast-function ,ensure-bits
             ((br ,type-name) (n (integer 0 ,max-ensure)))
           "Ensures that at least `n' bits are buffered in `br'."
           (loop :while (< (,bits-left br) n) :do
             (setf (ldb (byte 8 (,bits-left br)) (,buffer br))
                   (bs-read-byte (,source br)))
             (incf (,bits-left br) 8)))

         (define-fast-function ,dump-bits
             ((br ,type-name) (n (integer ,0 ,max-ensure)))
           "Removes up to the next `n' bits from the buffer in `br'."
           (assert (>= (,bits-left br) n))
           (setf (,buffer br) (ash (,buffer br) (- n)))
           (decf (,bits-left br) n))

         (define-fast-function (,read-bits (unsigned-byte ,max-read))
             ((br ,type-name) (n (integer 0 ,max-read)))
           "Returns and consumes the next `n' bits in `br'."
           (if (<= n ,max-ensure)
               ;; Fast path for decoders
               (progn
                 (,ensure-bits br n)
                 (prog1 (ldb (byte n 0) (,buffer br))
                   (,dump-bits br n)))
               (let ((result 0)
                     (result-length 0))
                 (declare (type (integer 0 ,max-read) result-length)
                          (type (unsigned-byte ,max-read) result))
                 (loop :while (< result-length n) :do
                   (let ((amount (min (- n result-length) ,max-ensure)))
                     (declare (type (integer 1 ,max-ensure) amount))
                     (,ensure-bits br amount)
                     (setf (ldb (byte amount result-length) result)
                           (,buffer br))
                     (incf result-length amount)
                     (,dump-bits br amount)))
                 result)))

         (define-fast-function ,flush-byte ((br ,type-name))
           "Discards buffered bits in `br' before the next byte boundary. This function
does NOT guarantee that bytewise I/O will be usable afterwards."
           ;; The buffer ends on a byte boundary, so skipping to the next byte boundary
           ;; just means discarding bits until the remaining bits are a multiple of 8.
           (let ((dropped (ldb (byte 3 0) (,bits-left br))))
             (declare (type (integer 0 7) dropped))
             (decf (,bits-left br) dropped)
             (setf (,buffer br) (ash (,buffer br) (- dropped)))
             nil))

         (define-fast-function ,byte-source-usable-p ((br ,type-name))
           ,(format nil
                    "Returns whether the underlying byte source can be safely used. This can be
guaranteed by consuming at least ~d bits without a call to `~(~a~)ensure-bits'."
                    max-buffer prefix)
           (zerop (,bits-left br)))))))

;;; We want to ensure/dump the longest Deflate Huffman codes, so `max-ensure'
;;; must be at least 15. We rely on the fact that we can return to byte I/O
;;; after 32 bits and use the bit reader on up to 32 bits at a time.
(define-bit-reader lsb-bit-reader lbr- 15 32)
