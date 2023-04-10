;;;; Bit reading
;;;
;;; This is a set of pretty standard bit readers that consider a byte either as
;;; a LSB-first or MSB-first bitstream. The interface only supports reading
;;; numbers in the same endianness as the reader itself. Byte sources can be
;;; either byte streams or the `buffer-stream' from `io.lisp'.
;;;
;;; The obvious interface is `read-bits', but similar to the gzip reference
;;; implementation, a combination of `ensure-bits' and `dump-bits' can be used
;;; for higher performance, especially when you don't mind overreads and only
;;; have an upper bound for the needed number of bits, as is the case for our
;;; Huffman code reader.
(cl:in-package #:semz.decompress)

;;; Since bytes are read as needed, at least 8-1=7 extra bits might end up being
;;; buffered. The restriction on the number of bits read by `read-bits' is not
;;; essential and only exists for cheap optimization.
(defmacro define-bit-reader (type-name prefix max-ensure max-read endianness)
  (let ((max-buffer (+ max-ensure 8 -1)))
    (with-prefixed-names
        (source buffer bits-left
         ensure-bits peek-bits dump-bits read-bits
         flush-byte byte-source-usable-p)
        prefix
      `(progn
         (declaim (inline ,source ,buffer ,bits-left))
         (defstruct (,type-name (:conc-name ,prefix))
           (source (required-argument :source) :type byte-source)
           ;; Leftover bits are stored in the specified endianness; consumed
           ;; bits are always set to zero. The buffer always ends on a byte
           ;; boundary of the source because we only read full bytes.
           (buffer    0 :type (unsigned-byte ,max-buffer))
           (bits-left 0 :type (integer 0 ,max-buffer)))

         (define-fast-function ,ensure-bits
             ((br ,type-name) (n (integer 0 ,max-ensure)))
           "Ensures that at least `n' bits are buffered in `br'."
           (loop :while (< (,bits-left br) n)
                 :do ,(ecase endianness
                        (:le `(setf (ldb (byte 8 (,bits-left br)) (,buffer br))
                                    (bs-read-byte (,source br))))
                        (:be `(setf (,buffer br)
                                    (logior (ash (,buffer br) 8)
                                            (bs-read-byte (,source br))))))
                     (incf (,bits-left br) 8)))

         (define-fast-function (,peek-bits (unsigned-byte ,max-ensure))
             ((br ,type-name) (n (integer ,0 ,max-ensure)))
           ,(ecase endianness
              (:le `(ldb (byte n 0) (,buffer br)))
              (:be `(ash (,buffer br) (- (- (,bits-left br) n))))))

         (define-fast-function ,dump-bits
             ((br ,type-name) (n (integer ,0 ,max-ensure)))
           "Removes up to the next `n' bits from the buffer in `br'."
           (assert (>= (,bits-left br) n))
           (setf (,buffer br)
                 ,(ecase endianness
                    (:le `(ash (,buffer br) (- n)))
                    (:be `(ldb (byte (- (,bits-left br) n) 0) (,buffer br)))))
           (decf (,bits-left br) n))

         (define-fast-function (,read-bits (unsigned-byte ,max-read))
             ((br ,type-name) (n (integer 0 ,max-read)))
           "Returns and consumes the next `n' bits in `br'."
           (if (<= n ,max-ensure)
               ;; Fast path for decoders
               (progn
                 (,ensure-bits br n)
                 (prog1 (,peek-bits br n)
                   (,dump-bits br n)))
               (let ((result 0)
                     (result-length 0))
                 (declare (type (integer 0 ,max-read) result-length)
                          (type (unsigned-byte ,max-read) result))
                 (loop :while (< result-length n) :do
                   (let ((amount (min (- n result-length) ,max-ensure)))
                     (declare (type (integer 1 ,max-ensure) amount)
                              #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
                     (,ensure-bits br amount)
                     (setf result
                           ,(ecase endianness
                              (:le `(logior (ash (,peek-bits br amount) result-length)
                                            result))
                              (:be `(logior (,peek-bits br amount)
                                            (ash result amount)))))
                     (incf result-length amount)
                     (,dump-bits br amount)))
                 result)))

         (define-fast-function ,flush-byte ((br ,type-name))
           "Discards buffered bits in `br' before the next byte boundary. This function
does NOT guarantee that bytewise I/O will be usable afterwards."
           ;; The buffer ends on a byte boundary, so skipping to the next byte
           ;; boundary just means discarding bits until the remaining bits are a
           ;; multiple of 8.
           (let ((dropped (ldb (byte 3 0) (,bits-left br))))
             (declare (type (integer 0 7) dropped))
             (decf (,bits-left br) dropped)
             ,(ecase endianness
                (:le `(setf (,buffer br) (ash (,buffer br) (- dropped))))
                (:be `(setf (,buffer br) (ldb (byte (,bits-left br) 0) (,buffer br)))))
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
(define-bit-reader lsb-bit-reader lbr- 15 32 :le)

(define-bit-reader msb-bit-reader mbr- 20 48 :be)
