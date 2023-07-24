;;;; SHA-256
;;;
;;; Implemented right off RFC 6234 with no major tricks because SHA-256 in XZ
;;; archives is super rare and known to be slow. Ironclad's implementation is
;;; roughly 1.7x faster, probably because it avoids our excessive `shiftf' use
;;; and unrolls aggressively. Unlike for the other checksums, (safety 0) doesn't
;;; do much here.
(cl:in-package #:semz.decompress)

(defstruct sha-256-state
  ;; The eight registers A, B, C, D, E, F, G, H, in order.
  (regs (map-into (make-array 8 :element-type '(unsigned-byte 32))
                  #'identity +sha-256-init+)
   :type (simple-array (unsigned-byte 32) (8)))
  ;; Total bit(!) length. Must be tracked to append it at the end.
  (bit-length 0 :type unsigned-byte)
  ;; SHA-256 works blockwise and our input might not always fill entire blocks
  ;; at a time, so we store incomplete blocks between calls to `update-sha-256'.
  (block (make-array 64 :element-type 'octet)
   :type (simple-array octet (64)))
  (block-index 0 :type (integer 0 64)))

(defun start-sha-256 ()
  (make-sha-256-state))

;; The message schedule array is passed for reuse between blocks; maybe silly.
(defun handle-sha-256-block (buffer start regs schedule)
  (declare (type buffer buffer)
           (type array-length start)
           (type (simple-array (unsigned-byte 32) (8)) regs)
           (type (simple-array (unsigned-byte 32) (64)) schedule)
           (optimize speed))
  (let ((t1 0)
        . #.(loop :for var :in '(a b c d e f g h)
                  :for index :from 0
                  :collect `(,var (aref regs ,index))))
    (declare (type (unsigned-byte 32) a b c d e f g h t1))
    (macrolet ((with-ub32-funcs (defs &body body)
                 "Like `labels', but declares functions as inline and taking /
returning (unsigned-byte 32) by default. Argument types can be overridden."
                 (loop :for (name args . function-body) :in defs
                       :for argnames = (mapcar (compose #'first #'ensure-list) args)
                       :for argtypes = (mapcar (lambda (a)
                                                 (or (second (ensure-list a))
                                                     '(unsigned-byte 32)))
                                               args)
                       :collect `(inline ,name) :into body-decls
                       :collect `(ftype (function ,argtypes (unsigned-byte 32)) ,name)
                         :into body-decls
                       :collect `(,name ,argnames
                                        (declare (optimize speed)
                                                 ,@(mapcar (lambda (arg type)
                                                             `(type ,type ,arg))
                                                           argnames argtypes))
                                        ,@function-body)
                         :into functions
                       :finally
                          (return `(labels ,functions
                                     (declare ,@body-decls)
                                     ,@body)))))
      (with-ub32-funcs
          ((rotr (x (n (integer 0 25)))
                 (logior (ash x (- n)) (ash (ldb (byte n 0) x) (- 32 n))))
           (mod+ (x y) (logand #xFFFFFFFF (+ x y)))
           (ch  (x y z) (logxor (logand x y) (logandc1 x z)))
           (maj (x y z) (logxor (logand x y) (logand x z) (logand y z)))
           (bsig0 (x) (logxor (rotr x 2) (rotr x 13) (rotr x 22)))
           (bsig1 (x) (logxor (rotr x 6) (rotr x 11) (rotr x 25)))
           (ssig0 (x) (logxor (rotr x 7) (rotr x 18) (ash x -3)))
           (ssig1 (x) (logxor (rotr x 17) (rotr x 19) (ash x -10))))
        ;; 1. Prepare the message schedule W:
        (dotimes (i 16)
          (setf (aref schedule i) (ub32ref/be buffer (+ start (* 4 i)))))
        (loop :for i :from 16 :below 64 :do
          (setf (aref schedule i)
                (mod+ (mod+ (ssig1 (aref schedule (- i 2)))
                            (aref schedule (- i 7)))
                      (mod+ (ssig0 (aref schedule (- i 15)))
                            (aref schedule (- i 16))))))
        ;; 2. Initialize the working variables:
        (setf . #.(loop :for var :in '(a b c d e f g h)
                        :for index :from 0
                        :collect var
                        :collect `(aref regs ,index)))
        ;; 3. Perform the main hash computation:
        (dotimes (i 64)
          (setf t1 (mod+ (mod+ h
                               (bsig1 e))
                         (mod+ (ch e f g)
                               (mod+ (aref +sha-256-constants+ i)
                                     (aref schedule i)))))
          ;; With a bit of unrolling (4), you can replace these `shiftf' forms
          ;; with variable renaming for an 18% speed increase. Meh.
          (shiftf h g f e (mod+ d t1))
          (shiftf d c b a (mod+ t1 (mod+ (bsig0 a) (maj a b c)))))
        ;; 4. Compute the intermediate hash value H(i)
        (setf . #.(loop :for var :in '(a b c d e f g h)
                        :for index :from 0
                        :collect `(aref regs ,index)
                        :collect `(mod+ (aref regs ,index) ,var)))))))

(defun update-sha-256 (buffer start end state)
  (let ((schedule (make-array 64 :element-type '(unsigned-byte 32)))
        (block (sha-256-state-block state)))
    (incf (sha-256-state-bit-length state) (* 8 (- end start)))
    ;; If there's an old block, fill up and handle that one first.
    (unless (zerop (sha-256-state-block-index state))
      (let ((increment (min (- 64 (sha-256-state-block-index state))
                            (- end start))))
        (replace block buffer
                 :start1 (sha-256-state-block-index state)
                 :end1 (+ (sha-256-state-block-index state) increment)
                 :start2 start
                 :end2 (+ start increment))
        (incf (sha-256-state-block-index state) increment)
        (incf start increment))
      (when (= (length block) (sha-256-state-block-index state))
        (handle-sha-256-block block 0 (sha-256-state-regs state) schedule)
        (setf (sha-256-state-block-index state) 0)))

    ;; Full blocks are handled directly since that's simpler and faster.
    (loop :while (<= start (- end 64)) :do
      (handle-sha-256-block buffer start (sha-256-state-regs state) schedule)
      (incf start 64))

    ;; Start a new block if necessary; the test is needed for the case where the
    ;; provided input is too small to finish the old block.
    (when (zerop (sha-256-state-block-index state))
      (assert (< (- end start) 64))
      (replace block buffer :start2 start :end2 end)
      (setf (sha-256-state-block-index state) (- end start)))

    state))

(defun finish-sha-256 (state)
  (let ((bit-length (sha-256-state-bit-length state)))
    ;; This can be triggered by very large XZ files, even if they stay within
    ;; the 64-bit byte length limit, because SHA-256 needs a 64-bit _bit_
    ;; length. It feels wrong to signal a decompression error in a largely
    ;; standalone hash function, but I don't know how else to handle this case
    ;; elegantly.
    (unless (< bit-length (expt 2 64))
      (die "Input data is too long for SHA-256."))
    ;; Pad bit length to multiple of 512 after appending a 1 bit and a 64-bit
    ;; length field.
    (let ((padding (make-array (/ (+ 1 64 (mod (- 512 64 1 bit-length) 512))
                                  8)
                               :element-type 'octet
                               :initial-element 0)))
      ;; Since our input is byte-wise, the appended one bit is always the most
      ;; significant bit of the byte. Since the fully padded message has a size
      ;; that's a multiple of 512 bits and the length field takes up 64 bits,
      ;; the octet we're setting here cannot possibly overlap with the length.
      (setf (aref padding 0) #x80)
      (dotimes (i 8)
        (setf (aref padding (- (length padding) 1 i))
              (ldb (byte 8 (* 8 i)) bit-length)))
      (setf state (update-sha-256 padding 0 (length padding) state)))
    (assert (zerop (sha-256-state-block-index state)))
    ;; Gotta convert to little endian since that's what we use for XZ checksums.
    (reduce (lambda (n a)
              (logior (reverse-ub32-byte-order n) (ash a 32)))
            (sha-256-state-regs state)
            :initial-value 0 ;; ensures that _all_ words are byte-reversed
            :from-end t)))
