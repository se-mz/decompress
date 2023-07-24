;;;; XZ branch/call/jump filters
;;;
;;; This is a direct adaptation of the corresponding XZ Utils code (v5.4.3),
;;; which is in the public domain and can be found at `src/liblzma/simple/'. I
;;; didn't replace the C-style bit operations with LDB et al to make it easier
;;; to verify that the code is the same.
(cl:in-package #:semz.decompress)

;;; Provides `buffer', `i', `end' and `now-pos' to the environment, with the
;;; same meaning as in XZ Utils. `i' is also called `buffer_pos' in the source
;;; for the x86 filter. The final state of `i' determines how many bytes are
;;; output; leftover bytes will be at the start of the buffer next time.
;;; Trailing bytes at the very end that can't be processed are output verbatim.
(defmacro define-bcj-filter (arch vars &body body)
  (with-gensyms (generator bs start preserve)
    `(defun ,(intern (concatenate 'string "WRAP-IN-XZ-" (string arch) "-FILTER"))
         (,generator now-pos)
       (let ((,bs (chunk-generator->buffer-stream ,generator))
             ;; At least 16 are necessary to guarantee progress for all filters.
             (buffer (make-array (max 16 *default-buffer-size*) :element-type 'octet))
             (,start 0)
             (end 0)
             (,preserve 0)
             ,@vars)
         (lambda ()
           (declare (type array-length ,start end ,preserve)
                    (type (unsigned-byte 32) now-pos)
                    (type buffer buffer)
                    (optimize speed))
           ;; Get the leftover data from last time into position
           (replace buffer buffer :end1 ,preserve :start2 (- end ,preserve))
           (setf ,start ,preserve)
           (setf end (bs-read-sequence buffer ,bs :start ,start))
           ;; We only preserve if we can't process further, so if there is no new
           ;; data, there is nothing left to do.
           (if (= ,start end)
               (values buffer 0 ,start t)
               (let ((i 0))
                 (declare (type array-length i))
                 ,@body
                 (setf ,preserve (- end i))
                 (setf now-pos (logand #xFFFFFFFF (+ now-pos i)))
                 (values buffer 0 i nil))))))))

(define-bcj-filter arm ()
  (loop :while (<= i (- end 4)) :do
    (when (= (aref buffer (+ i 3)) #xEB)
      (setf (ub24ref/le buffer i)
            (ash (logand #xFFFFFFFF
                         (- (ash (ub24ref/le buffer i) 2)
                            now-pos i 8))
                 -2)))
    (incf i 4)))

(define-bcj-filter arm64 ()
  (loop :while (<= i (- end 4)) :do
    (let ((pc (logand #xFFFFFFFF (+ now-pos i)))
          (instr (ub32ref/le buffer i)))
      (declare (type (unsigned-byte 32) pc instr))
      (cond
        ((= (ash instr -26) #x25)
         (setf (ub32ref/le buffer i)
               (logior (logand (- instr (ash pc -2))
                               #x03FFFFFF)
                       #x94000000)))

        ((= (logand instr #x9F000000) #x90000000)
         (let ((src (logior (logand (ash instr -29) 3)
                            (logand (ash instr -3) #x001FFFFC))))
           (declare (type (unsigned-byte 32) src))
           (when (zerop (logand (+ src #x00020000) #x001C0000))
             (setf (ub32ref/le buffer i)
                   (let ((dest (logand #xFFFFFFFF (- src (ash pc -12)))))
                     (declare (type (unsigned-byte 32) dest))
                     (logior (logand instr #x9000001F)
                             (ash (logand dest 3) 29)
                             (ash (logand dest #x0003FFFC) 3)
                             (logand (- 0 (logand dest #x00020000))
                                     #x00E00000)))))))))
    (incf i 4)))

(define-bcj-filter armthumb ()
  (loop :while (<= i (- end 4)) :do
    (when (and (= (logand (aref buffer (+ i 1)) #xF8) #xF0)
               (= (logand (aref buffer (+ i 3)) #xF8) #xF8))
      (let* ((src (ash (logior (ash (logand (aref buffer (+ i 1)) 7) 19)
                               (ash (aref buffer (+ i 0)) 11)
                               (ash (logand (aref buffer (+ i 3)) 7) 8)
                               (ash (aref buffer (+ i 2)) 0))
                       1))
             (dest (ash (logand #xFFFFFFFF (- src (+ now-pos i 4)))
                        -1)))
        (declare (type (unsigned-byte 32) src dest))
        (setf (aref buffer (+ i 1)) (logior #xF0 (logand (ash dest -19) 7))
              (aref buffer (+ i 0)) (logand #xFF (ash dest -11))
              (aref buffer (+ i 3)) (logior #xF8 (logand (ash dest -8) 7))
              (aref buffer (+ i 2)) (logand #xFF dest))
        (incf i 2)))
    (incf i 2)))

(define-bcj-filter ia64 ()
  (loop :while (<= i (- end 16)) :do
    (let ((mask (aref #(0 0 0 0  0 0 0 0
                        0 0 0 0  0 0 0 0
                        4 4 6 6  0 0 7 7
                        4 4 0 0  4 4 0 0)
                      (logand (aref buffer i) #x1F))))
      (declare (type (integer 0 7) mask))
      (loop :for slot :from 0 :below 3
            :for bit-pos :from 5 :by 41 :to 87
            :do (unless (zerop (logand (ash mask (- slot)) 1))
                  (let* ((byte-pos (ash bit-pos -3))
                         (bit-res (logand bit-pos 7))
                         (instruction (ub48ref/le buffer (+ i byte-pos)))
                         (inst-norm (ash instruction (- bit-res))))
                    (when (and (= (logand (ash inst-norm -37) #xF) #x5)
                               (= (logand (ash inst-norm -9) #x7) 0))
                      (let* ((src (ash (logior (logand (ash inst-norm -13) #xFFFFF)
                                               (ash (logand (ash inst-norm -36) 1) 20))
                                       4))
                             (dest (ash (logand (- src now-pos i) #xFFFFFFFF)
                                        -4)))
                        (declare (type (unsigned-byte 32) src dest))
                        (setf (ub48ref/le buffer (+ i byte-pos))
                              (logior (logand (- (ash 1 bit-res) 1) instruction)
                                      (ash (logior (ash (logand dest #x100000) (- 36 20))
                                                   (ash (logand dest #xFFFFF) 13)
                                                   (logand inst-norm (lognot (ash #x8FFFFF 13))))
                                           bit-res))))))))
      (incf i 16))))

(define-bcj-filter powerpc ()
  (loop :while (<= i (- end 4)) :do
    (when (and (= (ash (aref buffer i) -2) #x12)
               (= (logand (aref buffer (+ i 3)) 3) 1))
      (let ((dest (logand (- (logior (ash (logand (aref buffer (+ i 0)) 3) 24)
                                     (ash (aref buffer (+ i 1)) 16)
                                     (ash (aref buffer (+ i 2)) 8)
                                     (logandc2 (aref buffer (+ i 3)) 3))
                             now-pos i)
                          #xFFFFFFFF)))
        (declare (type (unsigned-byte 32) dest))
        (setf (aref buffer (+ i 0)) (logior #x48 (ldb (byte 2 24) dest))
              (aref buffer (+ i 1)) (ldb (byte 8 16) dest)
              (aref buffer (+ i 2)) (ldb (byte 8 8) dest)
              (aref buffer (+ i 3)) (logior (logand (aref buffer (+ i 3)) 3)
                                            (logand #xFF dest)))))
    (incf i 4)))

(define-bcj-filter sparc ()
  (loop :while (<= i (- end 4)) :do
    (when (or (and (= (aref buffer i) #x40)
                   (= (logand (aref buffer (+ i 1)) #xC0) #x00))
              (and (= (aref buffer i) #x7F)
                   (= (logand (aref buffer (+ i 1)) #xC0) #xC0)))
      (let ((dest (ash (logand (- (ash (ub32ref/be buffer i) 2)
                                  now-pos i)
                               #xFFFFFFFF)
                       -2)))
        (declare (type (unsigned-byte 32) dest))
        (setf (ub32ref/be buffer i)
              (logior (logand (ash (- 0 (logand (ash dest -22) 1))
                                   22)
                              #x3FFFFFFF)
                      (logand dest #x3FFFFF)
                      #x40000000))))
    (incf i 4)))

(define-bcj-filter x86 ((prev-mask 0) (prev-pos (logand #xFFFFFFFF -5)))
  (declare (type (unsigned-byte 32) prev-mask prev-pos))
  (unless (< end 5)
    (when (> (logand (- now-pos prev-pos) #xFFFFFFFF) 5)
      (setf prev-pos (- now-pos 5)))

    (let ((limit (- end 5)))
      (loop :while (<= i limit) :do
        (if (and (/= (aref buffer i) #xE8)
                 (/= (aref buffer i) #xE9))
            (incf i)
            (let ((offset (logand (+ now-pos i (- prev-pos))
                                  #xFFFFFFFF)))
              (declare (type (unsigned-byte 32) offset))
              (setf prev-pos (logand (+ now-pos i) #xFFFFFFFF))
              (if (> offset 5)
                  (setf prev-mask 0)
                  (loop :repeat offset :do
                    (setf prev-mask (ash (logand prev-mask #x77) 1))))

              (let ((b (aref buffer (+ i 4))))
                (declare (type octet b))
                (if (and (or (= b #x00) (= b #xFF))
                         (aref #(t t t nil t nil nil nil)
                               (logand (ash prev-mask -1) #x7))
                         (< (ash prev-mask -1) #x10))
                    (let ((src (ub32ref/le buffer (+ i 1))))
                      (declare (type (unsigned-byte 32) src))
                      (loop :for dest :of-type (unsigned-byte 32)
                              = (logand (- src now-pos i 5) #xFFFFFFFF)
                            :do (when (zerop prev-mask)
                                  (loop-finish))
                                ;; We call this `j' instead since `i' is taken.
                                (let ((j (aref #(0 1 2 2 3 3 3 3) (ash prev-mask -1))))
                                  (declare (type (integer 0 3) j))
                                  (setf b (logand #xFF (ash dest (- (- 24 (* j 8))))))
                                  (when (not (or (= b #x00) (= b #xFF)))
                                    (loop-finish))
                                  (setf src (logxor dest (- (ash 1 (- 32 (* j 8)))
                                                            1))))
                            :finally (setf (aref buffer (+ i 4))
                                           (logand #xFF (lognot (- (logand (ash dest -24) 1)
                                                                   1)))
                                           (ub24ref/le buffer (+ i 1)) dest)
                                     (incf i 5)
                                     (setf prev-mask 0)))
                    (progn
                      (incf i)
                      (setf prev-mask (logior prev-mask 1))
                      (when (or (= b #x00) (= b #xFF))
                        (setf prev-mask (logior prev-mask #x10))))))))))))
