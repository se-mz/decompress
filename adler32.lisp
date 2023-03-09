;;;; Adler-32 checksum
;;;
;;; The state of the Adler-32 hash function is a pair of integers (s1, s2), both
;;; modulo the prime p = 65521, initially (1,0). For each byte b, we update to
;;; (s1+b mod p, s2+s1+b mod p). The checksum of a byte string a_1, ..., a_n is
;;; therefore
;;;
;;;     (s1 + Σ[i=1…n] a_i  mod p,   s2 + Σ[i=1…n] (s1 + Σ[j=1…i] a_j)  mod p).
;;;
;;; The checksum state is canonically serialized as s2 * 2^16 + s1.
;;;
;;; This function is run across the entire uncompressed output and optimizing it
;;; has a large impact. The obvious approach is to delay the modular reduction
;;; for a while; it is almost always possible to delay reduction so that bignum
;;; arithmetic is avoided.
;;;
;;; If L is the maximal value that s1 and s2 may take on before reduction, then
;;; the largest number of iterations you can perform without running the risk of
;;; bignum arithmetic is the largest n > 0 such that
;;;
;;;     p-1 + n * 255,
;;;
;;;     p-1 + Σ[i=1…n] (p-1 + i * 255)
;;;       = p-1 + n(p-1) + 255 * n(n+1)/2
;;;       = 255/2 * n² + (p-1 + 255/2) * n + p-1
;;;
;;; are both at most L. Clearly, only the second term matters. Such an `n'
;;; exists if and only if L >= 131295 since for L = 131295, we have n = 1.
;;;
;;; In practice, `n' is so much larger than our buffer lengths that we only
;;; reduce once. The main loop is so hot that bignum promotion checks, bounds
;;; checks and default safety type checks add up to a significant amount of
;;; waste; deleting them via (safety 0) results in a 2.5x speedup under SBCL.
(cl:in-package #:semz.decompress)

(onetime-macrolet ((L most-positive-fixnum)
                   (p 65521))
  (labels ((L->n (L)
             ;; Just find the largest solution of the deg 2 polynomial.
             (let* ((a 255/2)
                    (b (+ p -1 255/2))
                    (c (- p 1 L))
                    (d (- (expt b 2) (* 4 a c))))
               (if (>= d 0)
                   (floor (/ (+ (- b) (sqrt (float d 0d0))) 2 a))
                   0))))
    ;; 2^30 - 1 is hopefully still fast enough when fixnums are tiny.
    (when (< (L->n L) 1)
      (setf L (- (expt 2 30) 1)))
    (let ((max-iterations (floor (L->n L))))
      (assert (>= L (- (expt 2 16) 1)))
      (assert (>= max-iterations 1))

      `(defun update-adler-32 (buffer start end state)
         (declare (type buffer buffer)
                  (type (unsigned-byte 32) state)
                  (type array-length start end))
         (assert (<= 0 start end (length buffer)))
         (let ((s1 (ldb (byte 16  0) state))
               (s2 (ldb (byte 16 16) state)))
           (declare (type (integer 0 ,L) s1 s2))
           (loop :while (< start end) :do
             (locally (declare (optimize (safety 0)))
               (loop :repeat (min ,max-iterations (- end start)) :do
                 (incf s1 (aref buffer start))
                 (incf s2 s1)
                 (incf start)))
             (setf s1 (mod s1 ,p)
                   s2 (mod s2 ,p)))
           (logior (ash s2 16) s1))))))

(defun start-adler-32 () 1)
(defun finish-adler-32 (state) state)

(defun adler-32 (data &key start end)
  "Returns the Adler-32 checksum of the given data, in the form s2 * 2^16 + s1."
  (normalize-bounds data start end)
  (finish-adler-32
   (update-adler-32 (if (typep data 'buffer)
                        data
                        ;; I don't really care that this is inefficient; it
                        ;; makes next to no sense to use this with gigantic
                        ;; non-buffers, so slowdowns are the user's fault.
                        (replace (make-array (- end start) :element-type 'octet)
                                 data :start2 start :end2 end))
                    start end (start-adler-32))))
