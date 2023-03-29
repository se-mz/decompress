(cl:defpackage #:semz.decompress
  (:use #:cl)
  (:export #:decompress
           #:make-decompression-stream
           #:list-supported-formats

           #:make-simple-zlib-dictionary
           #:adler-32

           #:decompression-stream
           #:decompression-stream-format
           #:decompression-stream-header

           #:decompression-error
           #:eof
           #:unrecognized-zlib-dictionary
           #:unrecognized-zlib-dictionary-checksum)
  (:import-from #:alexandria
                #:array-length
                #:clamp
                #:define-constant
                #:ensure-list
                #:read-stream-content-into-byte-vector
                #:remove-from-plistf
                #:required-argument
                #:with-gensyms)
  (:import-from #:trivial-gray-streams
                #:fundamental-binary-input-stream
                #:stream-read-byte
                #:stream-read-sequence))
(cl:in-package #:semz.decompress)


;;;; Types & conditions

(define-condition decompression-error (simple-error) ()
  (:documentation "General superclass for errors related to decompression."))

(define-condition eof (decompression-error) ()
  (:documentation
   "Signalled when the input stream/buffer is exhausted. Notably implies that the
data up until this point was not detectably malformed. Note that even when the
input is a stream, it is this condition which is signalled, not `end-of-file'."))

(defun die (fmt &rest fmt-args)
  (error 'decompression-error :format-control fmt :format-arguments fmt-args))

(defun %eof ()
  (error 'eof :format-control "Premature end of input."))

(deftype octet ()
  '(unsigned-byte 8))

(deftype buffer ()
  '(simple-array octet (*)))


;;;; Helpers

(define-constant +dummy-buffer+ (coerce #() 'buffer)
  :test 'equalp
  :documentation "Placeholder for buffer-typed slots.")

;;; We need to make some size choice when buffering things; 8192 seems fine.
(defparameter *default-buffer-size* (expt 2 13))

(defun ensure-simple-vector-constant (constant)
  (assert (constantp constant))
  (let ((result (eval constant)))
    (assert (typep result 'simple-vector))
    result))

(deftype element-of (sv-constant)
  (let ((sv (ensure-simple-vector-constant sv-constant)))
    (if (every #'integerp sv)
        `(integer ,(reduce #'min sv) ,(reduce #'max sv))
        `T)))

(deftype index-for (sv-constant)
  `(mod ,(length (ensure-simple-vector-constant sv-constant))))

(defmacro csvref (sv-constant index)
  "An `svref' for constants that derives integer bounds if possible."
  `(the (element-of ,sv-constant) (svref ,sv-constant ,index)))

(defmacro onetime-macrolet ((&rest bindings) &body code)
  (with-gensyms (define)
    `(macrolet ((,define () (let* ,bindings ,@code)))
       (,define))))

;;; We rely heavily on typed inline functions rather than big macrolets in the
;;; interest of readability; this macro removes some of the resulting clutter.
(defmacro define-fast-function (name-with-optional-return-type (&rest args) &body body)
  (destructuring-bind (name &optional (return-type '*))
      (ensure-list name-with-optional-return-type)
    (setf args (mapcar (lambda (x)
                         (if (listp x)
                             (progn
                               (assert (= 2 (length x)))
                               x)
                             (list x 'T)))
                       args))
    `(progn
       (declaim (ftype (function (,@(mapcar #'second args))
                                 ,@(if (eq return-type '*)
                                       '()
                                       `(,return-type)))
                       ,name)
                (inline ,name))
       (defun ,name (,@(mapcar #'first args))
         (declare ,@(mapcar (lambda (a)
                              (destructuring-bind (name type) a
                                `(type ,type ,name)))
                            args)
                  (optimize speed))
         ,@body))))

(defmacro normalize-bounds (array start end)
  (check-type array symbol)
  (check-type start symbol)
  (check-type end symbol)
  `(progn
     (check-type ,array (array * (*)))
     (setf ,start (or ,start 0))
     (setf ,end (or ,end (length ,array)))
     (check-type ,start array-length)
     (check-type ,end array-length)
     (assert (<= 0 ,start ,end (length ,array)))))

;;; I have been burned by nibbles before and I won't be again.
(macrolet
    ((define-le-accessor (name octet-count)
       `(progn
          (declaim (inline ,name (setf ,name))
                   (ftype (function (buffer array-length) (unsigned-byte ,(* 8 octet-count))) ,name))
          (defun ,name (vector index)
            (declare (type buffer vector)
                     (type array-length index))
            (logior ,@(loop :for i :from 0 :below octet-count
                            :collect `(ash (aref vector (+ index ,i)) ,(* 8 i)))))
          (defun (setf ,name) (value vector index)
            (setf ,@(loop :for i :from 0 :below octet-count
                          :collect `(aref vector (+ index ,i))
                          :collect `(ldb (byte 8 ,(* 8 i)) value)))
            value))))
  (define-le-accessor ub16ref/le 2)
  (define-le-accessor ub32ref/le 4)
  (define-le-accessor ub64ref/le 8))


;;;; Internal interface
;;;
;;; For each format, there should be methods defined on these two functions.
;;; `format' is always an identifying keyword such as :deflate or :zlib.
;;;
;;; The decompressed output is divided into "chunks" in some
;;; implementation-defined manner. The only requirement is that there is some
;;; sane upper bound for chunk size (to keep memory usage bounded).

(defparameter *known-formats* '()
  "`pushnew' the format keyword to this once you've implemented a new format.")

(defgeneric byte-source->decompression-state (format byte-source &key &allow-other-keys)
  (:documentation
   "Reads the necessary data from the given `byte-source' (see `io.lisp') to create
a decompression state for `format'. Returns two values: The decompression state
that can be passed to `next-decompressed-chunk' later and a plist of header
metadata which will be returned to the user."))

(defgeneric next-decompressed-chunk (state)
  (:documentation
   "Returns four values: chunk, start, end, finalp. The data is in `chunk',
between `start' and `end'. No callers modify the contents of `chunk'; methods
may change its contents on later calls, but not before that."))
