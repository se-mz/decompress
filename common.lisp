(cl:defpackage #:semz.decompress
  (:use #:cl)
  (:export #:decompress
           #:decompress-all
           #:make-decompression-stream
           #:make-full-decompression-stream
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
                #:compose
                #:define-constant
                #:ensure-list
                #:iota
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
   "Signalled when the input stream/buffer is exhausted. Notably implies that we
did not detect errors in the data up until this point, but this is not a hard
guarantee that the data can be continued in a valid manner since it would be
infeasible to verify this.

Even when the input is a stream, it is this condition which is signalled, not
`end-of-file'."))

(defun die (fmt &rest fmt-args)
  (error 'decompression-error :format-control fmt :format-arguments fmt-args))

(defun %eof ()
  (error 'eof :format-control "Premature end of input."))

(deftype octet ()
  '(unsigned-byte 8))

(deftype buffer ()
  '(simple-array octet (*)))


;;;; Fast functions
;;;
;;; We rely heavily on typed inline functions rather than big macrolets in the
;;; interest of readability; the macros below reduce the resulting clutter and
;;; make it easier to adjust optimization qualities.
;;;
;;; As a general rule, we want to go fast, ignore qualities that are already
;;; affected by heavy inlining, and keep the rest at the neutral defaults.
;;;
;;; On ABCL, (safety 0) makes a huge difference and basically just eliminates
;;; type checks and inlines accesses. Since ABCL is JVM-based, the bad
;;; consequences of (safety 0) are rather mild, too. Now if only it got an
;;; actually fast `replace' implementation...
;;;
;;; ECL has unusual default settings: (speed 3) (space 0) (safety 2) (debug 3).
;;; The manual documents how these settings affect things:
;;;
;;; https://ecl.common-lisp.dev/static/manual/Evaluation-and-compilation.html
;;;
;;; Setting safety and debug to 1 seems fine, considering what effects type
;;; declarations already have on implementations like CCL. (safety 0) speeds up
;;; things by quite a bit, but even ECL devs recommend against it, so that's an
;;; easy no.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *optimize-decls*
    '((speed 3) (space 0) (compilation-speed 0)
      #-abcl (safety 1)
      #+abcl (safety 0)
      (debug 1))
    "The implementation-dependent optimization qualities used for fast functions."))

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
                       ,name))
       (defun ,name (,@(mapcar #'first args))
         (declare ,@(mapcar (lambda (a)
                              (destructuring-bind (name type) a
                                `(type ,type ,name)))
                            args)
                  (optimize ,@*optimize-decls*))
         ,@body))))

(defmacro define-fast-inline-function (name-with-optional-return-type (&rest args) &body body)
  `(progn
     (declaim (inline ,(first (ensure-list name-with-optional-return-type))))
     (define-fast-function ,name-with-optional-return-type (,@args) ,@body)))


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

(defmacro with-prefixed-names ((&rest names) prefix &body body)
  `(let (,@(mapcar
             (lambda (name)
               `(,name (intern (concatenate 'string
                                            ;; `prefix' is evaluated
                                            (string ,prefix)
                                            ;; `name' isn't
                                            ,(string name)))))
             names))
     ,@body))

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
            value)))
     (define-be-accessor (name octet-count)
       `(progn
          (declaim (inline ,name (setf ,name))
                   (ftype (function (buffer array-length) (unsigned-byte ,(* 8 octet-count))) ,name))
          (defun ,name (vector index)
            (declare (type buffer vector)
                     (type array-length index))
            (logior ,@(loop :for i :from 0 :below octet-count
                            :collect `(ash (aref vector (+ index ,(- octet-count 1) (- ,i)))
                                           ,(* 8 i)))))
          (defun (setf ,name) (value vector index)
            (setf ,@(loop :for i :from 0 :below octet-count
                          :collect `(aref vector (+ index ,(- octet-count 1) (- ,i)))
                          :collect `(ldb (byte 8 ,(* 8 i)) value)))
            value))))
  (define-le-accessor ub16ref/le 2)
  (define-le-accessor ub24ref/le 3)
  (define-le-accessor ub32ref/le 4)
  (define-le-accessor ub48ref/le 6)
  (define-le-accessor ub64ref/le 8)

  (define-be-accessor ub16ref/be 2)
  (define-be-accessor ub32ref/be 4)
  (define-be-accessor ub64ref/be 8))

(defun positions-if (predicate sequence)
  (loop :for i :from 0 :below (length sequence)
        :when (funcall predicate (elt sequence i))
          :collect i))

(defun positions (elt sequence)
  (positions-if (lambda (x) (eql x elt)) sequence))

(defun hexdigitp (char)
  (not (not (position char "0123456789abcdefABCDEF"))))

(defun reverse-ub32-byte-order (ub32)
  (logior (ash (ldb (byte 8 0) ub32) 24)
          (ash (ldb (byte 8 8) ub32) 16)
          (ash (ldb (byte 8 16) ub32) 8)
          (ash (ldb (byte 8 24) ub32) 0)))


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

(defgeneric make-reset-state (old-state)
  (:documentation
   "Returns two values:

1. A new state that reads the next member of the same type, handling potential
padding/etc in between, and maybe reuses large intermediate resources.

2. The new header plist.

If the format doesn't support multi-member files, returns nil."))

;;; Most formats don't support multiple members, so default to that.
(defmethod make-reset-state (old-state)
  (declare (ignore old-state))
  nil)

;;; Multi-member formats with trailing non-member data (e.g. padding) can handle
;;; it in `make-reset-state' and then return this dummy state to signal EOF.
(defclass eof-dummy-state () ())
(defmethod next-decompressed-chunk ((state eof-dummy-state))
  (values +dummy-buffer+ 0 0 t))


;;;; Lempel-Ziv helpers

;;; We usually unify dictionaries and output buffers by designating the first
;;; `d' bytes as the dictionary area. When the output buffer is full, we publish
;;; the new data; on the next `next-decompressed-chunk' call, we then move the
;;; last `d' bytes into the dictionary area at the start. Until the buffer is
;;; filled for the first time, we write directly into the dictionary area.
(defun flush-dict-buffer (buffer buffer-i dict-size)
  "Moves trailing data in `buffer' into the dictionary area as designated by
`dict-size'. Returns the new value of `buffer-i'."
  (declare (type buffer buffer)
           (type array-length buffer-i dict-size))
  (if (<= buffer-i dict-size)
      buffer-i
      (progn
        (replace buffer buffer
                 :start1 0 :end1 dict-size
                 :start2 (- buffer-i dict-size)
                 :end2 buffer-i)
        dict-size)))

;;; Lempel-Ziv matches are a common feature and usually have relatively small
;;; lengths (~300 max). As a result, this simple loop implementation has less
;;; overhead than `replace' and deals with overlaps. The (safety 0) matters for
;;; heavily compressed files; the loop is simple and guarded by an assertion, so
;;; it's fine.
(define-fast-inline-function copy-match
    ((buffer buffer)
     (src-i array-length)
     (dest-i array-length)
     (length array-length))
  (assert (<= (+ src-i 1) dest-i (- (length buffer) length)))
  (locally (declare (optimize (safety 0)))
    (loop :for i :of-type array-length :from 0 :below length :do
      (setf (aref buffer (+ dest-i i))
            (aref buffer (+ src-i i))))))
