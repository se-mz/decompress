;; Assume semz.decompress is given the nickname d.

;; `decompress-all' is the idiomatic method for buffer-to-buffer decompression.
;; Input buffers need not be simple or specialized, but output buffers are both.
;; The second return value contains header information in the form of a plist.
(d:decompress-all :zlib #(120 156  99 84 100 7 0  0 79 0 42))
;; => #(1 33 7), (:WINDOW-SIZE 32768 :LEVEL 2 :DICTIONARY NIL)

;; If a format supports multiple members, `decompress-all' concatenates them.
;; The header information is always the first member's, as you can tell by the
;; filename field in this example.
(d:decompress-all
 :gzip
 ;;                          v  foo/bar  v
 #(31 139 8 8  0 0 0 0  0 0  102 111 111 0  99 84 100 7 0  101 51 120 236  3 0 0 0
   31 139 8 8  0 0 0 0  0 0   98  97 114 0  99 84 100 7 0  101 51 120 236  3 0 0 0))
;; => #(1 33 7 1 33 7),
;;    (:TEXTP NIL :EXTRA-FIELDS NIL :FILENAME "foo" :COMMENT NIL :MODIFICATION-TIME 0
;;     :EXTRA-FLAGS 0 :OPERATING-SYSTEM 0)

;; Vector inputs can be limited by :start and :end arguments, just like for the
;; sequence functions. This example reads the embedded Deflate section of a zlib
;; buffer. Deflate has no header info.
(d:decompress-all :deflate #(120 156  99 84 100 7 0  0 79 0 42)
                  :start 2 :end 7)
;; => #(1 33 7), NIL

;; Trailing data causes an error with `decompress-all'.
(d:decompress-all :zlib #(120 156  99 84 100 7 0  0 79 0 42  1 2 3))
;; => signals a `decompression-error'

;; Streams are also fine as input. They ignore :start and :end.
(alexandria:write-byte-vector-into-file
 (coerce #(120 156  99 84 100 7 0  0 79 0 42)
         '(simple-array (unsigned-byte 8) (*)))
 #p"single.z")
(with-open-file (f #p"single.z" :element-type '(unsigned-byte 8))
  (d:decompress-all :zlib f))
;; => #(1 33 7), (:WINDOW-SIZE 32768 :LEVEL 2 :DICTIONARY NIL)

;; `decompress' decompresses a single member from the input and leaves all
;; trailing data intact, allowing intricate stream processing. This is also a
;; convenient way to get the header info of later members if you need it.
(alexandria:write-byte-vector-into-file
 (coerce #(99 84 100 7 0  99 84 123 7 0  1 2 3)
         '(simple-array (unsigned-byte 8) (*)))
 #p"multi.bin")
(with-open-file (f #p"multi.bin" :element-type '(unsigned-byte 8))
  (list (d:decompress :deflate f)
        (d:decompress :deflate f)
        (alexandria:read-stream-content-into-byte-vector f)))
;; => (#(1 33 7) #(1 38 238) #(1 2 3))

;; There is also a Gray stream class for more complicated uses, which
;; `decompress' wraps. There's no need to close the decompression stream itself,
;; but any underlying stream must be closed by the user. The header information
;; can be queried with `decompression-stream-header'.
(let ((s (d:make-decompression-stream :zlib #(120 156  99 84 100 7 0  0 79 0 42))))
  (list (alexandria:read-stream-content-into-byte-vector s)
        (d:decompression-stream-header s)))
;; => (#(1 33 7) (:WINDOW-SIZE 32768 :LEVEL 2 :DICTIONARY NIL))

;; `decompress-all' is really just `decompress' with `all-members-p' set.
;; `make-full-decompression-stream' relates to `make-decompression-stream' the
;; same way. They're separate functions since forgetting an `all-members-p' can
;; result in very subtle bugs.
(d:decompress :deflate #(99 84 100 7 0  99 84 123 7 0  1 2 3)
              :start 5 :all-members-p t)
;; => signals a decompression-error

;; Unlike many other libraries, this one supports zlib preset dictionaries.
(d:decompress-all :zlib #(120 249  0 79 0 42  3 34 0  0 79 0 42)
                  :dictionary (d:make-simple-zlib-dictionary '(#(1 33 7))))
;; => #(1 33 7), (:WINDOW-SIZE 32768 :LEVEL 3 :DICTIONARY 5177386)

;; These objects can be passed to specify the compression format.
(d:list-supported-formats)
;; => (:XZ :LZMA2 :RAW-LZMA2 :LZMA :RAW-LZMA :BZIP2 :GZIP :ZLIB :DEFLATE)
