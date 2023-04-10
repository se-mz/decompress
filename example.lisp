;; Decompress buffer contents into a fresh buffer. The input buffer need not be
;; simple or specialized, but the output always is both. The second output value
;; contains header information.
(semz.decompress:decompress :zlib #(120 156  99 84 100 7 0  0 79 0 42))
;; => #(1 33 7), (:window-size 32768 :level 2 :dictionary nil)

;; These objects can be passed to specify the compression format.
(semz.decompress:list-supported-formats)
;; => (:bzip2 :gzip :zlib :deflate)

;; `decompress' accepts :start and :end arguments for vector arguments, just
;; like the sequence functions. Trailing data is ignored. This example reads
;; the embedded Deflate section of a zlib buffer.
(semz.decompress:decompress :deflate #(120 156  99 84 100 7 0  0 79 0 42)
                            :start 2)
;; => #(1 33 7), nil

(alexandria:write-byte-vector-into-file
 (coerce #(99 84 100 7 0  99 84 123 7 0  1 2 3)
         '(simple-array (unsigned-byte 8) (*)))
 #p"/tmp/sd-test-file.bin")

;; Streams are also fine as input. Only the needed bytes are read, allowing
;; complex stream processing…
(with-open-file (f #p"/tmp/sd-test-file.bin" :element-type '(unsigned-byte 8))
  (list (semz.decompress:decompress :deflate f)
        (semz.decompress:decompress :deflate f)
        (alexandria:read-stream-content-into-byte-vector f)))
;; => (#(1 33 7) #(1 38 238) #(1 2 3))

;; …but this can be relaxed to reduce stream reading overhead.
(with-open-file (f #p"/tmp/sd-test-file.bin" :element-type '(unsigned-byte 8))
  (list (semz.decompress:decompress :deflate f :allow-overreads-p t)
        (alexandria:read-stream-content-into-byte-vector f)))
;; => (#(1 33 7) <indeterminate octet array>)

;; There is also a Gray stream class for more complicated uses, which
;; `decompress' wraps. There's no need to close the decompression stream itself,
;; but any underlying stream must be closed by the user. The header information
;; can be queried with `decompression-stream-header'.
(let ((s (semz.decompress:make-decompression-stream
          :zlib #(120 156  99 84 100 7 0  0 79 0 42))))
  (list (alexandria:read-stream-content-into-byte-vector s)
        (semz.decompress:decompression-stream-header s)))
;; => (#(1 33 7) (:window-size 32768 :level 2 :dictionary nil))

;; Unlike many other libraries, this one supports zlib preset dictionaries.
(semz.decompress:decompress
 :zlib #(120 249  0 79 0 42  3 34 0  0 79 0 42)
 :dictionary (semz.decompress:make-simple-zlib-dictionary '(#(1 33 7))))
;; => #(1 33 7), (:window-size 32768 :level 3 :dictionary 5177386)
