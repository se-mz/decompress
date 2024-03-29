(asdf:defsystem "semz.decompress"
  :description "A defensive and fast decompression library in pure CL."
  :version "1.2.0"
  :author "Sebastian Melzer <semz@semelz.de>"
  :maintainer "Sebastian Melzer <semz@semelz.de>"
  :licence "MIT"
  :homepage "https://semelz.de/software/decompress.html"
  :depends-on ("alexandria" "trivial-gray-streams")
  :components ((:file "common")
               (:file "tables" :depends-on ("common"))
               (:file "io" :depends-on ("common"))
               (:file "bits" :depends-on ("common" "io"))
               (:file "interface" :depends-on ("common" "io"))

               (:file "huffman" :depends-on ("common" "bits"))
               (:file "deflate" :depends-on ("common" "io" "bits" "huffman"))

               (:file "adler32" :depends-on ("common"))
               (:file "zlib" :depends-on ("common" "io" "bits" "deflate" "adler32"))

               (:file "crc" :depends-on ("common"))
               (:file "gzip" :depends-on ("common" "io" "bits" "deflate" "crc"))

               (:file "bzip2" :depends-on ("common" "bits" "huffman" "crc" "tables"))

               (:file "lzma" :depends-on ("common" "io"))
               (:file "lzma2" :depends-on ("common" "io" "lzma"))
               (:file "sha256" :depends-on ("common" "tables"))
               (:file "xz-bcj-filters" :depends-on ("common" "io"))
               (:file "xz" :depends-on ("common" "io" "lzma2" "xz-bcj-filters" "crc" "sha256"))))
