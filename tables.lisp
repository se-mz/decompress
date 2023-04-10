;;;; Tables
;;;
;;; I usually try to avoid hardcoding big tables, but alas. Each table is
;;; generated from the exact listing in the relevant specification or reference
;;; implementation. The comment tells you where precisely it can be found; diff
;;; the listed source with this file to verify that the table is correct.
(cl:in-package #:semz.decompress)

;;; bzip2: crctable.c
(define-constant +bzip2-crc-table+
    (let ((src "
   0x00000000L, 0x04c11db7L, 0x09823b6eL, 0x0d4326d9L,
   0x130476dcL, 0x17c56b6bL, 0x1a864db2L, 0x1e475005L,
   0x2608edb8L, 0x22c9f00fL, 0x2f8ad6d6L, 0x2b4bcb61L,
   0x350c9b64L, 0x31cd86d3L, 0x3c8ea00aL, 0x384fbdbdL,
   0x4c11db70L, 0x48d0c6c7L, 0x4593e01eL, 0x4152fda9L,
   0x5f15adacL, 0x5bd4b01bL, 0x569796c2L, 0x52568b75L,
   0x6a1936c8L, 0x6ed82b7fL, 0x639b0da6L, 0x675a1011L,
   0x791d4014L, 0x7ddc5da3L, 0x709f7b7aL, 0x745e66cdL,
   0x9823b6e0L, 0x9ce2ab57L, 0x91a18d8eL, 0x95609039L,
   0x8b27c03cL, 0x8fe6dd8bL, 0x82a5fb52L, 0x8664e6e5L,
   0xbe2b5b58L, 0xbaea46efL, 0xb7a96036L, 0xb3687d81L,
   0xad2f2d84L, 0xa9ee3033L, 0xa4ad16eaL, 0xa06c0b5dL,
   0xd4326d90L, 0xd0f37027L, 0xddb056feL, 0xd9714b49L,
   0xc7361b4cL, 0xc3f706fbL, 0xceb42022L, 0xca753d95L,
   0xf23a8028L, 0xf6fb9d9fL, 0xfbb8bb46L, 0xff79a6f1L,
   0xe13ef6f4L, 0xe5ffeb43L, 0xe8bccd9aL, 0xec7dd02dL,
   0x34867077L, 0x30476dc0L, 0x3d044b19L, 0x39c556aeL,
   0x278206abL, 0x23431b1cL, 0x2e003dc5L, 0x2ac12072L,
   0x128e9dcfL, 0x164f8078L, 0x1b0ca6a1L, 0x1fcdbb16L,
   0x018aeb13L, 0x054bf6a4L, 0x0808d07dL, 0x0cc9cdcaL,
   0x7897ab07L, 0x7c56b6b0L, 0x71159069L, 0x75d48ddeL,
   0x6b93dddbL, 0x6f52c06cL, 0x6211e6b5L, 0x66d0fb02L,
   0x5e9f46bfL, 0x5a5e5b08L, 0x571d7dd1L, 0x53dc6066L,
   0x4d9b3063L, 0x495a2dd4L, 0x44190b0dL, 0x40d816baL,
   0xaca5c697L, 0xa864db20L, 0xa527fdf9L, 0xa1e6e04eL,
   0xbfa1b04bL, 0xbb60adfcL, 0xb6238b25L, 0xb2e29692L,
   0x8aad2b2fL, 0x8e6c3698L, 0x832f1041L, 0x87ee0df6L,
   0x99a95df3L, 0x9d684044L, 0x902b669dL, 0x94ea7b2aL,
   0xe0b41de7L, 0xe4750050L, 0xe9362689L, 0xedf73b3eL,
   0xf3b06b3bL, 0xf771768cL, 0xfa325055L, 0xfef34de2L,
   0xc6bcf05fL, 0xc27dede8L, 0xcf3ecb31L, 0xcbffd686L,
   0xd5b88683L, 0xd1799b34L, 0xdc3abdedL, 0xd8fba05aL,
   0x690ce0eeL, 0x6dcdfd59L, 0x608edb80L, 0x644fc637L,
   0x7a089632L, 0x7ec98b85L, 0x738aad5cL, 0x774bb0ebL,
   0x4f040d56L, 0x4bc510e1L, 0x46863638L, 0x42472b8fL,
   0x5c007b8aL, 0x58c1663dL, 0x558240e4L, 0x51435d53L,
   0x251d3b9eL, 0x21dc2629L, 0x2c9f00f0L, 0x285e1d47L,
   0x36194d42L, 0x32d850f5L, 0x3f9b762cL, 0x3b5a6b9bL,
   0x0315d626L, 0x07d4cb91L, 0x0a97ed48L, 0x0e56f0ffL,
   0x1011a0faL, 0x14d0bd4dL, 0x19939b94L, 0x1d528623L,
   0xf12f560eL, 0xf5ee4bb9L, 0xf8ad6d60L, 0xfc6c70d7L,
   0xe22b20d2L, 0xe6ea3d65L, 0xeba91bbcL, 0xef68060bL,
   0xd727bbb6L, 0xd3e6a601L, 0xdea580d8L, 0xda649d6fL,
   0xc423cd6aL, 0xc0e2d0ddL, 0xcda1f604L, 0xc960ebb3L,
   0xbd3e8d7eL, 0xb9ff90c9L, 0xb4bcb610L, 0xb07daba7L,
   0xae3afba2L, 0xaafbe615L, 0xa7b8c0ccL, 0xa379dd7bL,
   0x9b3660c6L, 0x9ff77d71L, 0x92b45ba8L, 0x9675461fL,
   0x8832161aL, 0x8cf30badL, 0x81b02d74L, 0x857130c3L,
   0x5d8a9099L, 0x594b8d2eL, 0x5408abf7L, 0x50c9b640L,
   0x4e8ee645L, 0x4a4ffbf2L, 0x470cdd2bL, 0x43cdc09cL,
   0x7b827d21L, 0x7f436096L, 0x7200464fL, 0x76c15bf8L,
   0x68860bfdL, 0x6c47164aL, 0x61043093L, 0x65c52d24L,
   0x119b4be9L, 0x155a565eL, 0x18197087L, 0x1cd86d30L,
   0x029f3d35L, 0x065e2082L, 0x0b1d065bL, 0x0fdc1becL,
   0x3793a651L, 0x3352bbe6L, 0x3e119d3fL, 0x3ad08088L,
   0x2497d08dL, 0x2056cd3aL, 0x2d15ebe3L, 0x29d4f654L,
   0xc5a92679L, 0xc1683bceL, 0xcc2b1d17L, 0xc8ea00a0L,
   0xd6ad50a5L, 0xd26c4d12L, 0xdf2f6bcbL, 0xdbee767cL,
   0xe3a1cbc1L, 0xe760d676L, 0xea23f0afL, 0xeee2ed18L,
   0xf0a5bd1dL, 0xf464a0aaL, 0xf9278673L, 0xfde69bc4L,
   0x89b8fd09L, 0x8d79e0beL, 0x803ac667L, 0x84fbdbd0L,
   0x9abc8bd5L, 0x9e7d9662L, 0x933eb0bbL, 0x97ffad0cL,
   0xafb010b1L, 0xab710d06L, 0xa6322bdfL, 0xa2f33668L,
   0xbcb4666dL, 0xb8757bdaL, 0xb5365d03L, 0xb1f740b4L
"))
      (map '(simple-array (unsigned-byte 32) (*))
           (lambda (s e)
             (parse-integer src :start (+ s 1) :end e :radix 16))
           (positions #\x src)
           (positions #\L src))
      )
  :test 'equalp)

;;; bzip2: randtable.c (trailing whitespace is intentional)
(declaim (type (simple-array (unsigned-byte 32) (512)) +bzip2-random-numbers+))
(define-constant +bzip2-random-numbers+
    (let ((src "
   619, 720, 127, 481, 931, 816, 813, 233, 566, 247, 
   985, 724, 205, 454, 863, 491, 741, 242, 949, 214, 
   733, 859, 335, 708, 621, 574, 73, 654, 730, 472, 
   419, 436, 278, 496, 867, 210, 399, 680, 480, 51, 
   878, 465, 811, 169, 869, 675, 611, 697, 867, 561, 
   862, 687, 507, 283, 482, 129, 807, 591, 733, 623, 
   150, 238, 59, 379, 684, 877, 625, 169, 643, 105, 
   170, 607, 520, 932, 727, 476, 693, 425, 174, 647, 
   73, 122, 335, 530, 442, 853, 695, 249, 445, 515, 
   909, 545, 703, 919, 874, 474, 882, 500, 594, 612, 
   641, 801, 220, 162, 819, 984, 589, 513, 495, 799, 
   161, 604, 958, 533, 221, 400, 386, 867, 600, 782, 
   382, 596, 414, 171, 516, 375, 682, 485, 911, 276, 
   98, 553, 163, 354, 666, 933, 424, 341, 533, 870, 
   227, 730, 475, 186, 263, 647, 537, 686, 600, 224, 
   469, 68, 770, 919, 190, 373, 294, 822, 808, 206, 
   184, 943, 795, 384, 383, 461, 404, 758, 839, 887, 
   715, 67, 618, 276, 204, 918, 873, 777, 604, 560, 
   951, 160, 578, 722, 79, 804, 96, 409, 713, 940, 
   652, 934, 970, 447, 318, 353, 859, 672, 112, 785, 
   645, 863, 803, 350, 139, 93, 354, 99, 820, 908, 
   609, 772, 154, 274, 580, 184, 79, 626, 630, 742, 
   653, 282, 762, 623, 680, 81, 927, 626, 789, 125, 
   411, 521, 938, 300, 821, 78, 343, 175, 128, 250, 
   170, 774, 972, 275, 999, 639, 495, 78, 352, 126, 
   857, 956, 358, 619, 580, 124, 737, 594, 701, 612, 
   669, 112, 134, 694, 363, 992, 809, 743, 168, 974, 
   944, 375, 748, 52, 600, 747, 642, 182, 862, 81, 
   344, 805, 988, 739, 511, 655, 814, 334, 249, 515, 
   897, 955, 664, 981, 649, 113, 974, 459, 893, 228, 
   433, 837, 553, 268, 926, 240, 102, 654, 459, 51, 
   686, 754, 806, 760, 493, 403, 415, 394, 687, 700, 
   946, 670, 656, 610, 738, 392, 760, 799, 887, 653, 
   978, 321, 576, 617, 626, 502, 894, 679, 243, 440, 
   680, 879, 194, 572, 640, 724, 926, 56, 204, 700, 
   707, 151, 457, 449, 797, 195, 791, 558, 945, 679, 
   297, 59, 87, 824, 713, 663, 412, 693, 342, 606, 
   134, 108, 571, 364, 631, 212, 174, 643, 304, 329, 
   343, 97, 430, 751, 497, 314, 983, 374, 822, 928, 
   140, 206, 73, 263, 980, 736, 876, 478, 430, 305, 
   170, 514, 364, 692, 829, 82, 855, 953, 676, 246, 
   369, 970, 294, 750, 807, 827, 150, 790, 288, 923, 
   804, 378, 215, 828, 592, 281, 565, 555, 710, 82, 
   896, 831, 547, 261, 524, 462, 293, 465, 502, 56, 
   661, 821, 976, 991, 658, 869, 905, 758, 745, 193, 
   768, 550, 608, 933, 378, 286, 215, 979, 792, 961, 
   61, 688, 793, 644, 986, 403, 106, 366, 905, 644, 
   372, 567, 466, 434, 645, 210, 389, 550, 919, 135, 
   780, 773, 635, 389, 707, 100, 626, 958, 165, 504, 
   920, 176, 193, 713, 857, 265, 203, 50, 668, 108, 
   645, 990, 626, 197, 510, 357, 358, 850, 858, 364, 
   936, 638
"))
      (map '(simple-array (unsigned-byte 32) (*))
           (lambda (end)
             (parse-integer src
                            :start (+ 1 (position-if-not #'digit-char-p src
                                                         :end end :from-end t))
                            :end end))
           (append (positions #\, src)
                   (list (+ 1 (position-if #'digit-char-p src :from-end t))))))
  :test 'equalp)
