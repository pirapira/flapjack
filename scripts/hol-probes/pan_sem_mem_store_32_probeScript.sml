load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val m0 = ``(\(_ : 64 word). Word (0w : 64 word)) : 64 word -> 64 word_lab``;
val dom0 = ``{(0w : 64 word)} : 64 word set``;
val domEmpty = ``({} : 64 word set)``;
val v32 = ``(0x11223344w : word32)``;

val _ = print_eval "ms32_aligned"
  ``(case mem_store_32 ^m0 ^dom0 F (0w : 64 word) ^v32 of SOME m => m (0w : 64 word) | NONE => Word (0w : 64 word))``;
val _ = print_eval "ms32_aligned4"
  ``(case mem_store_32 ^m0 ^dom0 F (4w : 64 word) ^v32 of SOME m => m (0w : 64 word) | NONE => Word (0w : 64 word))``;
val _ = print_eval "ms32_unaligned"
  ``(case mem_store_32 ^m0 ^dom0 F (2w : 64 word) ^v32 of SOME m => m (0w : 64 word) | NONE => Word (0w : 64 word))``;
val _ = print_eval "ms32_outside_domain"
  ``(case mem_store_32 ^m0 ^domEmpty F (0w : 64 word) ^v32 of SOME m => m (0w : 64 word) | NONE => Word (0w : 64 word))``;
val _ = print_eval "ms32_bigendian"
  ``(case mem_store_32 ^m0 ^dom0 T (0w : 64 word) ^v32 of SOME m => m (0w : 64 word) | NONE => Word (0w : 64 word))``;
val _ = print_eval "ms32_other_cell"
  ``(case mem_store_32 ^m0 ^dom0 F (0w : 64 word) ^v32 of SOME m => m (8w : 64 word) | NONE => Word (0w : 64 word))``;