load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val m0 = ``(\(_ : 64 word). Word (0w : 64 word)) : 64 word -> 64 word_lab``;
val dm0 = ``{(0w : 64 word); (8w : 64 word)} : 64 word set``;
val dmOnly0 = ``{(0w : 64 word)} : 64 word set``;

(* mem_store: in-domain replace vs out-of-domain failure *)
val _ = print_eval "ms_hit_lookup"
  ``(case mem_store (0w : 64 word) (Word (7w : 64 word)) ^dm0 ^m0 of
        SOME m => SOME (m (0w : 64 word)) | NONE => NONE) : 64 word_lab option``;
val _ = print_eval "ms_hit_other"
  ``(case mem_store (0w : 64 word) (Word (7w : 64 word)) ^dm0 ^m0 of
        SOME m => SOME (m (4w : 64 word)) | NONE => NONE) : 64 word_lab option``;
val _ = print_eval "ms_miss"
  ``(case mem_store (9w : 64 word) (Word (7w : 64 word)) ^dm0 ^m0 of
        SOME m => SOME (m (9w : 64 word)) | NONE => NONE) : 64 word_lab option``;

(* mem_stores: stride is bytes_in_word = 8w for 64-bit words *)
val _ = print_eval "mss_two"
  ``(case mem_stores (0w : 64 word) [Word (1w : 64 word); Word (2w : 64 word)] ^dm0 ^m0 of
        SOME m => SOME (m (0w : 64 word), m (8w : 64 word)) | NONE => NONE)
      : (64 word_lab # 64 word_lab) option``;
val _ = print_eval "mss_empty_lookup"
  ``(case mem_stores (0w : 64 word) [] ^dm0 ^m0 of
        SOME m => SOME (m (3w : 64 word)) | NONE => NONE) : 64 word_lab option``;
val _ = print_eval "mss_second_miss"
  ``(case mem_stores (0w : 64 word) [Word (1w : 64 word); Word (2w : 64 word)]
        ^dmOnly0 ^m0 of
        SOME m => SOME (m (8w : 64 word)) | NONE => NONE) : 64 word_lab option``;