(* Direct HOL4 probes for the imported generic word byte operations. *)
load "bossLib";
load "byteTheory";
load "wordsLib";
load "arithmeticTheory";
open bossLib;
open HolKernel Parse;

fun print_thm label th =
  (print (label ^ "="); print_term (concl th); print "\n")

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (concl th); print "\n"
  end

fun print_simp label q =
  let
    val rec_th = SIMP_CONV (srw_ss()) [byteTheory.word_of_bytes_def,
      byteTheory.set_byte_bit_field_insert] q
    val (_, rec_rhs) = dest_eq (concl rec_th)
    val th = EVAL rec_rhs
  in
    print (label ^ "="); print_term (concl th); print "\n"
  end

val _ = print_thm "byte_index_definition" byteTheory.byte_index_def;
val _ = print_thm "get_byte_definition" byteTheory.get_byte_def;
val _ = print_thm "set_byte_definition" byteTheory.set_byte_def;
val _ = print_thm "word_of_bytes_definition" byteTheory.word_of_bytes_def;
val _ = print_thm "natural_mod_zero_theorem" arithmeticTheory.MOD_0;
val _ = print_eval "byte_index_width5_little"
  ``byte_index (1w:5 word) F``;
val _ = print_eval "byte_index_width5_big"
  ``byte_index (1w:5 word) T``;
val _ = print_eval "get_byte_width5_little"
  ``get_byte (1w:5 word) (31w:5 word) F``;
val _ = print_eval "get_byte_width5_big"
  ``get_byte (1w:5 word) (31w:5 word) T``;

val _ = print_eval "word_of_bytes_width17_little"
  ``word_of_bytes F (0w:17 word)
      [0x11w:word8; 0x32w:word8; 0x11w:word8; 0x32w:word8]``;
val _ = print_eval "word_of_bytes_width17_big"
  ``word_of_bytes T (0w:17 word)
      [0x32w:word8; 0x11w:word8; 0x32w:word8; 0x11w:word8]``;
val _ = print_simp "word_of_bytes_width17_little_numeric"
  ``word_of_bytes F (0w:17 word)
      [0x11w:word8; 0x32w:word8; 0x11w:word8; 0x32w:word8]``;
val _ = print_simp "word_of_bytes_width17_big_numeric"
  ``word_of_bytes T (0w:17 word)
      [0x32w:word8; 0x11w:word8; 0x32w:word8; 0x11w:word8]``;
