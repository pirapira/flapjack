(* Direct HOL4 probes for the imported generic word byte operations. *)
load "bossLib";
load "byteTheory";
open bossLib;
open HolKernel Parse;

fun print_thm label th =
  (print (label ^ "="); print_term (concl th); print "\n")

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (concl th); print "\n"
  end

val _ = print_thm "byte_index_definition" byteTheory.byte_index_def;
val _ = print_thm "get_byte_definition" byteTheory.get_byte_def;
val _ = print_thm "set_byte_definition" byteTheory.set_byte_def;
val _ = print_thm "word_of_bytes_definition" byteTheory.word_of_bytes_def;

val _ = print_eval "word_of_bytes_width17_little"
  ``word_of_bytes F (0w:17 word)
      [0x11w:word8; 0x32w:word8; 0x11w:word8; 0x32w:word8]``;
val _ = print_eval "word_of_bytes_width17_big"
  ``word_of_bytes T (0w:17 word)
      [0x32w:word8; 0x11w:word8; 0x32w:word8; 0x11w:word8]``;
