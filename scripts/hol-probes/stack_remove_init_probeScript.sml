load "preamble";
load "stack_removeProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open stack_removeProofTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "is_word_some" ``is_SOME_Word (SOME (Word (7w:8 word)))``;
val _ = print_eval "is_word_loc" ``is_SOME_Word (SOME (Loc 1 2))``;
val _ = print_eval "is_word_none" ``is_SOME_Word NONE``;
val _ = print_eval "read_mem_len" ``LENGTH (read_mem (0w:8 word) (\x. Word x) 3)``;
val _ = print_eval "read_mem_val" ``HD (read_mem (2w:8 word) (\x. Word (x + 1w)) 3)``;
val _ = print_eval "in_addr_self" ``(0w:8 word) IN addresses (0w:8 word) 3``;
val _ = print_eval "in_addr_step" ``(2w:8 word) IN addresses (0w:8 word) 3``;
val _ = print_eval "in_addr_out" ``(5w:8 word) IN addresses (0w:8 word) 3``;