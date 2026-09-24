load "preamble";
load "stack_removeTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open stack_removeTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "max_stack_alloc" ``stack_remove$max_stack_alloc``;
val _ = print_eval "word_offset_3_8" ``stack_remove$word_offset (3n) : 8 word``;
val _ = print_eval "word_offset_3_64" ``stack_remove$word_offset (3n) : 64 word``;
val _ = print_eval "store_list_len" ``LENGTH (stack_remove$store_list : store_name list)``;
val _ = print_eval "store_list_head" ``HD (stack_remove$store_list : store_name list)``;
val _ = print_eval "store_list_last" ``LAST (stack_remove$store_list : store_name list)``;
val _ = print_eval "store_length" ``stack_remove$store_length``;
val _ = print_eval "stack_err_lab" ``stack_remove$stack_err_lab``;