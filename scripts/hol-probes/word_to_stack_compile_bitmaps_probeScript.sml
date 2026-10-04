load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val th = word_to_stackProofTheory.compile_word_to_stack_bitmaps;
val _ = (print "compile_word_to_stack_bitmaps_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n");
val _ = print("compile_word_to_stack_bitmaps_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = print("compile_word_to_stack_bitmaps_free=" ^ Int.toString(length(free_vars(concl th))) ^ "\n");
