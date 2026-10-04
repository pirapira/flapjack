load "word_to_wordProofTheory";
open HolKernel Parse bossLib word_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "compile_word_to_word_thm_statement="; print_term(concl compile_word_to_word_thm));
val _ = print("compile_word_to_word_thm_hypotheses=" ^ Int.toString(length(hyp compile_word_to_word_thm)) ^ "\n");
val _ = (print "compile_word_to_word_thm_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl compile_word_to_word_thm));
