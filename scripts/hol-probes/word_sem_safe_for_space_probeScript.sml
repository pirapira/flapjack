load "preamble"; load "wordSemTheory";
open HolKernel Parse bossLib preamble wordSemTheory;
val _ = Globals.linewidth := 1000000;
val th = wordSemTheory.word_lang_safe_for_space_def;
val _ = (print "word_lang_safe_for_space_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n");
val _ = print("word_lang_safe_for_space_def_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
