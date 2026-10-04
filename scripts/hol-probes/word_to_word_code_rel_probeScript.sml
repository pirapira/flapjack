load "word_to_wordProofTheory";
open HolKernel Parse bossLib word_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "code_rel_def_statement="; print_term(concl code_rel_def));
val _ = print("code_rel_def_hypotheses=" ^ Int.toString(length(hyp code_rel_def)) ^ "\n");
val _ = (print "code_rel_def_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl code_rel_def));
