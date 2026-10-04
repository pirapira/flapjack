load "word_cseProofTheory";
open HolKernel Parse bossLib word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "comp_correct_statement="; print_term(concl comp_correct));
val _ = print("comp_correct_hypotheses=" ^ Int.toString(length(hyp comp_correct)) ^ "\n");
val _ = (print "word_common_subexp_elim_correct_statement="; print_term(concl word_common_subexp_elim_correct));
val _ = print("word_common_subexp_elim_correct_hypotheses=" ^ Int.toString(length(hyp word_common_subexp_elim_correct)) ^ "\n");
val _ = (print "comp_correct_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl comp_correct));
