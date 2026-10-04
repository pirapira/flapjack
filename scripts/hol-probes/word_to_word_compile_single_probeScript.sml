load "word_to_wordProofTheory";
open HolKernel Parse bossLib word_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "FST_compile_single_statement="; print_term(concl FST_compile_single));
val _ = print("FST_compile_single_hypotheses=" ^ Int.toString(length(hyp FST_compile_single)) ^ "\n");
val _ = (print "FST_compile_single_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl FST_compile_single));
val _ = (print "compile_single_lem_statement="; print_term(concl compile_single_lem));
val _ = print("compile_single_lem_hypotheses=" ^ Int.toString(length(hyp compile_single_lem)) ^ "\n");
val _ = (print "compile_single_lem_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl compile_single_lem));
