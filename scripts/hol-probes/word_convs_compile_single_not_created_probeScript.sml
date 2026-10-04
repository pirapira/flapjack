load "wordConvsProofTheory";
open HolKernel Parse bossLib wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "compile_single_not_created_subprogs_statement="; print_term(concl compile_single_not_created_subprogs));
val _ = print("compile_single_not_created_subprogs_hypotheses=" ^ Int.toString(length(hyp compile_single_not_created_subprogs)) ^ "\n");
val _ = (print "compile_single_not_created_subprogs_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl compile_single_not_created_subprogs));
