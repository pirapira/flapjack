load "word_allocProofTheory";
open HolKernel Parse bossLib word_allocProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "ssa_cc_trans_distinct_tar_reg_statement="; print_term(concl ssa_cc_trans_distinct_tar_reg));
val _ = print("ssa_cc_trans_distinct_tar_reg_hypotheses=" ^ Int.toString(length(hyp ssa_cc_trans_distinct_tar_reg)) ^ "\n");
val _ = (print "ssa_cc_trans_distinct_tar_reg_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl ssa_cc_trans_distinct_tar_reg));
val _ = (print "full_ssa_cc_trans_distinct_tar_reg_statement="; print_term(concl full_ssa_cc_trans_distinct_tar_reg));
val _ = print("full_ssa_cc_trans_distinct_tar_reg_hypotheses=" ^ Int.toString(length(hyp full_ssa_cc_trans_distinct_tar_reg)) ^ "\n");
val _ = (print "full_ssa_cc_trans_distinct_tar_reg_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl full_ssa_cc_trans_distinct_tar_reg));
