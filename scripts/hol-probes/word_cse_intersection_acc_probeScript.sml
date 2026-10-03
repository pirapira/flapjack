load "word_cseProofTheory";
open HolKernel Parse bossLib word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "bm_inter_eq_acc_thm_statement="; print_term(concl bm_inter_eq_acc_thm));
val _ = print("bm_inter_eq_acc_thm_hypotheses=" ^ Int.toString(length(hyp bm_inter_eq_acc_thm)) ^ "\n");
val _ = (print "lookup_bm_inter_eq_statement="; print_term(concl lookup_bm_inter_eq));
val _ = print("lookup_bm_inter_eq_hypotheses=" ^ Int.toString(length(hyp lookup_bm_inter_eq)) ^ "\n");
val _ = (print "bm_inter_eq_acc_thm_typed="; Lib.with_flag (Globals.show_types, true) print_term (concl bm_inter_eq_acc_thm));
