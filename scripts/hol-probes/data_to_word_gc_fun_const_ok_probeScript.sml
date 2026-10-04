load "data_to_word_gcProofTheory";
open HolKernel Parse bossLib data_to_word_gcProofTheory;
val _ = Globals.linewidth := 1000000;
fun pr_stmt label th = (print (label ^ "="); print_term (concl th); print "\n");
fun pr_hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun pr_typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
val _ = pr_stmt "gc_fun_const_ok_word_gc_fun_statement" gc_fun_const_ok_word_gc_fun;
val _ = pr_hyps "gc_fun_const_ok_word_gc_fun_hypotheses" gc_fun_const_ok_word_gc_fun;
val _ = pr_typed "gc_fun_const_ok_word_gc_fun_typed" gc_fun_const_ok_word_gc_fun;
