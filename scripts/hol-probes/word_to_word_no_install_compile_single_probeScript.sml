load "word_to_wordProofTheory";
open HolKernel Parse bossLib word_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
fun pr_stmt label th = (print (label ^ "="); print_term (concl th); print "\n");
fun pr_hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun pr_typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
val _ = pr_stmt "no_install_no_alloc_compile_single_correct_statement" no_install_no_alloc_compile_single_correct;
val _ = pr_hyps "no_install_no_alloc_compile_single_correct_hypotheses" no_install_no_alloc_compile_single_correct;
val _ = pr_typed "no_install_no_alloc_compile_single_correct_typed" no_install_no_alloc_compile_single_correct;
