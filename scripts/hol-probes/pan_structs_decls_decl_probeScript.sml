load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsProofTheory panLangTheory;
val _ = Globals.linewidth := 1000000;
fun emit label th =
 (if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
  print(label ^ "="); print_term(concl th); print "\n");
val compile_decls_correct_full = GEN_ALL compile_decls_correct;
val _ = emit "compile_decls_correct_full_statement" compile_decls_correct_full;
val _ = print("compile_decls_correct_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO compile_decls_correct_full))) ^ "\n");
val _ = print("compile_decls_correct_full_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl compile_decls_correct_full)))) ^ "\n");
val compile_decls_correct_decl = GEN_ALL(Q.SPECL [`s`, `panLang$Decl sh v e :: ds`] compile_decls_correct);
val _ = emit "compile_decls_correct_decl_statement" compile_decls_correct_decl;
val _ = print("compile_decls_correct_decl_proved=" ^ term_to_string(rhs(concl(EQT_INTRO compile_decls_correct_decl))) ^ "\n");
val _ = print("compile_decls_correct_decl_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl compile_decls_correct_decl)))) ^ "\n");
val evaluate_decls_ind = GEN_ALL panSemTheory.evaluate_decls_ind;
val _ = emit "evaluate_decls_ind_statement" evaluate_decls_ind;
val _ = print("evaluate_decls_ind_proved=" ^ term_to_string(rhs(concl(EQT_INTRO evaluate_decls_ind))) ^ "\n");
val _ = print("evaluate_decls_ind_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl evaluate_decls_ind)))) ^ "\n");
