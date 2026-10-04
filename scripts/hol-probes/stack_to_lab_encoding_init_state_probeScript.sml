load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory stack_namesProofTheory
 stack_allocProofTheory stack_removeProofTheory stack_to_labTheory stackSemTheory
 stackPropsTheory stack_allocTheory labSemTheory labPropsTheory semanticsPropsTheory;
val _ = Globals.linewidth := 1000000;
(* The script-local simpset changes of stack_to_labProofScript.sml:14-22. *)
val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");
fun typed_statement label th =
  (show_types := true;
   print (label ^ "="); print_term (concl th); print "\n";
   show_types := false);
fun type_list label th =
  (show_types := true;
   print (label ^ "=");
   app (fn v => print (term_to_string v ^ ":" ^ type_to_string (type_of v) ^ ";"))
     (fst (strip_forall (concl th)) @ free_vars (concl th));
   print "\n";
   show_types := false);


(* Exported originals of stack_to_labProofScript.sml:3620-3799 not covered elsewhere. *)
val _ = checked "EVERY_sec_ends_with_label_MAP_prog_to_section_statement" EVERY_sec_ends_with_label_MAP_prog_to_section;
val _ = typed_statement "EVERY_sec_ends_with_label_MAP_prog_to_section_statement_typed" EVERY_sec_ends_with_label_MAP_prog_to_section;
val _ = type_list "EVERY_sec_ends_with_label_MAP_prog_to_section_statement_types" EVERY_sec_ends_with_label_MAP_prog_to_section;
val _ = checked "full_make_init_has_fp_ops_statement" full_make_init_has_fp_ops;
val _ = typed_statement "full_make_init_has_fp_ops_statement_typed" full_make_init_has_fp_ops;
val _ = type_list "full_make_init_has_fp_ops_statement_types" full_make_init_has_fp_ops;
val _ = checked "stack_to_lab_compile_all_enc_ok_statement" stack_to_lab_compile_all_enc_ok;
val _ = typed_statement "stack_to_lab_compile_all_enc_ok_statement_typed" stack_to_lab_compile_all_enc_ok;
val _ = type_list "stack_to_lab_compile_all_enc_ok_statement_types" stack_to_lab_compile_all_enc_ok;
val _ = checked "IMP_init_store_ok_statement" IMP_init_store_ok;
val _ = typed_statement "IMP_init_store_ok_statement_typed" IMP_init_store_ok;
val _ = type_list "IMP_init_store_ok_statement_types" IMP_init_store_ok;
val _ = checked "IMP_init_state_ok_statement" IMP_init_state_ok;
val _ = typed_statement "IMP_init_state_ok_statement_typed" IMP_init_state_ok;
val _ = type_list "IMP_init_state_ok_statement_types" IMP_init_state_ok;
