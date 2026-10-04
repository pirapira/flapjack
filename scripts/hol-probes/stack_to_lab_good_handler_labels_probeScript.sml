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


(* Exported originals of stack_to_labProofScript.sml:4537-4731. *)
val _ = checked "nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels_statement" nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels;
val _ = typed_statement "nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels_statement_typed" nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels;
val _ = type_list "nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels_statement_types" nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels;
val _ = checked "stack_names_stack_good_handler_labels_statement" stack_names_stack_good_handler_labels;
val _ = typed_statement "stack_names_stack_good_handler_labels_statement_typed" stack_names_stack_good_handler_labels;
val _ = type_list "stack_names_stack_good_handler_labels_statement_types" stack_names_stack_good_handler_labels;
val _ = checked "restrict_nonzero_union_statement" restrict_nonzero_union;
val _ = typed_statement "restrict_nonzero_union_statement_typed" restrict_nonzero_union;
val _ = type_list "restrict_nonzero_union_statement_types" restrict_nonzero_union;
val _ = checked "restrict_nonzero_IN_statement" restrict_nonzero_IN;
val _ = typed_statement "restrict_nonzero_IN_statement_typed" restrict_nonzero_IN;
val _ = type_list "restrict_nonzero_IN_statement_types" restrict_nonzero_IN;
val _ = checked "stack_good_handler_labels_append_statement" stack_good_handler_labels_append;
val _ = typed_statement "stack_good_handler_labels_append_statement_typed" stack_good_handler_labels_append;
val _ = type_list "stack_good_handler_labels_append_statement_types" stack_good_handler_labels_append;
val _ = checked "stack_remove_stack_good_handler_labels_incr_statement" stack_remove_stack_good_handler_labels_incr;
val _ = typed_statement "stack_remove_stack_good_handler_labels_incr_statement_typed" stack_remove_stack_good_handler_labels_incr;
val _ = type_list "stack_remove_stack_good_handler_labels_incr_statement_types" stack_remove_stack_good_handler_labels_incr;
val _ = checked "stack_remove_stack_good_handler_labels_statement" stack_remove_stack_good_handler_labels;
val _ = typed_statement "stack_remove_stack_good_handler_labels_statement_typed" stack_remove_stack_good_handler_labels;
val _ = type_list "stack_remove_stack_good_handler_labels_statement_types" stack_remove_stack_good_handler_labels;
val _ = checked "stack_alloc_stack_good_handler_labels_incr_statement" stack_alloc_stack_good_handler_labels_incr;
val _ = typed_statement "stack_alloc_stack_good_handler_labels_incr_statement_typed" stack_alloc_stack_good_handler_labels_incr;
val _ = type_list "stack_alloc_stack_good_handler_labels_incr_statement_types" stack_alloc_stack_good_handler_labels_incr;
val _ = checked "stack_alloc_stack_good_handler_labels_statement" stack_alloc_stack_good_handler_labels;
val _ = typed_statement "stack_alloc_stack_good_handler_labels_statement_typed" stack_alloc_stack_good_handler_labels;
val _ = type_list "stack_alloc_stack_good_handler_labels_statement_types" stack_alloc_stack_good_handler_labels;
val _ = checked "stack_rawcall_stack_good_handler_labels_statement" stack_rawcall_stack_good_handler_labels;
val _ = typed_statement "stack_rawcall_stack_good_handler_labels_statement_typed" stack_rawcall_stack_good_handler_labels;
val _ = type_list "stack_rawcall_stack_good_handler_labels_statement_types" stack_rawcall_stack_good_handler_labels;
val _ = checked "stack_to_lab_stack_good_handler_labels_statement" stack_to_lab_stack_good_handler_labels;
val _ = typed_statement "stack_to_lab_stack_good_handler_labels_statement_typed" stack_to_lab_stack_good_handler_labels;
val _ = type_list "stack_to_lab_stack_good_handler_labels_statement_types" stack_to_lab_stack_good_handler_labels;
val _ = checked "stack_to_lab_stack_good_handler_labels_incr_statement" stack_to_lab_stack_good_handler_labels_incr;
val _ = typed_statement "stack_to_lab_stack_good_handler_labels_incr_statement_typed" stack_to_lab_stack_good_handler_labels_incr;
val _ = type_list "stack_to_lab_stack_good_handler_labels_incr_statement_types" stack_to_lab_stack_good_handler_labels_incr;
