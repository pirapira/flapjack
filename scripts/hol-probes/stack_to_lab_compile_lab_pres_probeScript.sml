load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory stack_namesProofTheory
 stack_allocProofTheory stack_removeProofTheory stack_to_labTheory stackSemTheory
 stackPropsTheory stack_allocTheory labSemTheory labPropsTheory semanticsPropsTheory;
val _ = Globals.linewidth := 1000000;
(* Full original inferred carriers remain visible in every captured statement. *)
val _ = show_types := true;
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

(* Exported originals and local replays of stack_to_labProofScript.sml:3194-3347. *)
val MAP_FST_compile_compile = Q.prove(
  `MAP FST (compile jump off gen max_heap k InitGlobals_location
              (stack_alloc$compile c
                 (stack_rawcall$compile code))) =
    0::1::2::gc_stub_location::MAP FST code`,
  fs [stack_removeTheory.compile_def,stack_removeTheory.init_stubs_def,
      stack_allocTheory.compile_def,stack_rawcallTheory.compile_def,
      stack_allocTheory.stubs_def,stack_removeTheory.prog_comp_def]
  \\ rename [`comp_top ii`]
  \\ Induct_on `code` \\ fs []
  \\ fs [stack_removeTheory.prog_comp_def,FORALL_PROD,
         stack_allocTheory.prog_comp_def]);
val _ = checked "MAP_FST_compile_compile_statement" MAP_FST_compile_compile;
val _ = checked "next_lab_non_zero_3211_statement" stack_to_labProofTheory.next_lab_non_zero;
val MAP_prog_to_section_FST = Q.prove(
  `  MAP (λs. case s of Section n v => n) (MAP prog_to_section prog) =
  MAP FST prog`,
  match_mp_tac LIST_EQ>>rw[EL_MAP]>>Cases_on`EL x prog`>>fs[prog_to_section_def]>>
  pairarg_tac>>fs[]);
val _ = checked "MAP_prog_to_section_FST_3272_statement" MAP_prog_to_section_FST;
val extract_label_store_list_code = Q.prove(
  `  ∀a t ls.
  extract_labels (store_list_code a t ls) = []`,
  ho_match_mp_tac stack_removeTheory.store_list_code_ind>>
  EVAL_TAC>>fs[]);
val _ = checked "extract_label_store_list_code_statement" extract_label_store_list_code;
val _ = checked "stack_to_lab_compile_lab_pres_statement" stack_to_labProofTheory.stack_to_lab_compile_lab_pres;
