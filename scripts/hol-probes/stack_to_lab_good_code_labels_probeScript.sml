load "preamble"; load "stack_to_labProofTheory"; load "stack_rawcallProofTheory";
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


(* Exported originals and local replays of stack_to_labProofScript.sml:4090-4536,
   plus stack_rawcallProofScript.sml stack_get_handler_labels_comp. *)
val get_code_labels_comp_4090 = Q.prove(
  `  !f p. complex_get_code_labels (stack_names$comp f p) = complex_get_code_labels p`,
  HO_MATCH_MP_TAC stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs [get_code_labels_def]
  \\ every_case_tac \\ fs [] \\
  fs[stack_namesTheory.dest_find_name_def]);
val get_code_labels_comp_4110 = Q.prove(
  `  !a b c p. get_code_labels (comp a b c p) SUBSET (stack_err_lab,0) INSERT get_code_labels p`,
  HO_MATCH_MP_TAC stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_removeTheory.comp_def]
  \\ rw[] \\ fs [get_code_labels_def,stackLangTheory.list_Seq_def,
                 stack_removeTheory.copy_loop_def,stack_removeTheory.copy_each_def]
  \\ every_case_tac \\ fs [] \\
  TRY(rw[]>>match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
  metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (
    completeInduct_on`n`>>
    ONCE_REWRITE_TAC [stack_removeTheory.stack_alloc_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_alloc_def]>>rw[]>>
    fs[get_code_labels_def]>>rw[]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]>>
    rw[]>>EVAL_TAC)
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    completeInduct_on`n`>>simp[Once stack_removeTheory.stack_free_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_free_def,get_code_labels_def]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_store_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_load_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]));
val init_stubs_labels = Q.prove(
  `  EVERY (λp. get_code_labels p SUBSET (set [(1n,0n);(start,0n)])) (MAP SND (init_stubs ggc mh k start))`,
  rpt(EVAL_TAC>>rw[]>>fs[]));
val stack_names_get_code_labels_comp = Q.prove(
  `  !f p. get_code_labels (stack_names$comp f p) = get_code_labels p`,
  HO_MATCH_MP_TAC stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs [get_code_labels_def]
  \\ every_case_tac \\ fs [] \\
  fs[stack_namesTheory.dest_find_name_def]);
val stack_names_stack_get_handler_labels_comp = Q.prove(
  `  !f p n.
  stack_get_handler_labels n (stack_names$comp f p) =
  stack_get_handler_labels n p`,
  HO_MATCH_MP_TAC stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs [stack_get_handler_labels_def]
  \\ every_case_tac \\ fs [] \\
  fs[stack_namesTheory.dest_find_name_def]);
val UNCURRY_PAIR_ETA = Q.prove(
  `  UNCURRY f = λ(p1,p2). f p1 p2`,
  fs[FUN_EQ_THM]);
val stack_remove_get_code_labels_comp = Q.prove(
  `  !a b c p.
  get_code_labels (comp a b c p) SUBSET (stack_err_lab,0) INSERT get_code_labels p`,
  HO_MATCH_MP_TAC stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_removeTheory.comp_def]
  \\ rw[] \\ fs [get_code_labels_def,stackLangTheory.list_Seq_def,
                 stack_removeTheory.copy_loop_def,stack_removeTheory.copy_each_def]
  \\ every_case_tac \\ fs [] \\
  TRY(rw[]>>match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
  metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (
    completeInduct_on`n`>>
    ONCE_REWRITE_TAC [stack_removeTheory.stack_alloc_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_alloc_def]>>rw[]>>
    fs[get_code_labels_def]>>rw[]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]>>
    rw[]>>EVAL_TAC)
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    completeInduct_on`n`>>simp[Once stack_removeTheory.stack_free_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_free_def,get_code_labels_def]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_store_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_load_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]));
val stack_remove_stack_get_handler_labels_comp = Q.prove(
  `  !a b c p m.
  stack_get_handler_labels m (comp a b c p) =
  stack_get_handler_labels m p`,
  HO_MATCH_MP_TAC stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_removeTheory.comp_def]
  \\ rw[] \\ fs [stack_get_handler_labels_def,stackLangTheory.list_Seq_def,
                 stack_removeTheory.copy_loop_def,stack_removeTheory.copy_each_def]
  \\ every_case_tac \\ fs []
  >- (
    completeInduct_on`n`>>
    ONCE_REWRITE_TAC [stack_removeTheory.stack_alloc_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_alloc_def]>>rw[]>>
    fs[stack_get_handler_labels_def]>>rw[]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]>>
    rw[]>>EVAL_TAC)
  >- (
    completeInduct_on`n`>>simp[Once stack_removeTheory.stack_free_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_free_def,stack_get_handler_labels_def]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_store_def]>>
    rw[stack_get_handler_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[stack_get_handler_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_load_def]>>
    rw[stack_get_handler_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[stack_get_handler_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]));
val stack_remove_init_code_labels = Q.prove(
  `  x ∈ get_code_labels (init_code ggc mh sp) ⇒ x = (1n,0n)`,
  rpt(EVAL_TAC>>rw[]>>fs[]));
val stack_alloc_get_code_labels_comp = Q.prove(
  `  !n m p pp mm.
  get_code_labels (FST (comp n m p)) ⊆ (gc_stub_location,0) INSERT get_code_labels p`,
  HO_MATCH_MP_TAC stack_allocTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_allocTheory.comp_def]
  \\ rw[] \\ fs [stack_get_handler_labels_def,stackLangTheory.list_Seq_def]
  \\ every_case_tac \\ fs []
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[SUBSET_DEF]>>metis_tac[]);
val stack_alloc_stack_get_handler_labels_comp = Q.prove(
  `  !n m p pp mm.
  stack_get_handler_labels i (FST (comp n m p)) = stack_get_handler_labels i p`,
  HO_MATCH_MP_TAC stack_allocTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_allocTheory.comp_def]
  \\ rw[] \\ fs [stack_get_handler_labels_def,stackLangTheory.list_Seq_def]
  \\ every_case_tac \\ fs []
  \\ rpt(pairarg_tac \\ fs[stack_get_handler_labels_def])
  \\ fs[stack_get_handler_labels_def]);
val stack_alloc_init_code_labels = Q.prove(
  `  get_code_labels (word_gc_code c) = {}`,
  simp[stack_allocTheory.word_gc_code_def]>>
  EVAL_TAC>>
  EVERY_CASE_TAC>>fs[]>>
  rpt(EVAL_TAC>>rw[]>>fs[]));

val _ = checked "get_code_labels_comp_4090_statement" get_code_labels_comp_4090;
val _ = typed_statement "get_code_labels_comp_4090_statement_typed" get_code_labels_comp_4090;
val _ = type_list "get_code_labels_comp_4090_statement_types" get_code_labels_comp_4090;
val _ = checked "stack_names_get_code_labels_statement" stack_names_get_code_labels;
val _ = typed_statement "stack_names_get_code_labels_statement_typed" stack_names_get_code_labels;
val _ = type_list "stack_names_get_code_labels_statement_types" stack_names_get_code_labels;
val _ = checked "get_code_labels_comp_4110_statement" get_code_labels_comp_4110;
val _ = typed_statement "get_code_labels_comp_4110_statement_typed" get_code_labels_comp_4110;
val _ = type_list "get_code_labels_comp_4110_statement_types" get_code_labels_comp_4110;
val _ = checked "init_stubs_labels_statement" init_stubs_labels;
val _ = typed_statement "init_stubs_labels_statement_typed" init_stubs_labels;
val _ = type_list "init_stubs_labels_statement_types" init_stubs_labels;
val _ = checked "stack_names_get_code_labels_comp_statement" stack_names_get_code_labels_comp;
val _ = typed_statement "stack_names_get_code_labels_comp_statement_typed" stack_names_get_code_labels_comp;
val _ = type_list "stack_names_get_code_labels_comp_statement_types" stack_names_get_code_labels_comp;
val _ = checked "stack_names_stack_get_handler_labels_comp_statement" stack_names_stack_get_handler_labels_comp;
val _ = typed_statement "stack_names_stack_get_handler_labels_comp_statement_typed" stack_names_stack_get_handler_labels_comp;
val _ = type_list "stack_names_stack_get_handler_labels_comp_statement_types" stack_names_stack_get_handler_labels_comp;
val _ = checked "UNCURRY_PAIR_ETA_statement" UNCURRY_PAIR_ETA;
val _ = typed_statement "UNCURRY_PAIR_ETA_statement_typed" UNCURRY_PAIR_ETA;
val _ = type_list "UNCURRY_PAIR_ETA_statement_types" UNCURRY_PAIR_ETA;
val _ = checked "stack_names_stack_good_code_labels_statement" stack_names_stack_good_code_labels;
val _ = typed_statement "stack_names_stack_good_code_labels_statement_typed" stack_names_stack_good_code_labels;
val _ = type_list "stack_names_stack_good_code_labels_statement_types" stack_names_stack_good_code_labels;
val _ = checked "stack_remove_get_code_labels_comp_statement" stack_remove_get_code_labels_comp;
val _ = typed_statement "stack_remove_get_code_labels_comp_statement_typed" stack_remove_get_code_labels_comp;
val _ = type_list "stack_remove_get_code_labels_comp_statement_types" stack_remove_get_code_labels_comp;
val _ = checked "stack_remove_stack_get_handler_labels_comp_statement" stack_remove_stack_get_handler_labels_comp;
val _ = typed_statement "stack_remove_stack_get_handler_labels_comp_statement_typed" stack_remove_stack_get_handler_labels_comp;
val _ = type_list "stack_remove_stack_get_handler_labels_comp_statement_types" stack_remove_stack_get_handler_labels_comp;
val _ = checked "stack_remove_init_code_labels_statement" stack_remove_init_code_labels;
val _ = typed_statement "stack_remove_init_code_labels_statement_typed" stack_remove_init_code_labels;
val _ = type_list "stack_remove_init_code_labels_statement_types" stack_remove_init_code_labels;
val _ = checked "stack_remove_stack_good_code_labels_statement" stack_remove_stack_good_code_labels;
val _ = typed_statement "stack_remove_stack_good_code_labels_statement_typed" stack_remove_stack_good_code_labels;
val _ = type_list "stack_remove_stack_good_code_labels_statement_types" stack_remove_stack_good_code_labels;
val _ = checked "stack_remove_stack_good_code_labels_incr_statement" stack_remove_stack_good_code_labels_incr;
val _ = typed_statement "stack_remove_stack_good_code_labels_incr_statement_typed" stack_remove_stack_good_code_labels_incr;
val _ = type_list "stack_remove_stack_good_code_labels_incr_statement_types" stack_remove_stack_good_code_labels_incr;
val _ = checked "stack_alloc_get_code_labels_comp_statement" stack_alloc_get_code_labels_comp;
val _ = typed_statement "stack_alloc_get_code_labels_comp_statement_typed" stack_alloc_get_code_labels_comp;
val _ = type_list "stack_alloc_get_code_labels_comp_statement_types" stack_alloc_get_code_labels_comp;
val _ = checked "stack_alloc_stack_get_handler_labels_comp_statement" stack_alloc_stack_get_handler_labels_comp;
val _ = typed_statement "stack_alloc_stack_get_handler_labels_comp_statement_typed" stack_alloc_stack_get_handler_labels_comp;
val _ = type_list "stack_alloc_stack_get_handler_labels_comp_statement_types" stack_alloc_stack_get_handler_labels_comp;
val _ = checked "stack_alloc_init_code_labels_statement" stack_alloc_init_code_labels;
val _ = typed_statement "stack_alloc_init_code_labels_statement_typed" stack_alloc_init_code_labels;
val _ = type_list "stack_alloc_init_code_labels_statement_types" stack_alloc_init_code_labels;
val _ = checked "stack_alloc_stack_good_code_labels_statement" stack_alloc_stack_good_code_labels;
val _ = typed_statement "stack_alloc_stack_good_code_labels_statement_typed" stack_alloc_stack_good_code_labels;
val _ = type_list "stack_alloc_stack_good_code_labels_statement_types" stack_alloc_stack_good_code_labels;
val _ = checked "stack_alloc_stack_good_code_labels_incr_statement" stack_alloc_stack_good_code_labels_incr;
val _ = typed_statement "stack_alloc_stack_good_code_labels_incr_statement_typed" stack_alloc_stack_good_code_labels_incr;
val _ = type_list "stack_alloc_stack_good_code_labels_incr_statement_types" stack_alloc_stack_good_code_labels_incr;
val _ = checked "IN_get_code_labels_comp_top_lemma_statement" IN_get_code_labels_comp_top_lemma;
val _ = typed_statement "IN_get_code_labels_comp_top_lemma_statement_typed" IN_get_code_labels_comp_top_lemma;
val _ = type_list "IN_get_code_labels_comp_top_lemma_statement_types" IN_get_code_labels_comp_top_lemma;
val _ = checked "IN_domain_collect_info_statement" IN_domain_collect_info;
val _ = typed_statement "IN_domain_collect_info_statement_typed" IN_domain_collect_info;
val _ = type_list "IN_domain_collect_info_statement_types" IN_domain_collect_info;
val _ = checked "IN_get_code_labels_comp_top_statement" IN_get_code_labels_comp_top;
val _ = typed_statement "IN_get_code_labels_comp_top_statement_typed" IN_get_code_labels_comp_top;
val _ = type_list "IN_get_code_labels_comp_top_statement_types" IN_get_code_labels_comp_top;
val _ = checked "stack_rawcall_stack_good_code_labels_statement" stack_rawcall_stack_good_code_labels;
val _ = typed_statement "stack_rawcall_stack_good_code_labels_statement_typed" stack_rawcall_stack_good_code_labels;
val _ = type_list "stack_rawcall_stack_good_code_labels_statement_types" stack_rawcall_stack_good_code_labels;
val _ = checked "stack_to_lab_stack_good_code_labels_statement" stack_to_lab_stack_good_code_labels;
val _ = typed_statement "stack_to_lab_stack_good_code_labels_statement_typed" stack_to_lab_stack_good_code_labels;
val _ = type_list "stack_to_lab_stack_good_code_labels_statement_types" stack_to_lab_stack_good_code_labels;
val _ = checked "stack_to_lab_stack_good_code_labels_incr_statement" stack_to_lab_stack_good_code_labels_incr;
val _ = typed_statement "stack_to_lab_stack_good_code_labels_incr_statement_typed" stack_to_lab_stack_good_code_labels_incr;
val _ = type_list "stack_to_lab_stack_good_code_labels_incr_statement_types" stack_to_lab_stack_good_code_labels_incr;
val _ = checked "rawcall_stack_get_handler_labels_comp_statement" stack_rawcallProofTheory.stack_get_handler_labels_comp;
val _ = typed_statement "rawcall_stack_get_handler_labels_comp_statement_typed" stack_rawcallProofTheory.stack_get_handler_labels_comp;
val _ = type_list "rawcall_stack_get_handler_labels_comp_statement_types" stack_rawcallProofTheory.stack_get_handler_labels_comp;
