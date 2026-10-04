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

(* Exported originals and local replays of stack_to_labProofScript.sml:3800-4089. *)
val complex_flatten_labels = Q.prove(
  `  ∀t p n m cs bs.
  let pp = set(append (FST (flatten t p n m cs bs))) in
  BIGUNION (IMAGE line_get_labels pp)
  ⊆
  (n,0) INSERT
  (n,if t /\ ?p1 p2. p = Seq p1 p2 then 1 else 0) INSERT
  set (MAP (λl. (n,l)) (cs ++ bs)) ∪
  IMAGE (λn2. (n,n2)) (BIGUNION (IMAGE line_get_code_labels pp)) ∪
  complex_get_code_labels p`,
  recInduct flatten_ind >> rw[]
  THEN1
   (once_rewrite_tac [flatten_def]>>
    fs[line_get_labels_def,get_code_labels_def]>>
    rpt(pairarg_tac>>fs[]) >>
    rw[] >> fs[line_get_labels_def,get_code_labels_def]>>
    match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS]) >>
  once_rewrite_tac [flatten_def]>>
  Cases_on `p`>>
  fs[line_get_labels_def,get_code_labels_def]>>
  rpt(pairarg_tac>>fs[])
  >-
    (TOP_CASE_TAC
    >-
      (* hidden jump target in dest *)
      (Cases_on`s`>>fs[compile_jump_def,line_get_labels_def]>>
      fs[])>>
    PairCases_on`x`>>fs[]>>
    pairarg_tac>>fs[]>>
    TOP_CASE_TAC>>
    fs[]>>TRY(PairCases_on`x`>>fs[]>> pairarg_tac)>>
    fs[line_get_labels_def] >>
    Cases_on`s`>>
    fs[compile_jump_def,line_get_labels_def]>>
    rw[]>>match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (
    rw[] >> fs[line_get_labels_def,get_code_labels_def]>>
    match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (* locally introduced labels in If *)
    (rw[]>>
    fs[line_get_labels_def]>>
    match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (
    fs[line_get_labels_def]>>
    match_mp_tac SUBSET_TRANS>>
    asm_exists_tac>>
    rw[]>>
    metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS]) >>
  rw [find_lab_def,oEL_THM,MEM_MAP] >>
  gvs [MEM_EL] >>
  metis_tac []);
val flatten_labels = Q.prove(
  `   ∀t m n p cs bs l x y.
     flatten t m n p cs bs = (l,x,y) ∧
     EVERY (sec_label_ok n) (append l)
     ⇒
     BIGUNION (IMAGE line_get_labels (set (append l))) ⊆
     set (MAP (λl. (n,l)) (cs ++ bs)) ∪
     sec_get_code_labels (Section n (append l)) ∪
     get_code_labels m`,
  recInduct stack_to_labTheory.flatten_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rw[Once stack_to_labTheory.flatten_def]
  \\ qabbrev_tac`XXX = debug p`
  \\ Cases_on`p` \\ fs[] \\ rveq
  \\ fs[labPropsTheory.line_get_labels_def,
        labPropsTheory.sec_get_code_labels_def]
  >- (
    fs[CaseEq"option",CaseEq"prod"]
    \\ rveq \\ fs[]
    >- (
      Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def]
      \\ EVAL_TAC \\ fs[] \\ rw[] )
    \\ rpt(pairarg_tac \\ fs[])
    \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    \\ fs[labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    >- (
      Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def]
      \\ fs[labPropsTheory.line_get_labels_def,
            labPropsTheory.line_get_code_labels_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
      \\ metis_tac[] )
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def]
    \\ fs[labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ metis_tac[] )
  >~ [‘Break’] >-
   (rw [find_lab_def,oEL_THM,MEM_MAP] \\ fs [MEM_EL] \\ metis_tac [])
  >~ [‘Continue’] >-
   (rw [find_lab_def,oEL_THM,MEM_MAP] \\ fs [MEM_EL] \\ metis_tac [])
  \\ (
    rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD, MEM_MAP]
    \\ fs[CaseEq"bool"] \\ rveq
    \\ fsrw_tac[DNF_ss][labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    \\ metis_tac[] ));
val prog_to_section_preserves_MAP_FST = Q.prove(
  `  ∀p.
    IMAGE (λn. n,0) (set (MAP FST p)) ⊆
    get_code_labels (MAP prog_to_section p)`,
  Induct>>
    fs[labPropsTheory.get_code_labels_cons,FORALL_PROD,stack_to_labTheory.prog_to_section_def]>>
    rw[]>> rpt(pairarg_tac>>fs[])>>
    simp[labPropsTheory.get_code_labels_cons, labPropsTheory.sec_get_code_labels_def]>>
    fs[SUBSET_DEF]);
val _ = checked "complex_get_code_labels_def_statement" stack_to_labProofTheory.complex_get_code_labels_def;
val _ = typed_statement "complex_get_code_labels_def_statement_typed" stack_to_labProofTheory.complex_get_code_labels_def;
val _ = type_list "complex_get_code_labels_def_statement_types" stack_to_labProofTheory.complex_get_code_labels_def;
val _ = checked "complex_flatten_labels_statement" complex_flatten_labels;
val _ = typed_statement "complex_flatten_labels_statement_typed" complex_flatten_labels;
val _ = type_list "complex_flatten_labels_statement_types" complex_flatten_labels;
val _ = checked "flatten_labels_statement" flatten_labels;
val _ = typed_statement "flatten_labels_statement_typed" flatten_labels;
val _ = type_list "flatten_labels_statement_types" flatten_labels;
val _ = checked "get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma_statement" stack_to_labProofTheory.get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma;
val _ = typed_statement "get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma_statement_typed" stack_to_labProofTheory.get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma;
val _ = type_list "get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma_statement_types" stack_to_labProofTheory.get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma;
val _ = checked "prog_to_section_preserves_MAP_FST_statement" prog_to_section_preserves_MAP_FST;
val _ = typed_statement "prog_to_section_preserves_MAP_FST_statement_typed" prog_to_section_preserves_MAP_FST;
val _ = type_list "prog_to_section_preserves_MAP_FST_statement_types" prog_to_section_preserves_MAP_FST;
val _ = checked "prog_to_section_labels_statement" stack_to_labProofTheory.prog_to_section_labels;
val _ = typed_statement "prog_to_section_labels_statement_typed" stack_to_labProofTheory.prog_to_section_labels;
val _ = type_list "prog_to_section_labels_statement_types" stack_to_labProofTheory.prog_to_section_labels;
val _ = checked "flatten_preserves_handler_labels_statement" stack_to_labProofTheory.flatten_preserves_handler_labels;
val _ = typed_statement "flatten_preserves_handler_labels_statement_typed" stack_to_labProofTheory.flatten_preserves_handler_labels;
val _ = type_list "flatten_preserves_handler_labels_statement_types" stack_to_labProofTheory.flatten_preserves_handler_labels;
val _ = checked "MAP_prog_to_section_preserves_handler_labels_statement" stack_to_labProofTheory.MAP_prog_to_section_preserves_handler_labels;
val _ = typed_statement "MAP_prog_to_section_preserves_handler_labels_statement_typed" stack_to_labProofTheory.MAP_prog_to_section_preserves_handler_labels;
val _ = type_list "MAP_prog_to_section_preserves_handler_labels_statement_types" stack_to_labProofTheory.MAP_prog_to_section_preserves_handler_labels;
val _ = checked "one_prog_section_statement" stack_to_labProofTheory.one_prog_section;
val _ = typed_statement "one_prog_section_statement_typed" stack_to_labProofTheory.one_prog_section;
val _ = type_list "one_prog_section_statement_types" stack_to_labProofTheory.one_prog_section;
val _ = checked "get_labels_MAP_prog_to_section_SUBSET_code_labels_statement" stack_to_labProofTheory.get_labels_MAP_prog_to_section_SUBSET_code_labels;
val _ = typed_statement "get_labels_MAP_prog_to_section_SUBSET_code_labels_statement_typed" stack_to_labProofTheory.get_labels_MAP_prog_to_section_SUBSET_code_labels;
val _ = type_list "get_labels_MAP_prog_to_section_SUBSET_code_labels_statement_types" stack_to_labProofTheory.get_labels_MAP_prog_to_section_SUBSET_code_labels;
