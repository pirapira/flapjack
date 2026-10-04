load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse bossLib preamble wordConvsTheory wordLangTheory word_unreachTheory word_simpTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
val extract_labels_SimpSeq = GEN_ALL(prove(``
set (extract_labels (SimpSeq p1 p2)) ⊆  set (extract_labels (Seq p1 p2))
``,
  rw [SimpSeq_def,extract_labels_def]
  \\ Cases_on ‘p1’ \\ rw [extract_labels_def] \\ gvs [SUBSET_DEF]
  \\ Cases_on ‘dest_Seq_Move p2’ \\ gvs []
  \\ rw [extract_labels_def] \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘x’ \\ gvs []
  \\ pop_assum mp_tac \\ rw []
  \\ gvs [oneline dest_Seq_Move_def, AllCaseEqs(), extract_labels_def]
));
val _ = if null(hyp extract_labels_SimpSeq) andalso null(free_vars(concl extract_labels_SimpSeq)) then () else raise Fail "open extract_labels_SimpSeq";
val _ = (print "unreachLabels1_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl extract_labels_SimpSeq));
val _ = print("unreachLabels1_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_SimpSeq))) ^ "\n");
val _ = print("unreachLabels1_hypotheses=" ^ Int.toString(length(hyp extract_labels_SimpSeq)) ^ "\n");
val extract_labels_Seq_assoc_right_lemma = GEN_ALL(prove(``
∀p1 p2. set (extract_labels (Seq_assoc_right p1 p2)) ⊆
          set (extract_labels p1) ∪ set (extract_labels p2)
``,
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
  >- (
    gvs[SUBSET_DEF]
    \\ metis_tac[])
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[extract_labels_def]
    \\ irule SUBSET_TRANS
    \\ irule_at Any extract_labels_SimpSeq
    \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
    \\ gvs[SUBSET_DEF]
  )
  \\ irule SUBSET_TRANS
  \\ irule_at Any extract_labels_SimpSeq
  \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
  \\ gvs[SUBSET_DEF]
));
val _ = if null(hyp extract_labels_Seq_assoc_right_lemma) andalso null(free_vars(concl extract_labels_Seq_assoc_right_lemma)) then () else raise Fail "open extract_labels_Seq_assoc_right_lemma";
val _ = (print "unreachLabels2_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl extract_labels_Seq_assoc_right_lemma));
val _ = print("unreachLabels2_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_Seq_assoc_right_lemma))) ^ "\n");
val _ = print("unreachLabels2_hypotheses=" ^ Int.toString(length(hyp extract_labels_Seq_assoc_right_lemma)) ^ "\n");
val extract_labels_remove_unreach = GEN_ALL(prove(``
set (extract_labels (remove_unreach p)) ⊆ set (extract_labels p)
``,
  simp[remove_unreach_def]
  \\ irule SUBSET_TRANS
  \\ irule_at (Pos hd) extract_labels_Seq_assoc_right_lemma
  \\ gvs [extract_labels_def]
));
val _ = if null(hyp extract_labels_remove_unreach) andalso null(free_vars(concl extract_labels_remove_unreach)) then () else raise Fail "open extract_labels_remove_unreach";
val _ = (print "unreachLabels3_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl extract_labels_remove_unreach));
val _ = print("unreachLabels3_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_remove_unreach))) ^ "\n");
val _ = print("unreachLabels3_hypotheses=" ^ Int.toString(length(hyp extract_labels_remove_unreach)) ^ "\n");
val MEM_extract_labels_Seq_assoc_right_lemma = GEN_ALL(prove(``
∀p1 p2 x.
    MEM x (extract_labels (Seq_assoc_right p1 p2)) ⇒
    MEM x (extract_labels p1) ∨ MEM x (extract_labels p2)
``,
  rpt strip_tac >>
  assume_tac extract_labels_Seq_assoc_right_lemma >>
  first_x_assum $ qspecl_then [‘p1’,‘p2’] assume_tac>>
  imp_res_tac SUBSET_THM >> fs[]
));
val _ = if null(hyp MEM_extract_labels_Seq_assoc_right_lemma) andalso null(free_vars(concl MEM_extract_labels_Seq_assoc_right_lemma)) then () else raise Fail "open MEM_extract_labels_Seq_assoc_right_lemma";
val _ = (print "unreachLabels4_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl MEM_extract_labels_Seq_assoc_right_lemma));
val _ = print("unreachLabels4_proved=" ^ term_to_string(rhs(concl(EQT_INTRO MEM_extract_labels_Seq_assoc_right_lemma))) ^ "\n");
val _ = print("unreachLabels4_hypotheses=" ^ Int.toString(length(hyp MEM_extract_labels_Seq_assoc_right_lemma)) ^ "\n");
val helper = MEM_extract_labels_Seq_assoc_right_lemma |> REWRITE_RULE [Once (GSYM CONTRAPOS_THM)];
val ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma = GEN_ALL(prove(``
∀p1 p2. ALL_DISTINCT ((extract_labels p1) ++ (extract_labels p2)) ⇒
          ALL_DISTINCT (extract_labels (Seq_assoc_right p1 p2))
``,
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,extract_labels_def,SimpSeq_def] >>
  TRY (rw[extract_labels_def] >> NO_TAC) >>
  TRY (CASE_TAC >> fs[extract_labels_def] >> NO_TAC) >>
  TRY (rename1 `Loop names _ exit_names` >>
       IF_CASES_TAC >>
       gvs [extract_labels_def, ALL_DISTINCT_APPEND'] >>
       rpt conj_tac >>
       TRY (first_x_assum irule >> fs [ALL_DISTINCT_APPEND'] >> NO_TAC) >>
       irule_at Any SUBSET_DISJOINT >>
       irule_at Any extract_labels_Seq_assoc_right_lemma >>
       irule_at Any SUBSET_REFL >>
       gvs [extract_labels_def] >> NO_TAC)
  >- (first_x_assum irule >>
      fs[ALL_DISTINCT_APPEND'] >>
      irule_at Any SUBSET_DISJOINT >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      irule_at Any SUBSET_REFL >>
      simp[DISJOINT_UNION'])
  >- (CASE_TAC >> fs[extract_labels_def] >>
      fs [ALL_DISTINCT_APPEND'] >>
      irule_at Any SUBSET_DISJOINT >>
      last_assum $ irule_at Any >>
      irule_at Any SUBSET_TRANS >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any SUBSET_TRANS >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any SUBSET_DISJOINT >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any SUBSET_REFL >> simp[] >>
      irule_at Any SUBSET_DISJOINT >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any SUBSET_REFL >> simp[])
  >- (CASE_TAC >> fs[extract_labels_def] >>
      fs [ALL_DISTINCT_APPEND'] >>
      irule_at Any SUBSET_DISJOINT >>
      last_assum $ irule_at Any >>
      irule_at Any SUBSET_TRANS >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def])
  >- (rpt (CASE_TAC >> fs[]) >> fs[extract_labels_def]
      >- (irule helper >> simp[extract_labels_def])
      >- (fs[ALL_DISTINCT_APPEND'] >>
          irule_at Any SUBSET_DISJOINT >>
          irule_at Any extract_labels_Seq_assoc_right_lemma >>
          simp[extract_labels_def] >>
          irule_at Any SUBSET_REFL >> simp[] >>
          irule helper >> simp[extract_labels_def])
      >- (fs[ALL_DISTINCT_APPEND'] >>
          irule_at Any SUBSET_DISJOINT >>
          irule_at Any extract_labels_Seq_assoc_right_lemma >>
          irule_at Any extract_labels_Seq_assoc_right_lemma >>
          simp[extract_labels_def] >>
          irule_at Any (iffRL DISJOINT_SYM) >> fs[] >>
          ntac 4 (irule_at Any helper >> simp[extract_labels_def])) >>
      fs[ALL_DISTINCT_APPEND'] >>
      irule_at Any SUBSET_DISJOINT >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any (iffRL DISJOINT_SYM) >> fs[] >>
      ntac 4 (irule_at Any helper >> simp[extract_labels_def]) >>
      ntac 2 (irule_at Any SUBSET_DISJOINT >>
              irule_at Any extract_labels_Seq_assoc_right_lemma >>
              simp[extract_labels_def] >>
              irule_at Any SUBSET_REFL >> simp[])) >>
  rpt (CASE_TAC >> fs[]) >> fs[extract_labels_def] >>
  Cases_on ‘p2’ >> fs[dest_Seq_Move_def] >> rename1 ‘Seq p p0’ >>
  Cases_on ‘p’ >> fs[dest_Seq_Move_def,extract_labels_def]
));
val _ = if null(hyp ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma) andalso null(free_vars(concl ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma)) then () else raise Fail "open ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma";
val _ = (print "unreachLabels5_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma));
val _ = print("unreachLabels5_proved=" ^ term_to_string(rhs(concl(EQT_INTRO ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma))) ^ "\n");
val _ = print("unreachLabels5_hypotheses=" ^ Int.toString(length(hyp ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma)) ^ "\n");
val ALL_DISTINCT_extract_labels_remove_unreach = GEN_ALL(prove(``
ALL_DISTINCT (extract_labels p) ⇒
   ALL_DISTINCT (extract_labels (remove_unreach p))
``,
  rw[remove_unreach_def] >>
  irule ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma >>
  simp[extract_labels_def]
));
val _ = if null(hyp ALL_DISTINCT_extract_labels_remove_unreach) andalso null(free_vars(concl ALL_DISTINCT_extract_labels_remove_unreach)) then () else raise Fail "open ALL_DISTINCT_extract_labels_remove_unreach";
val _ = (print "unreachLabels6_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl ALL_DISTINCT_extract_labels_remove_unreach));
val _ = print("unreachLabels6_proved=" ^ term_to_string(rhs(concl(EQT_INTRO ALL_DISTINCT_extract_labels_remove_unreach))) ^ "\n");
val _ = print("unreachLabels6_hypotheses=" ^ Int.toString(length(hyp ALL_DISTINCT_extract_labels_remove_unreach)) ^ "\n");
val labels_rel_remove_unreach = GEN_ALL(prove(``
labels_rel (extract_labels q) (extract_labels (remove_unreach q))
``,
  rw[labels_rel_def]
  >- fs[ALL_DISTINCT_extract_labels_remove_unreach] >>
  irule_at Any extract_labels_remove_unreach>> simp[]
));
val _ = if null(hyp labels_rel_remove_unreach) andalso null(free_vars(concl labels_rel_remove_unreach)) then () else raise Fail "open labels_rel_remove_unreach";
val _ = (print "unreachLabels7_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl labels_rel_remove_unreach));
val _ = print("unreachLabels7_proved=" ^ term_to_string(rhs(concl(EQT_INTRO labels_rel_remove_unreach))) ^ "\n");
val _ = print("unreachLabels7_hypotheses=" ^ Int.toString(length(hyp labels_rel_remove_unreach)) ^ "\n");
