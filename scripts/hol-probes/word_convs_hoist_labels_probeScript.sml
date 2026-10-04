load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse bossLib preamble wordConvsTheory wordLangTheory word_simpTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
val extract_labels_SmartSeq = GEN_ALL(prove(``
extract_labels (SmartSeq p1 p2) = extract_labels (Seq p1 p2)
``,
  rw [SmartSeq_def,extract_labels_def]
));
val _ = if null(hyp extract_labels_SmartSeq) andalso null(free_vars(concl extract_labels_SmartSeq)) then () else raise Fail "open extract_labels_SmartSeq";
val extract_labels_Seq_assoc_lemma = GEN_ALL(prove(``
!p1 p2. extract_labels (Seq_assoc p1 p2) =
            extract_labels p1 ++ extract_labels p2
``,
  HO_MATCH_MP_TAC Seq_assoc_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_def,extract_labels_def,extract_labels_SmartSeq]
  \\ Cases_on `ret_prog` \\ Cases_on `handler` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ PairCases_on `x'` \\ fs []
));
val _ = if null(hyp extract_labels_Seq_assoc_lemma) andalso null(free_vars(concl extract_labels_Seq_assoc_lemma)) then () else raise Fail "open extract_labels_Seq_assoc_lemma";
val extract_labels_Seq_assoc = GEN_ALL(prove(``
extract_labels (Seq_assoc Skip p) = extract_labels p
``,
  fs [extract_labels_Seq_assoc_lemma,extract_labels_def]
));
val _ = if null(hyp extract_labels_Seq_assoc) andalso null(free_vars(concl extract_labels_Seq_assoc)) then () else raise Fail "open extract_labels_Seq_assoc";
val extract_labels_drop_consts_1 = GEN_ALL(prove(``
extract_labels (drop_consts cs ls) = []
``,
  Induct_on`ls`>>rw[drop_consts_def]>>
  every_case_tac>>
  rw[extract_labels_SmartSeq,extract_labels_def]
));
val _ = if null(hyp extract_labels_drop_consts_1) andalso null(free_vars(concl extract_labels_drop_consts_1)) then () else raise Fail "open extract_labels_drop_consts_1";
val extract_labels_drop_consts = GEN_ALL(prove(``
extract_labels (SmartSeq (drop_consts cs ls) p) = extract_labels p
``,
  rw[extract_labels_SmartSeq,extract_labels_def,extract_labels_drop_consts_1]
));
val _ = if null(hyp extract_labels_drop_consts) andalso null(free_vars(concl extract_labels_drop_consts)) then () else raise Fail "open extract_labels_drop_consts";
val labels_rel_append_imp = GEN_ALL(prove(``
labels_rel (Y ++ X) Z ==> labels_rel (X ++ Y) Z
``,
  metis_tac [PERM_APPEND, labels_rel_TRANS, PERM_IMP_labels_rel]
));
val _ = if null(hyp labels_rel_append_imp) andalso null(free_vars(concl labels_rel_append_imp)) then () else raise Fail "open labels_rel_append_imp";
load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse bossLib preamble wordLangTheory wordConvsTheory word_simpTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
(* Unchanged original local proofs in source order. The first five are replayed
   only to supply the original sequence/drop-constant prerequisites. *)
val extract_labels_SmartSeq = Q.prove (`
   extract_labels (SmartSeq p1 p2) = extract_labels (Seq p1 p2)
`,
  rw [SmartSeq_def,extract_labels_def]
);
val extract_labels_Seq_assoc_lemma = Q.prove (`
   !p1 p2. extract_labels (Seq_assoc p1 p2) =
            extract_labels p1 ++ extract_labels p2
`,
  HO_MATCH_MP_TAC Seq_assoc_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_def,extract_labels_def,extract_labels_SmartSeq]
  \\ Cases_on `ret_prog` \\ Cases_on `handler` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ PairCases_on `x'` \\ fs []
);
val extract_labels_Seq_assoc = Q.prove (`
   extract_labels (Seq_assoc Skip p) = extract_labels p
`,
  fs [extract_labels_Seq_assoc_lemma,extract_labels_def]
);
val extract_labels_drop_consts_1 = Q.prove (`
  extract_labels (drop_consts cs ls) = []
`,
  Induct_on`ls`>>rw[drop_consts_def]>>
  every_case_tac>>
  rw[extract_labels_SmartSeq,extract_labels_def]
);
val extract_labels_drop_consts = Q.prove (`
  extract_labels (SmartSeq (drop_consts cs ls) p) = extract_labels p
`,
  rw[extract_labels_SmartSeq,extract_labels_def,extract_labels_drop_consts_1]
);
val _ = augment_srw_ss [rewrites [extract_labels_drop_consts]];
val extract_labels_const_fp_loop = Q.prove (`
  !p cs p1 cs1.
  const_fp_loop p cs = (p1,cs1) ==>
  labels_rel (extract_labels p) (extract_labels p1)
`,
  ho_match_mp_tac const_fp_loop_ind
  \\ ntac 6 (conj_tac THEN1
   (fs [const_fp_loop_def] \\ rw [] \\ fs [extract_labels_def]
    \\ every_case_tac
    \\ fs [const_fp_loop_def] \\ rw [] \\ fs [extract_labels_def]
    \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [extract_labels_def]
    \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [extract_labels_def]
    \\ match_mp_tac labels_rel_APPEND \\ fs []))
  \\ reverse (rpt conj_tac)
  \\ TRY (fs [const_fp_loop_def] \\ rw [] \\ fs [extract_labels_def] \\ NO_TAC)
  THEN1 (* Loop *)
   (rw [] \\ fs [const_fp_loop_def]
    \\ Cases_on `const_fp_loop p LN` \\ fs []
    \\ rveq \\ fs [extract_labels_def]
    \\ res_tac)
  THEN1 (* Call *)
   (rw [] \\ fs [const_fp_loop_def]
    \\ gvs[AllCaseEqs()]
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [extract_labels_def]
    \\ once_rewrite_tac [CONS_APPEND]
    \\ match_mp_tac labels_rel_APPEND \\ fs [])
  \\ (* If *) rw [] \\ fs [const_fp_loop_def]
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs [extract_labels_def]
  \\ TRY (match_mp_tac labels_rel_APPEND \\ fs [])
  \\ fs [labels_rel_def,ALL_DISTINCT_APPEND,SUBSET_DEF]
);
val extract_labels_const_fp_loop_closed = GEN_ALL extract_labels_const_fp_loop;
val _ = if null(hyp extract_labels_const_fp_loop_closed) andalso null(free_vars(concl extract_labels_const_fp_loop_closed)) then () else raise Fail "open extract_labels_const_fp_loop";
val extract_labels_const_fp = Q.prove (`
   labels_rel (extract_labels p) (extract_labels (const_fp p))
`,
  fs [const_fp_def] \\ Cases_on `const_fp_loop p LN`
  \\ drule extract_labels_const_fp_loop
  \\ simp []
);
val extract_labels_const_fp_closed = GEN_ALL extract_labels_const_fp;
val _ = if null(hyp extract_labels_const_fp_closed) andalso null(free_vars(concl extract_labels_const_fp_closed)) then () else raise Fail "open extract_labels_const_fp";
load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse bossLib preamble wordConvsTheory wordLangTheory word_simpTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
val const_fp_loop_Seq = GEN_ALL(
  const_fp_loop_def |> BODY_CONJUNCTS
  |> filter (can (find_term (fn t => total (fst o dest_const) t = SOME "Seq")) o concl)
  |> LIST_CONJ
);
val _ = if null(hyp const_fp_loop_Seq) andalso null(free_vars(concl const_fp_loop_Seq)) then () else raise Fail "open const_fp_loop_Seq";
val const_fp_loop_dummy_cases = GEN_ALL(prove(``
const_fp_loop (If cmp lhs rhs (Raise 1) (Raise 2)) cs = (p2, cs2) ==>
  (dest_Raise_num p2 = 1 /\
  (! br1 br2 . const_fp_loop (If cmp lhs rhs br1 br2) cs = const_fp_loop br1 cs)) \/
  (dest_Raise_num p2 = 2 /\
  (! br1 br2 . const_fp_loop (If cmp lhs rhs br1 br2) cs = const_fp_loop br2 cs)) \/
  (dest_Raise_num p2 = 0)
``,
  rw [const_fp_loop_def, dest_Raise_num_def]
  \\ gvs [CaseEq "option", CaseEq "bool"]
));
val _ = if null(hyp const_fp_loop_dummy_cases) andalso null(free_vars(concl const_fp_loop_dummy_cases)) then () else raise Fail "open const_fp_loop_dummy_cases";
val dest_If_thm = GEN_ALL(prove(``
dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = If g1 g2 g3 g4 g5
``,
  Cases_on `x2` \\ fs [dest_If_def]
));
val _ = if null(hyp dest_If_thm) andalso null(free_vars(concl dest_If_thm)) then () else raise Fail "open dest_If_thm";
fun FIRST_THEN tacs tac = FIRST (map (fn t => t \\ tac) tacs)

val try_cancel_labels_rel_append =
  FIRST_THEN [ALL_TAC, irule labels_rel_append_imp]
  (FIRST_THEN [REWRITE_TAC [GSYM APPEND_ASSOC],
      REWRITE_TAC [APPEND_ASSOC], ONCE_REWRITE_TAC [APPEND_ASSOC]]
  (FIRST_THEN [ALL_TAC, irule labels_rel_append_imp]
  (FIRST_THEN [REWRITE_TAC [GSYM APPEND_ASSOC], REWRITE_TAC [APPEND_ASSOC]]
  (drule_at_then Any irule labels_rel_APPEND))));

val labels_rel_hoist2 = GEN_ALL(prove(``
! N p1 interm dummy p2 s.
  try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
  dest_If p2 = SOME (cmp, lhs, rhs, br1, br2) ==>
  dummy = If cmp lhs rhs (Raise 1) (Raise 2) ==>
  extract_labels interm = [] ==>
  labels_rel (extract_labels p1 ++ extract_labels p2)
    (extract_labels p3)
``,
  ho_match_mp_tac try_if_hoist2_ind
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ REWRITE_TAC [Once try_if_hoist2_def]
  \\ rw []
  \\ fs [CaseEq "bool", CaseEq "wordLang$prog",
        CaseEq "option", CaseEq "prod"]
  \\ gvs []
  \\ fs [extract_labels_def, dest_If_thm]
  >- (
    fs [is_simple_def] \\ every_case_tac
    \\ gs [extract_labels_def]
  )
  >- (
    fs [const_fp_def, const_fp_loop_Seq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [dest_Seq_def]
    \\ simp [Once const_fp_loop_def]
    \\ rpt (dxrule const_fp_loop_dummy_cases)
    \\ rw [] \\ fs []
    \\ gs []
    \\ fs [const_fp_loop_Seq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [extract_labels_def]
    \\ imp_res_tac extract_labels_const_fp_loop
    \\ gs [extract_labels_def, EVAL ``labels_rel [] _``]
    \\ rpt try_cancel_labels_rel_append
    \\ simp []
  )
  >- (
    fs [const_fp_def, const_fp_loop_Seq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [dest_Seq_def]
    \\ simp [Once const_fp_loop_def]
    \\ rpt (dxrule const_fp_loop_dummy_cases)
    \\ rw [] \\ fs []
    \\ gs []
    \\ fs [const_fp_loop_Seq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [extract_labels_def]
    \\ imp_res_tac extract_labels_const_fp_loop
    \\ gs [extract_labels_def, EVAL ``labels_rel [] _``]
    \\ rpt try_cancel_labels_rel_append
    \\ simp []
  )
));
val _ = if null(hyp labels_rel_hoist2) andalso null(free_vars(concl labels_rel_hoist2)) then () else raise Fail "open labels_rel_hoist2";
val _ = (print "hoistLabels_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl labels_rel_hoist2));
val _ = print("hoistLabels_proved=" ^ term_to_string(rhs(concl(EQT_INTRO labels_rel_hoist2))) ^ "\n");
val _ = print("hoistLabels_hypotheses=" ^ Int.toString(length(hyp labels_rel_hoist2)) ^ "\n");
val labels_rel_simp_duplicate_if = GEN_ALL(prove(``
!p. labels_rel (extract_labels p) (extract_labels (simp_duplicate_if p))
``,
  ho_match_mp_tac simp_duplicate_if_ind
  \\ rw []
  \\ simp [Once simp_duplicate_if_def]
  \\ Cases_on `p` \\ fs []
  \\ simp [extract_labels_def]
  \\ every_case_tac
  \\ fs [extract_labels_def, labels_rel_CONS, labels_rel_APPEND]
  \\ simp [extract_labels_Seq_assoc_lemma, extract_labels_def]
  \\ fs [try_if_hoist1_def, CaseEq "option", CaseEq "prod", EXISTS_PROD]
  \\ drule labels_rel_hoist2
  \\ rw [extract_labels_def]
  \\ drule_at_then Any irule labels_rel_TRANS
  \\ irule labels_rel_APPEND
  \\ simp []
));
val _ = if null(hyp labels_rel_simp_duplicate_if) andalso null(free_vars(concl labels_rel_simp_duplicate_if)) then () else raise Fail "open labels_rel_simp_duplicate_if";
val _ = (print "duplicateIfLabels_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl labels_rel_simp_duplicate_if));
val _ = print("duplicateIfLabels_proved=" ^ term_to_string(rhs(concl(EQT_INTRO labels_rel_simp_duplicate_if))) ^ "\n");
val _ = print("duplicateIfLabels_hypotheses=" ^ Int.toString(length(hyp labels_rel_simp_duplicate_if)) ^ "\n");
