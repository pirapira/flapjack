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
val _ = (print "extract_labels_const_fp_loop_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl extract_labels_const_fp_loop_closed));
val _ = print("extract_labels_const_fp_loop_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_const_fp_loop_closed))) ^ "\n");
val _ = print("extract_labels_const_fp_loop_hypotheses=" ^ Int.toString(length(hyp extract_labels_const_fp_loop_closed)) ^ "\n");
val extract_labels_const_fp = Q.prove (`
   labels_rel (extract_labels p) (extract_labels (const_fp p))
`,
  fs [const_fp_def] \\ Cases_on `const_fp_loop p LN`
  \\ drule extract_labels_const_fp_loop
  \\ simp []
);
val extract_labels_const_fp_closed = GEN_ALL extract_labels_const_fp;
val _ = if null(hyp extract_labels_const_fp_closed) andalso null(free_vars(concl extract_labels_const_fp_closed)) then () else raise Fail "open extract_labels_const_fp";
val _ = (print "extract_labels_const_fp_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl extract_labels_const_fp_closed));
val _ = print("extract_labels_const_fp_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_const_fp_closed))) ^ "\n");
val _ = print("extract_labels_const_fp_hypotheses=" ^ Int.toString(length(hyp extract_labels_const_fp_closed)) ^ "\n");
