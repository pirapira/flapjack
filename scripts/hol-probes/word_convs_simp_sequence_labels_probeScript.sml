load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse bossLib preamble wordConvsTheory wordLangTheory word_simpTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
val extract_labels_SmartSeq = GEN_ALL(prove(``
extract_labels (SmartSeq p1 p2) = extract_labels (Seq p1 p2)
``,
  rw [SmartSeq_def,extract_labels_def]
));
val _ = if null(hyp extract_labels_SmartSeq) andalso null(free_vars(concl extract_labels_SmartSeq)) then () else raise Fail "open extract_labels_SmartSeq";
val _ = (print "simpSequenceLabels1_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl extract_labels_SmartSeq));
val _ = print("simpSequenceLabels1_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_SmartSeq))) ^ "\n");
val _ = print("simpSequenceLabels1_hypotheses=" ^ Int.toString(length(hyp extract_labels_SmartSeq)) ^ "\n");
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
val _ = (print "simpSequenceLabels2_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl extract_labels_Seq_assoc_lemma));
val _ = print("simpSequenceLabels2_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_Seq_assoc_lemma))) ^ "\n");
val _ = print("simpSequenceLabels2_hypotheses=" ^ Int.toString(length(hyp extract_labels_Seq_assoc_lemma)) ^ "\n");
val extract_labels_Seq_assoc = GEN_ALL(prove(``
extract_labels (Seq_assoc Skip p) = extract_labels p
``,
  fs [extract_labels_Seq_assoc_lemma,extract_labels_def]
));
val _ = if null(hyp extract_labels_Seq_assoc) andalso null(free_vars(concl extract_labels_Seq_assoc)) then () else raise Fail "open extract_labels_Seq_assoc";
val _ = (print "simpSequenceLabels3_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl extract_labels_Seq_assoc));
val _ = print("simpSequenceLabels3_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_Seq_assoc))) ^ "\n");
val _ = print("simpSequenceLabels3_hypotheses=" ^ Int.toString(length(hyp extract_labels_Seq_assoc)) ^ "\n");
val extract_labels_drop_consts_1 = GEN_ALL(prove(``
extract_labels (drop_consts cs ls) = []
``,
  Induct_on`ls`>>rw[drop_consts_def]>>
  every_case_tac>>
  rw[extract_labels_SmartSeq,extract_labels_def]
));
val _ = if null(hyp extract_labels_drop_consts_1) andalso null(free_vars(concl extract_labels_drop_consts_1)) then () else raise Fail "open extract_labels_drop_consts_1";
val _ = (print "simpSequenceLabels4_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl extract_labels_drop_consts_1));
val _ = print("simpSequenceLabels4_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_drop_consts_1))) ^ "\n");
val _ = print("simpSequenceLabels4_hypotheses=" ^ Int.toString(length(hyp extract_labels_drop_consts_1)) ^ "\n");
val extract_labels_drop_consts = GEN_ALL(prove(``
extract_labels (SmartSeq (drop_consts cs ls) p) = extract_labels p
``,
  rw[extract_labels_SmartSeq,extract_labels_def,extract_labels_drop_consts_1]
));
val _ = if null(hyp extract_labels_drop_consts) andalso null(free_vars(concl extract_labels_drop_consts)) then () else raise Fail "open extract_labels_drop_consts";
val _ = (print "simpSequenceLabels5_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl extract_labels_drop_consts));
val _ = print("simpSequenceLabels5_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extract_labels_drop_consts))) ^ "\n");
val _ = print("simpSequenceLabels5_hypotheses=" ^ Int.toString(length(hyp extract_labels_drop_consts)) ^ "\n");
val labels_rel_append_imp = GEN_ALL(prove(``
labels_rel (Y ++ X) Z ==> labels_rel (X ++ Y) Z
``,
  metis_tac [PERM_APPEND, labels_rel_TRANS, PERM_IMP_labels_rel]
));
val _ = if null(hyp labels_rel_append_imp) andalso null(free_vars(concl labels_rel_append_imp)) then () else raise Fail "open labels_rel_append_imp";
val _ = (print "simpSequenceLabels6_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl labels_rel_append_imp));
val _ = print("simpSequenceLabels6_proved=" ^ term_to_string(rhs(concl(EQT_INTRO labels_rel_append_imp))) ^ "\n");
val _ = print("simpSequenceLabels6_hypotheses=" ^ Int.toString(length(hyp labels_rel_append_imp)) ^ "\n");
