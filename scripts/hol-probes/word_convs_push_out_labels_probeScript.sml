load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse bossLib preamble wordConvsTheory wordLangTheory word_simpTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
val labels_rel_append_imp = GEN_ALL(prove(``
labels_rel (Y ++ X) Z ==> labels_rel (X ++ Y) Z
``,
  metis_tac [PERM_APPEND, labels_rel_TRANS, PERM_IMP_labels_rel]
));
val _ = if null(hyp labels_rel_append_imp) andalso null(free_vars(concl labels_rel_append_imp)) then () else raise Fail "open labels_rel_append_imp";
val _ = (print "pushOutLabelsHelper_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl labels_rel_append_imp));
val _ = print("pushOutLabelsHelper_proved=" ^ term_to_string(rhs(concl(EQT_INTRO labels_rel_append_imp))) ^ "\n");
val _ = print("pushOutLabelsHelper_hypotheses=" ^ Int.toString(length(hyp labels_rel_append_imp)) ^ "\n");
val labels_rel_push_out_if = GEN_ALL(prove(``
!p. labels_rel (extract_labels p) (extract_labels (push_out_if p))
``,
  simp[push_out_if_def]
  \\ ho_match_mp_tac push_out_if_aux_ind
  \\ rw[]
  \\ simp_tac(srw_ss())[Once push_out_if_aux_def]
  \\ simp $ map (Q.ISPEC `FST:'free_tyvar # 'free_tyvar2 -> 'free_tyvar` o TypeBase.case_rand_of) $
     [``:'a prog``, ``:'a # 'b``,``:'a option``,``:bool``]
  \\ rpt (PURE_TOP_CASE_TAC \\ simp_tac(srw_ss())[])
  \\ fs[] \\ simp[extract_labels_def]
  \\ metis_tac[ labels_rel_refl,labels_rel_APPEND,labels_rel_append_imp]
));
val _ = if null(hyp labels_rel_push_out_if) andalso null(free_vars(concl labels_rel_push_out_if)) then () else raise Fail "open labels_rel_push_out_if";
val _ = (print "pushOutLabels_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl labels_rel_push_out_if));
val _ = print("pushOutLabels_proved=" ^ term_to_string(rhs(concl(EQT_INTRO labels_rel_push_out_if))) ^ "\n");
val _ = print("pushOutLabels_hypotheses=" ^ Int.toString(length(hyp labels_rel_push_out_if)) ^ "\n");
