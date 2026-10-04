load "preamble"; load "word_to_wordProofTheory";
open HolKernel Parse bossLib preamble word_to_wordTheory word_to_wordProofTheory
  wordLangTheory wordConvsTheory wordConvsProofTheory word_allocTheory
  word_simpTheory word_instTheory word_unreachTheory word_copyTheory
  word_removeTheory word_removeProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = bring_to_front_overload "Call" {Thy="wordLang",Name="Call"};
val rmt_thms = (remove_must_terminate_conventions |> SIMP_RULE std_ss [LET_THM,FORALL_AND_THM]) |> CONJUNCTS;
val rmd_thms = (remove_dead_prog_conventions |> SIMP_RULE std_ss [LET_THM,FORALL_AND_THM]) |> CONJUNCTS;
(* Original first two CONJ_TAC proof sections. Only the split introducing the
   omitted third conjunct is removed; all names/labels proof tactics unchanged. *)
val namesLabelsSections = GEN_ALL(prove(``
  EVERY (λ(_,_,prg). no_share_inst prg ∨ ac.ISA ≠ Ag32) p ⇒
  let (_,progs) = compile wc ac p in
  MAP FST progs = MAP FST p ∧
  EVERY2 labels_rel (MAP (extract_labels o SND o SND) p)
                    (MAP (extract_labels o SND o SND) progs)
``,
  fs[compile_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[]>>
  `LENGTH n_oracles = LENGTH p` by
    (fs[next_n_oracle_def]>>
    every_case_tac>>rw[]>>
    simp[LENGTH_TAKE,LENGTH_REPLICATE])>>
  CONJ_TAC >- (
    match_mp_tac LIST_EQ>>
    fs[EL_MAP,full_compile_single_def]>>
    rw[]>>
    qpat_abbrev_tac`q = EL x A`>>
    fs[markerTheory.Abbrev_def]>>PairCases_on`q`>>
    pop_assum (assume_tac o SYM)>>
    fs[compile_single_def]>>
    pop_assum mp_tac>>
    fs[EL_MAP,EL_ZIP])>>
  (
    simp[LIST_REL_EL_EQN,EL_MAP,full_compile_single_def]>>
    rw[]>>
    qpat_abbrev_tac`q = EL x A`>>
    fs[markerTheory.Abbrev_def]>>PairCases_on`q`>>
    pop_assum (mp_tac o SYM)>>
    fs[EL_MAP,EL_ZIP]>>
    fs[compile_single_def]>>
    fs[GSYM (el 5 rmt_thms),GSYM word_alloc_lab_pres]>>
    fs[GSYM (el 6 rmd_thms)]>>
    strip_tac>>
    irule_at Any (labels_rel_TRANS)>>
    irule_at (Pos last) labels_rel_remove_unreach>>
    simp[GSYM three_to_two_reg_prog_lab_pres]>>
    simp[extract_labels_copy_prop] >>
    simp[extract_labels_word_common_subexp_elim] >>
    simp[GSYM remove_dead_prog_conventions]>>
    simp[GSYM full_ssa_cc_trans_lab_pres] >>
    simp[GSYM inst_select_lab_pres] >>
    simp[extract_labels_compile_exp]
    )
));
val _ = if null(hyp namesLabelsSections) andalso null(free_vars(concl namesLabelsSections)) then () else raise Fail "open names/labels sections";
val _ = (print "namesLabelsSections_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl namesLabelsSections));
val _ = print("namesLabelsSections_proved=" ^ term_to_string(rhs(concl(EQT_INTRO namesLabelsSections))) ^ "\n");
val _ = print("namesLabelsSections_hypotheses=" ^ Int.toString(length(hyp namesLabelsSections)) ^ "\n");
