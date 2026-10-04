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
open word_simpProofTheory wordPropsTheory word_allocProofTheory word_instProofTheory
  word_unreachProofTheory word_cseProofTheory word_elimProofTheory word_copyProofTheory;
(* Entire original local proof, statement and tactics copied unchanged. *)
val fullConventions = GEN_ALL(prove(``
  EVERY (λ(_,_,prg). no_share_inst prg ∨ ac.ISA ≠ Ag32) p ⇒
  let (_,progs) = compile wc ac p in
  MAP FST progs = MAP FST p ∧
  EVERY2 labels_rel (MAP (extract_labels o SND o SND) p)
                    (MAP (extract_labels o SND o SND) progs) ∧
  EVERY (λ(n,m,prog).
    flat_exp_conventions prog ∧
    post_alloc_conventions (ac.reg_count - (5+LENGTH ac.avoid_regs)) prog ∧
    (EVERY (λ(n,m,prog). every_inst (inst_ok_less ac) prog) p ∧
     addr_offset_ok ac 0w ∧ hw_offset_ok ac 0w ∧ byte_offset_ok ac 0w ⇒
      full_inst_ok_less ac prog) ∧
    (ac.two_reg_arith ⇒ every_inst two_reg_inst prog) ∧
    (no_share_inst prog ∨ ac.ISA ≠ Ag32)) progs
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
  CONJ_TAC >- (
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
    )>>
  fs[EVERY_MAP,EVERY_MEM,MEM_ZIP,FORALL_PROD]>>rw[]>>
  fs[full_compile_single_def,compile_single_def]>>
  CONJ_TAC>- (
    match_mp_tac (el 1 rmt_thms)>>
    match_mp_tac word_alloc_flat_exp_conventions>>
    match_mp_tac (el 1 rmd_thms)>>
    match_mp_tac flat_exp_conventions_remove_unreach>>
    match_mp_tac three_to_two_reg_prog_flat_exp_conventions>>
    irule flat_exp_conventions_copy_prop>>
    irule flat_exp_conventions_word_common_subexp_elim >>
    match_mp_tac (el 1 rmd_thms)>>
    match_mp_tac full_ssa_cc_trans_flat_exp_conventions>>
    fs[inst_select_flat_exp_conventions])>>
  CONJ_TAC>- (
    match_mp_tac (el 3 rmt_thms)>>
    match_mp_tac pre_post_conventions_word_alloc>>
    match_mp_tac (el 3 rmd_thms)>>
    match_mp_tac pre_alloc_conventions_remove_unreach>>
    match_mp_tac three_to_two_reg_prog_pre_alloc_conventions >>
    (* pre_alloc_conventions *)
    irule pre_alloc_conventions_copy_prop>>
    irule pre_alloc_conventions_word_common_subexp_elim >>
    match_mp_tac (el 3 rmd_thms)>>
    fs[full_ssa_cc_trans_pre_alloc_conventions])>>
  CONJ_TAC>- (
    strip_tac>>
    match_mp_tac (el 2 rmt_thms)>>
    match_mp_tac word_alloc_full_inst_ok_less>>
    match_mp_tac (el 2 rmd_thms)>>
    match_mp_tac full_inst_ok_less_remove_unreach>>
    match_mp_tac three_to_two_reg_prog_full_inst_ok_less >>
    irule full_inst_ok_less_copy_prop>>
    irule full_inst_ok_less_word_common_subexp_elim >>
    match_mp_tac (el 2 rmd_thms)>>
    match_mp_tac full_ssa_cc_trans_full_inst_ok_less>>
    match_mp_tac inst_select_full_inst_ok_less>>
    fs[]>>
    metis_tac[compile_exp_no_inst,MEM_EL])>>
  rw[]
  >- (match_mp_tac (el 4 rmt_thms)>>
      match_mp_tac word_alloc_two_reg_inst>>
      match_mp_tac (el 4 rmd_thms)>>
      match_mp_tac every_inst_remove_unreach >>
      match_mp_tac three_to_two_reg_prog_two_reg_inst >>
      fs[])>>
  ‘no_share_inst (SND (SND (FST (EL n p,EL n n_oracles))))’ by
    (fs[MEM_EL]>>res_tac>>
     qpat_x_assum ‘_ = EL n p’ $ assume_tac o GSYM >> fs[])>>
  imp_res_tac full_compile_single_no_share_inst>>
  first_x_assum $ qspecl_then [‘ac.two_reg_arith’,‘ac.reg_count - (LENGTH ac.avoid_regs + 5)’,‘ac’, ‘wc.reg_alg’] assume_tac>>
  qpat_x_assum ‘_ = EL n p’ $ assume_tac o GSYM>>fs[]>>
  fs[full_compile_single_def,compile_single_def]
));
val _ = if null(hyp fullConventions) andalso null(free_vars(concl fullConventions)) then () else raise Fail "open full conventions";
val _ = (print "fullConventions_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl fullConventions));
val _ = print("fullConventions_proved=" ^ term_to_string(rhs(concl(EQT_INTRO fullConventions))) ^ "\n");
val _ = print("fullConventions_hypotheses=" ^ Int.toString(length(hyp fullConventions)) ^ "\n");
