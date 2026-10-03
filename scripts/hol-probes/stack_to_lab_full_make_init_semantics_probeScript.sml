load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble wordPropsTheory stack_namesProofTheory
 stack_allocProofTheory stack_removeProofTheory stack_to_labTheory stackSemTheory
 stackPropsTheory stack_allocTheory labSemTheory labPropsTheory semanticsPropsTheory
 stack_to_labProofTheory;
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

(* The SML val make_init_semantics, the local MAP_FST_compile_compile and halt_assum_lemma used by the proof,
   and the original line-3365 full_make_init_semantics, replayed with their
   source proofs (stack_to_labProofScript.sml:3047-3049, 3132-3150, 3194-3207, 3365-3615). *)
val make_init_semantics = flatten_semantics
  |> Q.INST [`s1`|->`make_init code coracle regs save_regs (s:('a,'c,'ffi)labSem$state)`,`s2`|->`s`]
  |> SIMP_RULE std_ss [EVAL ``(make_init code coracle regs save_regs s).code``];
val halt_assum_lemma = Q.prove(
  `  halt_assum (:'ffi#'c)
     (fromAList (stack_names$compile f
       (compile jump off gen max_heap k l code)))`,
  fs [halt_assum_def] \\ rw []
  \\ fs [stackSemTheory.evaluate_def,
         stackSemTheory.find_code_def]
  \\ fs [stack_namesTheory.compile_def,
         stack_namesTheory.prog_comp_def,
         stack_removeTheory.compile_def,
         stack_removeTheory.init_stubs_def,
         subspt_def,
         lookup_fromAList,domain_fromAList,
         EVAL ``stack_names$comp f (halt_inst 0w)``]
  \\ first_x_assum(qspec_then`1`mp_tac) \\ simp[]
  \\ fs [stackSemTheory.evaluate_def,EVAL ``inst (Const n 0w) (dec_clock s)``,
         get_var_def,FLOOKUP_UPDATE]);
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
val full_make_init_semantics_3365 = Q.prove(
  `   full_make_init stack_conf data_conf max_heap sp offset
    (bitmaps:'a word list) code t save_regs data_sp coracle = (s,opt) ∧
   good_dimindex(:'a) ∧
   t.code = stack_to_lab$compile stack_conf data_conf max_heap sp offset code ∧
   t.compile_oracle = (λn.
     let (c,p,b) = coracle n in
       (c,compile_no_stubs stack_conf.reg_names stack_conf.jump offset sp p)) ∧
   ¬t.failed ∧
   memory_assumption stack_conf.reg_names bitmaps data_sp t ∧
   max_stack_alloc ≤ max_heap ∧
   t.link_reg ∉ save_regs ∧ t.pc = 0 ∧
   (∀k i n. k ∈ save_regs ⇒ t.io_regs n i k = NONE) ∧
   (∀k n. k ∈ save_regs ⇒ t.cc_regs n k = NONE) ∧
   (∀x. x ∈ t.mem_domain ⇒ w2n x MOD (dimindex(:'a) DIV 8) = 0) ∧
   (∀x. x ∈ t.shared_mem_domain ⇒ w2n x MOD (dimindex(:'a) DIV 8) = 0) ∧
   good_code sp code ∧
   (∀n. good_code sp (FST(SND(coracle n)))) ∧
   10 <= sp ∧
   EVERY (λr. (find_name stack_conf.reg_names (r+sp-2)) ∈ save_regs) [2;3;4] ∧
   find_name stack_conf.reg_names 4 = t.len2_reg ∧
   find_name stack_conf.reg_names 3 = t.ptr2_reg ∧
   find_name stack_conf.reg_names 2 = t.len_reg ∧
   find_name stack_conf.reg_names 1 = t.ptr_reg ∧
   find_name stack_conf.reg_names 0 = t.link_reg ∧
   BIJ (find_name stack_conf.reg_names) UNIV UNIV
   ⇒
   Abbrev (opt <> NONE /\ (semantics InitGlobals_location s ≠ Fail ⇒
   semantics t = semantics InitGlobals_location s))`,
  srw_tac[][full_make_init_def,GSYM contain_def]
  \\ last_x_assum mp_tac \\ LET_ELIM_TAC
  \\ rewrite_tac [contain_def]
  (* Prove the syntactic things for the oracle sequences *)
  \\ `semantics 0 s2 ≠ Fail ⇒ semantics t = semantics 0 s2`
  by (
    strip_tac
    \\ (GSYM stack_namesProofTheory.make_init_semantics
        |> Q.GENL[`code`,`f`,`s`,`start`,`oracle`]
        |> Q.ISPECL_THEN[`code2`,`stack_conf.reg_names`,`s3`,`0`,`coracle2`]mp_tac)
    \\ simp[]
    \\ impl_tac
    >- (
      simp[Abbr`s3`] \\ fs[good_code_def]
      \\ simp[make_init_def]
      \\ simp[Abbr`code2`]
      \\ simp[stack_removeTheory.compile_def,
              stack_removeProofTheory.prog_comp_eta,
              stack_removeTheory.init_stubs_def,
              MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\ simp[Abbr`code1`,stack_allocTheory.compile_def,
              stack_allocProofTheory.prog_comp_lambda,
              MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\ simp[stack_rawcallTheory.compile_def,
              MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
      \\  fs[ALL_DISTINCT_APPEND]
      \\ EVAL_TAC
      \\ fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,FORALL_PROD]
      \\ CCONTR_TAC \\ fs[] \\ res_tac
      \\ fs[backend_commonTheory.stack_num_stubs_def] )
    \\ disch_then (SUBST_ALL_TAC)
    \\ simp[Abbr`s3`]
    \\ match_mp_tac make_init_semantics
    \\ conj_tac
    >- ( simp[Abbr`code3`,Abbr`code2`,halt_assum_lemma] )
    \\ conj_tac
    >- (
      simp[state_rel_make_init] \\ fs[good_code_def]
      \\ conj_tac
      >- (
        simp[Abbr`code3`,lookup_fromAList]
        \\ simp[stack_to_labTheory.compile_def]
        \\ qmatch_goalsub_abbrev_tac`ALOOKUP code3`
        \\ `EVERY (λp. call_args p t.ptr_reg t.len_reg t.ptr2_reg t.len2_reg t.link_reg) (MAP SND code3)`
        by (
          rpt(qpat_x_assum`find_name _ _ = _`(sym_sub_tac))
          \\ match_mp_tac (GEN_ALL stack_namesProofTheory.stack_names_call_args)
          \\ qexists_tac`code2` \\ simp[]
          \\ match_mp_tac (GEN_ALL stack_removeProofTheory.stack_remove_call_args)
          \\ first_assum(part_match_exists_tac (fst o dest_conj) o (rconc o SYM_CONV o rand o concl))
          \\ simp[Abbr`code1`]
          \\ match_mp_tac (GEN_ALL stack_allocProofTheory.stack_alloc_call_args)
          \\ simp [stack_rawcallProofTheory.stack_alloc_call_args])
        \\ ntac 3 strip_tac
        \\ conj_tac
        >- (
          imp_res_tac ALOOKUP_MEM \\
          fs[EVERY_MAP,EVERY_MEM,FORALL_PROD]
          \\ metis_tac[] )
        \\ match_mp_tac code_installed_prog_to_section
        \\ simp[Abbr`code2`,Abbr`code1`,Abbr`ggc`,Abbr`code3`,Abbr`jump`]
        \\ (stack_to_lab_compile_lab_pres
            |> SIMP_RULE(srw_ss()++LET_ss)[stack_to_labTheory.compile_def]
            |> match_mp_tac)
        \\ simp[]
        \\ fs[EVERY_MEM,EVERY_MAP,EXISTS_PROD,FORALL_PROD]
        \\ rw[] \\ strip_tac \\ res_tac
        \\ rfs[backend_commonTheory.stack_num_stubs_def,stackLangTheory.gc_stub_location_eq] )
      \\ conj_tac
      >- (
        simp[FUN_EQ_THM,Abbr`coracle3`,Abbr`coracle2`,Abbr`coracle1`,compile_no_stubs_def]
        \\ simp[UNCURRY] )
      \\ conj_tac >-(
        strip_tac>>
        first_x_assum(qspec_then`k` assume_tac)>>fs[]>>
        Cases_on`coracle k`>>Cases_on`r`>>rfs[]>>
        unabbrev_all_tac>>fs[]>>
        old_drule stack_alloc_call_args>>
        strip_tac>>
        fs[stack_allocTheory.compile_def,PAIR_MAP]>>
        (* call_args preservation *)
        old_drule (stack_remove_call_args |> SIMP_RULE (srw_ss()) [EQ_SYM_EQ,Once CONJ_COMM] |> GEN_ALL) >> simp[]>>
        fs[stack_removeTheory.compile_def,FORALL_AND_THM,GSYM AND_IMP_INTRO]>>
        disch_then kall_tac>>
        disch_then(qspecl_then[`offset`,`sp`,`stack_conf.jump`] assume_tac)>>
        old_drule (stack_names_call_args |> SIMP_RULE (srw_ss()) [EQ_SYM_EQ,Once CONJ_COMM] |> GEN_ALL)>>
        simp[]>>
        disch_then(qspec_then`stack_conf.reg_names` assume_tac)>>rfs[]>>
        fs[Once EVERY_MEM,stack_namesTheory.compile_def,MEM_MAP,PULL_EXISTS,UNCURRY]>>
        reverse conj_tac>-
          fs[MAP_MAP_o,o_DEF,ETA_AX,prog_comp_eta,stack_allocProofTheory.prog_comp_lambda,UNCURRY]>>
        simp[FORALL_PROD,PULL_FORALL,prog_comp_eta,stack_allocProofTheory.prog_comp_lambda,stack_namesTheory.prog_comp_def]>>
        ntac 3 strip_tac>>
        rpt(first_x_assum old_drule>>strip_tac)>>
        fs[]>>
        imp_res_tac stack_alloc_lab_pres>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum(qspec_then`next_lab p_2 2` assume_tac)>>fs[]>>
        pairarg_tac>>fs[]>>
        metis_tac[stack_names_lab_pres,stack_remove_lab_pres])
      \\ conj_tac
      >- ( metis_tac[BIJ_DEF,IN_UNIV,DECIDE``0n <> 1 /\ 0n <> 2 /\ 1n <> 2``,INJ_DEF] )
      \\ conj_tac
      >- ( metis_tac[BIJ_DEF,IN_UNIV,DECIDE``0n <> 1 /\ 0n <> 2 /\ 1n <> 2``,INJ_DEF] )
      \\ conj_tac
      >- ( metis_tac[BIJ_DEF,IN_UNIV,
             DECIDE``0n <> 1 /\ 0n <> 2 /\ 0n <> 3 /\ 0n <> 4 /\ 1n <> 2 /\ 1n <> 3 /\ 2n <> 3``, INJ_DEF] )
      \\ conj_tac
      >- ( metis_tac[BIJ_DEF,IN_UNIV,
             DECIDE``0n <> 1 /\ 0n <> 2 /\ 0n <> 3 /\ 1n <> 2 /\ 1n <> 3``, INJ_DEF] )
      \\ simp[Abbr`code3`,domain_fromAList,Abbr`code2`]
      \\ conj_tac >-
        simp[stack_to_labTheory.compile_def,MAP_prog_to_section_Section_num]>>
      qmatch_goalsub_abbrev_tac`EVERY _ cc`>>
      `labels_ok cc` by
        (fs[Abbr`cc`]>>
        match_mp_tac stack_to_lab_compile_lab_pres>>
        fs[]>>
        `!n. stack_num_stubs ≤ n ⇒ n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gc_stub_location` by
          (EVAL_TAC>>fs[])>>
        fs[UNCURRY,EVERY_MEM,MEM_MAP,PULL_EXISTS])>>
      metis_tac[labels_ok_imp])
    \\ conj_tac
    >- (
      simp[stack_to_labTheory.compile_def,
           stack_namesTheory.compile_def,Abbr`code2`,
           stack_removeTheory.compile_def,
           stack_removeTheory.init_stubs_def,
           stack_namesTheory.prog_comp_def,
           prog_to_section_def] \\
      pairarg_tac \\ fs[Once loc_to_pc_def] )
    \\ rfs[])
  \\ `discharge_these stack_conf.jump offset ggc max_heap sp InitGlobals_location coracle1 code1 s2`
  by (
    simp[discharge_these_def] \\ fs[good_code_def]
    \\ simp[Abbr`s2`]
    \\ conj_tac
    >- (
      imp_res_tac stack_rawcallProofTheory.stack_rawcall_reg_bound \\
      imp_res_tac stack_alloc_reg_bound \\
      rfs[EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS,Abbr`code1`] \\
      first_x_assum(qspec_then`data_conf`mp_tac) \\ simp[] \\
      ntac 4 strip_tac \\
      conj_tac >- metis_tac[] \\
      fs[stack_allocTheory.compile_def,stack_allocTheory.stubs_def]
      >- EVAL_TAC
      \\ fs[stack_allocProofTheory.prog_comp_lambda,MEM_MAP,EXISTS_PROD,
            stack_rawcallTheory.compile_def]
      \\ res_tac \\ fs[] )
    \\ simp[stack_namesProofTheory.make_init_def,Abbr`code2`,Abbr`s3`,make_init_def]
    \\ simp[domain_fromAList]
    \\ conj_tac >-(
      ntac 4 strip_tac>>
      first_x_assum(qspec_then`n` assume_tac)>>
      Cases_on`coracle n`>>Cases_on`r`>>fs[]>>
      fs[Abbr`coracle1`]>>
      old_drule (GEN_ALL stack_alloc_reg_bound)>>
      disch_then old_drule>>
      disch_then(qspec_then `ARB` assume_tac)>>
      fs[stack_allocTheory.compile_def]>>
      fs[Once EVERY_MAP,LAMBDA_PROD,EVERY_MEM,FORALL_PROD]>>
      conj_tac>-
        metis_tac[]>>
      fs[stack_allocProofTheory.prog_comp_lambda,MEM_MAP,UNCURRY]>>
      Cases_on`y`>>fs[]>>
      rpt(first_x_assum old_drule)>>
      fs[])
    \\ conj_tac >- EVAL_TAC
    \\ fs[]
    \\ metis_tac[LINV_DEF,IN_UNIV,BIJ_DEF] ) \\
  `propagate_these s2 bitmaps data_sp` by (
    fs[propagate_these_def,Abbr`s2`,Abbr`s3`,
        stack_namesProofTheory.make_init_def,
        make_init_def,BIJ_FLOOKUP_MAP_KEYS,
        flookup_fupdate_list]
    \\ fs[memory_assumption_def]) \\
  `t.ffi = s2.ffi` by
    (unabbrev_all_tac>>EVAL_TAC)
  \\ (stack_allocProofTheory.make_init_semantics
      |> Q.GENL[`start`,`c`,`s`,`oracle`,`code`]
      |> Q.ISPECL_THEN[`InitGlobals_location`,`data_conf`,`s1`,
               `coracle`,`stack_rawcall$compile code`]mp_tac)
  \\ `¬(stack_num_stubs ≤ gc_stub_location)` by EVAL_TAC
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [GSYM AND_IMP_INTRO]
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ impl_tac
  >- (
    fs[good_code_def] \\
    conj_tac >- (
      simp [stack_rawcallTheory.compile_def,ALOOKUP_MAP,PULL_EXISTS]
      \\ ntac 3 strip_tac \\ imp_res_tac ALOOKUP_MEM
      \\ fs[EVERY_MEM,FORALL_PROD,stack_rawcallProofTheory.call_arg_comp]
      \\ metis_tac[]) \\
    conj_tac >- (
      `!k. stack_num_stubs ≤ k ⇒ k ≠ gc_stub_location` by
        (EVAL_TAC>>fs[])>>
      fs[EVERY_MEM,UNCURRY]>>
      metis_tac[FST,SND])
    \\ simp[Abbr`s1`,make_init_any_use_stack,make_init_any_use_store,
            make_init_any_use_alloc,make_init_any_code,make_init_any_bitmaps,
            make_init_any_stack_limit,make_init_any_compile_oracle]
    \\ simp[make_init_any_def,stack_rawcallProofTheory.MAP_FST_compile]
    \\ fs[make_init_opt_def,case_eq_thms,init_prop_def,init_reduce_def]
    \\ rw[] \\ fs [good_dimindex_def,dimword_def])
  \\ disch_then(assume_tac o GSYM)
  \\ old_drule stack_removeProofTheory.make_init_semantics
  \\ simp [] \\ strip_tac \\ simp []
  \\ fs [] \\ rveq \\ fs []
  \\ rewrite_tac [markerTheory.Abbrev_def] \\ rw []
  \\ fs[make_init_any_def]
  \\ first_assum (mp_then (Pos last) mp_tac stack_rawcallProofTheory.compile_semantics)
  \\ disch_then (qspec_then `code` mp_tac)
  \\ impl_tac THEN1 fs [stack_allocProofTheory.make_init_def,good_code_def]
  \\ qmatch_goalsub_abbrev_tac `semantics _ m1`
  \\ rename [`(make_init data_conf (fromAList code) coracle s0)`]
  \\ `m1 = make_init data_conf (fromAList (stack_rawcall$compile code)) coracle s0` by
    simp [Abbr`m1`,stack_allocProofTheory.make_init_def]
  \\ rveq \\ fs []
  \\ metis_tac []);
val _ = checked "full_make_init_semantics_3365_statement" full_make_init_semantics_3365;
val _ = checked "full_make_init_semantics_3617_statement" stack_to_labProofTheory.full_make_init_semantics;
