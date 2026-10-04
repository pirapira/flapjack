(* Literal source-theorem replay of pan_to_targetProof 909-1166 (no_alloc_word_evaluate,
   the panLang stack-size constancy group and option_lt_SOME). The original proof theory is
   unbuilt; every statement and HOL's own proof are replayed in source order over the loaded
   original theories, with the script's word_to_word_compile/pan_to_word_compile_prog
   overloads and option_lt definition. This is not an exported original-theory capture. *)
load "bossLib"; load "preamble"; load "word_to_wordProofTheory"; load "wordConvsProofTheory";
load "wordPropsTheory"; load "pan_to_wordProofTheory"; load "pan_to_targetTheory"; load "targetSemTheory";
open bossLib HolKernel Parse preamble pan_to_wordProofTheory;
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "pancake/proofs/pan_to_targetProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;
fun guard name lit = if String.isSubstring lit source_text then ()
  else raise Fail (name ^ " literal source changed");
val _ = guard "overloads" "Overload word_to_word_compile[local] = ``word_to_word$compile``";
val _ = guard "overloads" "Overload pan_to_word_compile_prog[local] = ``pan_to_word$compile_prog``";
val _ = guard "option_lt_def" "Definition option_lt_def[simp]:\n  (option_lt n0 NONE \226\135\148 T) \226\136\167 (option_lt NONE (SOME n1) \226\135\148 F) \226\136\167\n  (option_lt (SOME n1) (SOME n2) \226\135\148 n1 < n2:num)\nEnd";
val _ = new_theory "flapjack_pan_to_target_stack_size_source_replay";
val _ = overload_on ("word_to_word_compile", ``word_to_word$compile``);
val _ = overload_on ("pan_to_word_compile_prog", ``pan_to_word$compile_prog``);
val option_lt_def = Define `
  (option_lt n0 NONE <=> T) /\ (option_lt NONE (SOME n1) <=> F) /\
  (option_lt (SOME n1) (SOME n2) <=> n1 < n2:num)`;
val _ = augment_srw_ss [rewrites [option_lt_def]];
val _ = guard "word_to_word_compile_no_install_no_alloc" "Theorem word_to_word_compile_no_install_no_alloc:\n  word_to_word$compile wconf aconf progs0 = (col, progs) \226\136\167\n  ALL_DISTINCT (MAP FST progs0) \226\136\167\n  no_mt_code (fromAList progs0) \226\136\167\n  no_install_code (fromAList progs0) \226\135\146\n  no_install_code (fromAList progs) \226\136\167\n  (no_alloc_code (fromAList progs0) \226\135\146 no_alloc_code (fromAList progs))\nProof\n  strip_tac>>gs[word_to_wordTheory.compile_def]>>\n  rpt (pairarg_tac>>gs[])>>\n  gvs[]>>\n  DEP_REWRITE_TAC[word_to_wordProofTheory.no_mt_code_full_compile_single]>>\n  simp []>>\n  conj_asm1_tac >- (\n    fs[word_to_wordTheory.next_n_oracle_def]>>every_case_tac>>gvs[]\n  )>>\n  fs[wordPropsTheory.no_install_code_def, wordPropsTheory.no_alloc_code_def,\n        lookup_fromAList]>>\n  fs[wordConvsTheory.no_install_subprogs_def,\n        wordConvsTheory.no_alloc_subprogs_def]>>\n  rw[]>>drule ALOOKUP_MEM>>strip_tac>>\n  gs[PAIR_FST_SND_EQ, MEM_MAP]>>\n  irule wordConvsProofTheory.compile_single_not_created_subprogs>>\n  first_x_assum irule>>\n  gs[MEM_ZIP]>>\n  drule_at Any ALOOKUP_ALL_DISTINCT_EL>>\n  rw[]>>\n  drule_then (irule_at Any) EQ_TRANS>>\n  simp[PAIR_FST_SND_EQ]\nQED";
val word_to_word_compile_no_install_no_alloc = store_thm("word_to_word_compile_no_install_no_alloc",
``  word_to_word$compile wconf aconf progs0 = (col, progs) ∧
  ALL_DISTINCT (MAP FST progs0) ∧
  no_mt_code (fromAList progs0) ∧
  no_install_code (fromAList progs0) ⇒
  no_install_code (fromAList progs) ∧
  (no_alloc_code (fromAList progs0) ⇒ no_alloc_code (fromAList progs))``,
  strip_tac>>gs[word_to_wordTheory.compile_def]>>
  rpt (pairarg_tac>>gs[])>>
  gvs[]>>
  DEP_REWRITE_TAC[word_to_wordProofTheory.no_mt_code_full_compile_single]>>
  simp []>>
  conj_asm1_tac >- (
    fs[word_to_wordTheory.next_n_oracle_def]>>every_case_tac>>gvs[]
  )>>
  fs[wordPropsTheory.no_install_code_def, wordPropsTheory.no_alloc_code_def,
        lookup_fromAList]>>
  fs[wordConvsTheory.no_install_subprogs_def,
        wordConvsTheory.no_alloc_subprogs_def]>>
  rw[]>>drule ALOOKUP_MEM>>strip_tac>>
  gs[PAIR_FST_SND_EQ, MEM_MAP]>>
  irule wordConvsProofTheory.compile_single_not_created_subprogs>>
  first_x_assum irule>>
  gs[MEM_ZIP]>>
  drule_at Any ALOOKUP_ALL_DISTINCT_EL>>
  rw[]>>
  drule_then (irule_at Any) EQ_TRANS>>
  simp[PAIR_FST_SND_EQ]);
val _ = guard "no_alloc_word_evaluate" "Theorem no_alloc_word_evaluate:\n  \226\136\128prog s res t.\n  wordSem$evaluate (prog,s) = (res,t) \226\136\167\n  no_install_code s.code \226\136\167 no_alloc_code s.code \226\136\167\n  no_install prog \226\136\167 no_alloc prog \226\135\146\n  res \226\137\160 SOME NotEnoughSpace\nProof\n  recInduct (name_ind_cases [] wordSemTheory.evaluate_ind)>>\n  rw[wordConvsTheory.no_alloc_def,\n     wordConvsTheory.no_install_def,\n     wordConvsTheory.no_mt_def,\n     wordSemTheory.evaluate_def]\n  >~ [`Case (Call _ _ _ _, _)`]\n  >- (\n    fs [CaseEq \"option\", CaseEq \"word_loc\", CaseEq \"bool\"] >> gvs [] >>\n    fs [CaseEq \"prod\"] >> gvs [] >>\n    drule wordPropsTheory.no_alloc_find_code >>\n    drule_at (Pos (el 2)) wordPropsTheory.no_install_find_code >>\n    CCONTR_TAC >> gs [] >>\n    fs [CaseEq \"option\", CaseEq \"bool\", CaseEq \"prod\"] >>\n    imp_res_tac wordPropsTheory.no_install_evaluate_const_code >>\n    gvs [] >>\n    fs[AllCaseEqs (), UNCURRY_eq_pair, wordSemTheory.set_var_def,\n       wordSemTheory.pop_env_def] >> gvs []\n  )\n  >~ [`Case (ShareInst op _ _, _)`]\n  >- (\n    fs [CaseEq \"option\", CaseEq \"word_loc\"] >>\n    Cases_on `op` >>\n    gs[wordSemTheory.share_inst_def,\n         wordSemTheory.sh_mem_load_def, wordSemTheory.sh_mem_load_byte_def,\n         wordSemTheory.sh_mem_store_def, wordSemTheory.sh_mem_store_byte_def,\n         wordSemTheory.sh_mem_load16_def, wordSemTheory.sh_mem_store16_def,\n         wordSemTheory.sh_mem_load32_def, wordSemTheory.sh_mem_store32_def,\n         ffiTheory.call_FFI_def]>>\n    every_case_tac>>\n    fs[wordSemTheory.sh_mem_set_var_def,\n         wordSemTheory.set_var_def, wordSemTheory.flush_state_def]>>\n    gvs[]\n  )\n  >~ [`Case (Loop _ _ _, _)`]\n  >- (\n    CCONTR_TAC >> fs[] >>\n    gvs[AllCaseEqs(), UNCURRY_eq_pair] >>\n    imp_res_tac wordPropsTheory.cut_state_const >>\n    imp_res_tac wordPropsTheory.no_install_evaluate_const_code >>\n    gs[wordSemTheory.STOP_def, wordConvsTheory.no_install_def,\n       wordConvsTheory.no_alloc_def] >>\n    Cases_on `res` >> gvs[wordSemTheory.exit_loop_def] >>\n    rename1 `SOME r` >>\n    Cases_on `r` >>\n    gvs[wordSemTheory.exit_loop_def, wordSemTheory.cont_loop_def]\n  )\n  >>\n  CCONTR_TAC>> fs[]>>\n  fs[AllCaseEqs (), UNCURRY_eq_pair]>>\n  imp_res_tac wordPropsTheory.no_install_evaluate_const_code>>\n  gs[]\nQED";
val no_alloc_word_evaluate = store_thm("no_alloc_word_evaluate",
``  ∀prog s res t.
  wordSem$evaluate (prog,s) = (res,t) ∧
  no_install_code s.code ∧ no_alloc_code s.code ∧
  no_install prog ∧ no_alloc prog ⇒
  res ≠ SOME NotEnoughSpace``,
  recInduct (name_ind_cases [] wordSemTheory.evaluate_ind)>>
  rw[wordConvsTheory.no_alloc_def,
     wordConvsTheory.no_install_def,
     wordConvsTheory.no_mt_def,
     wordSemTheory.evaluate_def]
  >~ [`Case (Call _ _ _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc", CaseEq "bool"] >> gvs [] >>
    fs [CaseEq "prod"] >> gvs [] >>
    drule wordPropsTheory.no_alloc_find_code >>
    drule_at (Pos (el 2)) wordPropsTheory.no_install_find_code >>
    CCONTR_TAC >> gs [] >>
    fs [CaseEq "option", CaseEq "bool", CaseEq "prod"] >>
    imp_res_tac wordPropsTheory.no_install_evaluate_const_code >>
    gvs [] >>
    fs[AllCaseEqs (), UNCURRY_eq_pair, wordSemTheory.set_var_def,
       wordSemTheory.pop_env_def] >> gvs []
  )
  >~ [`Case (ShareInst op _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc"] >>
    Cases_on `op` >>
    gs[wordSemTheory.share_inst_def,
         wordSemTheory.sh_mem_load_def, wordSemTheory.sh_mem_load_byte_def,
         wordSemTheory.sh_mem_store_def, wordSemTheory.sh_mem_store_byte_def,
         wordSemTheory.sh_mem_load16_def, wordSemTheory.sh_mem_store16_def,
         wordSemTheory.sh_mem_load32_def, wordSemTheory.sh_mem_store32_def,
         ffiTheory.call_FFI_def]>>
    every_case_tac>>
    fs[wordSemTheory.sh_mem_set_var_def,
         wordSemTheory.set_var_def, wordSemTheory.flush_state_def]>>
    gvs[]
  )
  >~ [`Case (Loop _ _ _, _)`]
  >- (
    CCONTR_TAC >> fs[] >>
    gvs[AllCaseEqs(), UNCURRY_eq_pair] >>
    imp_res_tac wordPropsTheory.cut_state_const >>
    imp_res_tac wordPropsTheory.no_install_evaluate_const_code >>
    gs[wordSemTheory.STOP_def, wordConvsTheory.no_install_def,
       wordConvsTheory.no_alloc_def] >>
    Cases_on `res` >> gvs[wordSemTheory.exit_loop_def] >>
    rename1 `SOME r` >>
    Cases_on `r` >>
    gvs[wordSemTheory.exit_loop_def, wordSemTheory.cont_loop_def]
  )
  >>
  CCONTR_TAC>> fs[]>>
  fs[AllCaseEqs (), UNCURRY_eq_pair]>>
  imp_res_tac wordPropsTheory.no_install_evaluate_const_code>>
  gs[]);
val _ = guard "panLang_wordSem_neq_NotEnoughSpace" "Theorem panLang_wordSem_neq_NotEnoughSpace:\n  evaluate (Call NONE (SOME start) [0] NONE, s with clock := k) = (res, t) \226\136\167\n  ALL_DISTINCT (MAP FST (functions pan_code)) \226\136\167\n  word_to_word_compile c.word_to_word_conf mc.target.config\n                       (pan_to_word_compile_prog mc.target.config.ISA pan_code) = (col,wprog) \226\136\167\n  s.code = fromAList wprog \226\135\146\n  res \226\137\160 SOME NotEnoughSpace\nProof\n  rw[]>>\n  qmatch_asmsub_abbrev_tac \226\128\152wordSem$evaluate (prg, _) = _\226\128\153 >>\n  \226\128\152no_install prg /\\ no_alloc prg /\\ no_mt prg\226\128\153\n    by gs[wordConvsTheory.no_alloc_def, wordConvsTheory.no_install_def,\n          wordConvsTheory.no_mt_def, Abbr \226\128\152prg\226\128\153]>>\n  qmatch_asmsub_abbrev_tac \226\128\152word_to_word_compile _ _ wprog0\226\128\153>>\n  qpat_x_assum \226\128\152Abbrev (_ = _)\226\128\153 (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>\n  \226\128\152ALL_DISTINCT (MAP FST wprog0)\226\128\153\n    by (drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>\n        strip_tac>>gvs[])>>\n  drule_then irule no_alloc_word_evaluate >>\n  imp_res_tac pan_to_word_compile_prog_no_install_code>>\n  imp_res_tac pan_to_word_compile_prog_no_alloc_code>>\n  imp_res_tac pan_to_word_compile_prog_no_mt_code>>\n  drule word_to_word_compile_no_install_no_alloc>>\n  simp []\nQED";
val panLang_wordSem_neq_NotEnoughSpace = store_thm("panLang_wordSem_neq_NotEnoughSpace",
``  evaluate (Call NONE (SOME start) [0] NONE, s with clock := k) = (res, t) ∧
  ALL_DISTINCT (MAP FST (functions pan_code)) ∧
  word_to_word_compile c.word_to_word_conf mc.target.config
                       (pan_to_word_compile_prog mc.target.config.ISA pan_code) = (col,wprog) ∧
  s.code = fromAList wprog ⇒
  res ≠ SOME NotEnoughSpace``,
  rw[]>>
  qmatch_asmsub_abbrev_tac ‘wordSem$evaluate (prg, _) = _’ >>
  ‘no_install prg /\ no_alloc prg /\ no_mt prg’
    by gs[wordConvsTheory.no_alloc_def, wordConvsTheory.no_install_def,
          wordConvsTheory.no_mt_def, Abbr ‘prg’]>>
  qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0’>>
  qpat_x_assum ‘Abbrev (_ = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
  ‘ALL_DISTINCT (MAP FST wprog0)’
    by (drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
        strip_tac>>gvs[])>>
  drule_then irule no_alloc_word_evaluate >>
  imp_res_tac pan_to_word_compile_prog_no_install_code>>
  imp_res_tac pan_to_word_compile_prog_no_alloc_code>>
  imp_res_tac pan_to_word_compile_prog_no_mt_code>>
  drule word_to_word_compile_no_install_no_alloc>>
  simp []);
val _ = guard "inst_stack_size_const_panLang" "Theorem inst_stack_size_const_panLang:\n  \226\136\128i s t.\n  wordSem$inst i s = SOME t ==>\n  t.stack_size = s.stack_size\nProof\n  Induct>>rw[wordSemTheory.inst_def,wordSemTheory.assign_def]>>\n  fs [AllCaseEqs (), UNCURRY_eq_pair] >>\n  gvs [wordSemTheory.word_exp_def,\n          wordSemTheory.set_var_def,\n          wordSemTheory.mem_store_def,\n          wordSemTheory.get_fp_var_def,\n          wordSemTheory.get_var_def,\n          wordSemTheory.get_vars_def]\nQED";
val inst_stack_size_const_panLang = store_thm("inst_stack_size_const_panLang",
``  ∀i s t.
  wordSem$inst i s = SOME t ==>
  t.stack_size = s.stack_size``,
  Induct>>rw[wordSemTheory.inst_def,wordSemTheory.assign_def]>>
  fs [AllCaseEqs (), UNCURRY_eq_pair] >>
  gvs [wordSemTheory.word_exp_def,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_fp_var_def,
          wordSemTheory.get_var_def,
          wordSemTheory.get_vars_def]);
val _ = guard "inst_stack_limit_const_panLang" "Theorem inst_stack_limit_const_panLang:\n  \226\136\128i s t.\n  wordSem$inst i s = SOME t ==>\n  t.stack_limit = s.stack_limit\nProof\n  Induct>>rw[wordSemTheory.inst_def,wordSemTheory.assign_def]>>\n  fs [AllCaseEqs (), UNCURRY_eq_pair] >>\n  gvs[wordSemTheory.word_exp_def,\n          wordSemTheory.set_var_def,\n          wordSemTheory.mem_store_def,\n          wordSemTheory.get_fp_var_def,\n          wordSemTheory.get_var_def,\n          wordSemTheory.get_vars_def]\nQED";
val inst_stack_limit_const_panLang = store_thm("inst_stack_limit_const_panLang",
``  ∀i s t.
  wordSem$inst i s = SOME t ==>
  t.stack_limit = s.stack_limit``,
  Induct>>rw[wordSemTheory.inst_def,wordSemTheory.assign_def]>>
  fs [AllCaseEqs (), UNCURRY_eq_pair] >>
  gvs[wordSemTheory.word_exp_def,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_fp_var_def,
          wordSemTheory.get_var_def,
          wordSemTheory.get_vars_def]);
val _ = guard "inst_stack_max_const_panLang" "Theorem inst_stack_max_const_panLang:\n  \226\136\128i s t.\n  wordSem$inst i s = SOME t ==>\n  t.stack_max = s.stack_max\nProof\n  Induct>>rw[wordSemTheory.inst_def,wordSemTheory.assign_def]>>\n  fs [AllCaseEqs (), UNCURRY_eq_pair] >>\n  gvs[wordSemTheory.word_exp_def,\n          wordSemTheory.set_var_def,\n          wordSemTheory.mem_store_def,\n          wordSemTheory.get_fp_var_def,\n          wordSemTheory.get_var_def,\n          wordSemTheory.get_vars_def]\nQED";
val inst_stack_max_const_panLang = store_thm("inst_stack_max_const_panLang",
``  ∀i s t.
  wordSem$inst i s = SOME t ==>
  t.stack_max = s.stack_max``,
  Induct>>rw[wordSemTheory.inst_def,wordSemTheory.assign_def]>>
  fs [AllCaseEqs (), UNCURRY_eq_pair] >>
  gvs[wordSemTheory.word_exp_def,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_fp_var_def,
          wordSemTheory.get_var_def,
          wordSemTheory.get_vars_def]);
val _ = guard "share_inst_modifies" "Theorem share_inst_modifies:\n  wordSem$share_inst op v ad s = (res, t) ==>\n  ? ls ffi stk lsz st.\n  t = (s with <| locals := ls; ffi := ffi;\n        stack := stk; locals_size := lsz; store := st |>)\nProof\n  Cases_on \226\128\152op\226\128\153>>\n  gs[wordSemTheory.share_inst_def,\n     wordSemTheory.sh_mem_load_def,\n     wordSemTheory.sh_mem_load_def,\n     wordSemTheory.sh_mem_load_byte_def,\n     wordSemTheory.sh_mem_load16_def,\n     wordSemTheory.sh_mem_load32_def,\n     wordSemTheory.sh_mem_store_def,\n     wordSemTheory.sh_mem_store_byte_def,\n     wordSemTheory.sh_mem_store16_def,\n     wordSemTheory.sh_mem_store32_def,\n     ffiTheory.call_FFI_def]>>\n  every_case_tac >>\n  fs[wordSemTheory.sh_mem_set_var_def,\n         wordSemTheory.set_var_def,\n         wordSemTheory.flush_state_def]>>gvs[] >>\n  rw [] >>\n  simp [wordSemTheory.state_component_equality]\nQED";
val share_inst_modifies = store_thm("share_inst_modifies",
``  wordSem$share_inst op v ad s = (res, t) ==>
  ? ls ffi stk lsz st.
  t = (s with <| locals := ls; ffi := ffi;
        stack := stk; locals_size := lsz; store := st |>)``,
  Cases_on ‘op’>>
  gs[wordSemTheory.share_inst_def,
     wordSemTheory.sh_mem_load_def,
     wordSemTheory.sh_mem_load_def,
     wordSemTheory.sh_mem_load_byte_def,
     wordSemTheory.sh_mem_load16_def,
     wordSemTheory.sh_mem_load32_def,
     wordSemTheory.sh_mem_store_def,
     wordSemTheory.sh_mem_store_byte_def,
     wordSemTheory.sh_mem_store16_def,
     wordSemTheory.sh_mem_store32_def,
     ffiTheory.call_FFI_def]>>
  every_case_tac >>
  fs[wordSemTheory.sh_mem_set_var_def,
         wordSemTheory.set_var_def,
         wordSemTheory.flush_state_def]>>gvs[] >>
  rw [] >>
  simp [wordSemTheory.state_component_equality]);
val _ = guard "evaluate_stack_size_limit_const_panLang" "Theorem evaluate_stack_size_limit_const_panLang:\n  \226\136\128prog s res t.\n  wordSem$evaluate (prog, s) = (res,t) \226\136\167\n  no_install prog \226\136\167 no_install_code s.code \226\136\167\n  no_alloc prog \226\136\167 no_alloc_code s.code ==>\n  t.stack_size = s.stack_size /\\ t.stack_limit = s.stack_limit\nProof\n  recInduct (name_ind_cases [] wordSemTheory.evaluate_ind)>>\n  simp[wordSemTheory.evaluate_def,wordSemTheory.flush_state_def]>>\n  rpt conj_tac>>rpt (gen_tac ORELSE disch_tac)>>\n  gs[wordConvsTheory.no_install_def,\n     wordConvsTheory.no_alloc_def,\n     wordConvsTheory.no_mt_def,\n     wordSemTheory.jump_exc_def,\n     wordSemTheory.get_var_def, wordSemTheory.mem_store_def]\n  >~ [`Case (Call _ _ _ _, _)`]\n  >- (\n    fs [CaseEq \"option\"]\n    \\\\ fs [CaseEq \"option\", CaseEq \"prod\", CaseEq \"bool\"] \\\\ gvs []\n    \\\\ imp_res_tac wordPropsTheory.no_install_find_code\n    \\\\ imp_res_tac wordPropsTheory.no_alloc_find_code\n    \\\\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code\n    \\\\ gs []\n    \\\\ gs [wordSemTheory.set_var_def, wordSemTheory.call_env_def,\n         wordSemTheory.pop_env_def]\n    \\\\ fs [AllCaseEqs (), UNCURRY_eq_pair] \\\\ gvs []\n  )\n  >~ [`Case (Inst _, _)`]\n  >- (\n    fs [AllCaseEqs (), UNCURRY_eq_pair] \\\\ gvs []\n    \\\\ drule inst_stack_size_const_panLang\n    \\\\ drule inst_stack_limit_const_panLang\n    \\\\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code\n    \\\\ imp_res_tac share_inst_modifies\n    \\\\ gs []\n    \\\\ imp_res_tac wordPropsTheory.cut_state_const \\\\ gvs []\n    \\\\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code \\\\ gs []\n    \\\\ gs [wordSemTheory.STOP_def, wordConvsTheory.no_install_def,\n           wordConvsTheory.no_alloc_def]\n  )\n  \\\\ fs [AllCaseEqs (), UNCURRY_eq_pair] \\\\ gvs []\n  \\\\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code\n  \\\\ imp_res_tac share_inst_modifies\n  \\\\ gs []\n  \\\\ imp_res_tac wordPropsTheory.cut_state_const \\\\ gvs []\n  \\\\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code \\\\ gs []\n  \\\\ gs [wordSemTheory.STOP_def, wordConvsTheory.no_install_def,\n         wordConvsTheory.no_alloc_def]\nQED";
val evaluate_stack_size_limit_const_panLang = store_thm("evaluate_stack_size_limit_const_panLang",
``  ∀prog s res t.
  wordSem$evaluate (prog, s) = (res,t) ∧
  no_install prog ∧ no_install_code s.code ∧
  no_alloc prog ∧ no_alloc_code s.code ==>
  t.stack_size = s.stack_size /\ t.stack_limit = s.stack_limit``,
  recInduct (name_ind_cases [] wordSemTheory.evaluate_ind)>>
  simp[wordSemTheory.evaluate_def,wordSemTheory.flush_state_def]>>
  rpt conj_tac>>rpt (gen_tac ORELSE disch_tac)>>
  gs[wordConvsTheory.no_install_def,
     wordConvsTheory.no_alloc_def,
     wordConvsTheory.no_mt_def,
     wordSemTheory.jump_exc_def,
     wordSemTheory.get_var_def, wordSemTheory.mem_store_def]
  >~ [`Case (Call _ _ _ _, _)`]
  >- (
    fs [CaseEq "option"]
    \\ fs [CaseEq "option", CaseEq "prod", CaseEq "bool"] \\ gvs []
    \\ imp_res_tac wordPropsTheory.no_install_find_code
    \\ imp_res_tac wordPropsTheory.no_alloc_find_code
    \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code
    \\ gs []
    \\ gs [wordSemTheory.set_var_def, wordSemTheory.call_env_def,
         wordSemTheory.pop_env_def]
    \\ fs [AllCaseEqs (), UNCURRY_eq_pair] \\ gvs []
  )
  >~ [`Case (Inst _, _)`]
  >- (
    fs [AllCaseEqs (), UNCURRY_eq_pair] \\ gvs []
    \\ drule inst_stack_size_const_panLang
    \\ drule inst_stack_limit_const_panLang
    \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code
    \\ imp_res_tac share_inst_modifies
    \\ gs []
    \\ imp_res_tac wordPropsTheory.cut_state_const \\ gvs []
    \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code \\ gs []
    \\ gs [wordSemTheory.STOP_def, wordConvsTheory.no_install_def,
           wordConvsTheory.no_alloc_def]
  )
  \\ fs [AllCaseEqs (), UNCURRY_eq_pair] \\ gvs []
  \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code
  \\ imp_res_tac share_inst_modifies
  \\ gs []
  \\ imp_res_tac wordPropsTheory.cut_state_const \\ gvs []
  \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code \\ gs []
  \\ gs [wordSemTheory.STOP_def, wordConvsTheory.no_install_def,
         wordConvsTheory.no_alloc_def]);
val _ = guard "option_lt_SOME" "Theorem option_lt_SOME:\n  option_lt x (SOME n) = (\226\136\131m. x = SOME m \226\136\167 m < n)\nProof\n  Cases_on \226\128\152x\226\128\153>>fs[]\nQED";
val option_lt_SOME = store_thm("option_lt_SOME",
``  option_lt x (SOME n) = (∃m. x = SOME m ∧ m < n)``,
  Cases_on ‘x’>>fs[]);
fun pr_stmt label th = (print (label ^ "="); print_term (concl th); print "\n");
fun pr_hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun pr_typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
val _ = Globals.linewidth := 1000000;
val _ = pr_stmt "no_alloc_word_evaluate_replay_statement" no_alloc_word_evaluate;
val _ = pr_hyps "no_alloc_word_evaluate_replay_hypotheses" no_alloc_word_evaluate;
val _ = pr_typed "no_alloc_word_evaluate_replay_typed" no_alloc_word_evaluate;
val _ = pr_stmt "panLang_wordSem_neq_NotEnoughSpace_replay_statement" panLang_wordSem_neq_NotEnoughSpace;
val _ = pr_hyps "panLang_wordSem_neq_NotEnoughSpace_replay_hypotheses" panLang_wordSem_neq_NotEnoughSpace;
val _ = pr_typed "panLang_wordSem_neq_NotEnoughSpace_replay_typed" panLang_wordSem_neq_NotEnoughSpace;
val _ = pr_stmt "inst_stack_size_const_panLang_replay_statement" inst_stack_size_const_panLang;
val _ = pr_hyps "inst_stack_size_const_panLang_replay_hypotheses" inst_stack_size_const_panLang;
val _ = pr_typed "inst_stack_size_const_panLang_replay_typed" inst_stack_size_const_panLang;
val _ = pr_stmt "inst_stack_limit_const_panLang_replay_statement" inst_stack_limit_const_panLang;
val _ = pr_hyps "inst_stack_limit_const_panLang_replay_hypotheses" inst_stack_limit_const_panLang;
val _ = pr_typed "inst_stack_limit_const_panLang_replay_typed" inst_stack_limit_const_panLang;
val _ = pr_stmt "inst_stack_max_const_panLang_replay_statement" inst_stack_max_const_panLang;
val _ = pr_hyps "inst_stack_max_const_panLang_replay_hypotheses" inst_stack_max_const_panLang;
val _ = pr_typed "inst_stack_max_const_panLang_replay_typed" inst_stack_max_const_panLang;
val _ = pr_stmt "share_inst_modifies_replay_statement" share_inst_modifies;
val _ = pr_hyps "share_inst_modifies_replay_hypotheses" share_inst_modifies;
val _ = pr_typed "share_inst_modifies_replay_typed" share_inst_modifies;
val _ = pr_stmt "evaluate_stack_size_limit_const_panLang_replay_statement" evaluate_stack_size_limit_const_panLang;
val _ = pr_hyps "evaluate_stack_size_limit_const_panLang_replay_hypotheses" evaluate_stack_size_limit_const_panLang;
val _ = pr_typed "evaluate_stack_size_limit_const_panLang_replay_typed" evaluate_stack_size_limit_const_panLang;
val _ = pr_stmt "option_lt_SOME_replay_statement" option_lt_SOME;
val _ = pr_hyps "option_lt_SOME_replay_hypotheses" option_lt_SOME;
val _ = pr_typed "option_lt_SOME_replay_typed" option_lt_SOME;
