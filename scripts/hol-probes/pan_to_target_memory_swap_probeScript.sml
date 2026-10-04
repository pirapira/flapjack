load "preamble"; load "wordSemTheory"; load "set_sepTheory"; load "miscTheory"; load "wordPropsTheory"; load "wordConvsProofTheory"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble wordSemTheory;
val _ = new_theory "flapjack_pan_to_target_memory_swap_replay";
val _ = Globals.linewidth := 1000000;
(* Literal source replay of pan_to_targetProofScript 336-908 (pan_to_targetProofTheory is not built here). *)
(* memory update *)
Theorem fun2set_update_eq[simp]:
  fun2set (m, md) = fun2set (m', md) ⇒
  fun2set (m⦇x ↦ a⦈, md) = fun2set (m'⦇x ↦ a⦈, md)
Proof
  strip_tac>>
  gs[set_sepTheory.fun2set_eq,UPDATE_def]>>
  IF_CASES_TAC>>gs[]
QED

Theorem get_var_const_memory[simp]:
  wordSem$get_var x (y with memory := m) = get_var x y
Proof
  gs[wordSemTheory.get_var_def]
QED

Theorem set_var_const_memory[simp]:
  wordSem$set_var v x (y with memory := m) = (set_var v x y) with memory := m
Proof
  gs[wordSemTheory.set_var_def]
QED

Theorem unset_var_const_memory[simp]:
  wordSem$unset_var v (y with memory := m) = (unset_var v y) with memory := m
Proof
  gs[wordSemTheory.unset_var_def]
QED

Theorem get_vars_const_memory[simp]:
  wordSem$get_vars x (y with memory := m) = get_vars x y
Proof
  Induct_on`x`>>srw_tac[][wordSemTheory.get_vars_def]
QED

Theorem set_vars_const_memory[simp]:
  wordSem$set_vars vs xs (y with memory := m) = (set_vars vs xs y) with memory := m
Proof
  Induct_on`xs`>>srw_tac[][wordSemTheory.set_vars_def]
QED

Theorem get_var_imm_const_memory[simp]:
  wordSem$get_var_imm ri (s with memory := m) = get_var_imm ri s
Proof
  Cases_on ‘ri’>>gs[wordSemTheory.get_var_imm_def]
QED

Theorem mem_load_const_memory[simp]:
  fun2set (s.memory,s.mdomain) = fun2set (m,s.mdomain) ⇒
  wordSem$mem_load ad (s with memory := m) = mem_load ad s
Proof
  strip_tac>>gs[wordSemTheory.mem_load_def]>>
  IF_CASES_TAC>>gs[set_sepTheory.fun2set_eq]
QED

Theorem mem_store_const_memory[simp]:
  fun2set (s.memory,s.mdomain) = fun2set (m,s.mdomain) ⇒
  (mem_store ad w s = NONE ⇔ wordSem$mem_store ad w (s with memory := m) = NONE) ∧
  (mem_store ad w s = SOME (s with memory:= s.memory⦇ad↦w⦈) ⇔
     wordSem$mem_store ad w (s with memory := m) =
     SOME (s with memory := m⦇ad↦w⦈))
Proof
  strip_tac>>gs[wordSemTheory.mem_store_def]
QED

Theorem mem_load_32_const_memory[simp]:
  fun2set (m,dm) = fun2set (m',dm) ⇒
  wordSem$mem_load_32 m dm be ad = mem_load_32 m' dm be ad
Proof
  strip_tac>>gs[wordSemTheory.mem_load_32_alt]>>
  rpt (TOP_CASE_TAC>>gs[set_sepTheory.fun2set_eq])>>
  last_x_assum $ qspec_then ‘byte_align ad’ assume_tac>>gvs[]
QED

Theorem mem_store_32_const_memory:
  fun2set (m, dm) = fun2set (m', dm) ⇒
  (mem_store_32 m dm be ad hw = NONE ⇔ wordSem$mem_store_32 m' dm be ad hw = NONE) ∧
  (fun2set (THE (mem_store_32 m dm be ad hw), dm) =
    fun2set (THE (wordSem$mem_store_32 m' dm be ad hw), dm))
Proof
  strip_tac>>gs[wordSemTheory.mem_store_32_alt]>>
  rpt (TOP_CASE_TAC>>gs[set_sepTheory.fun2set_eq])>>
  rpt strip_tac>>
  simp[APPLY_UPDATE_THM]
QED

Theorem word_exp_const_memory[simp]:
  ∀s exp m.
  fun2set (s.memory,s.mdomain) = fun2set (m, s.mdomain) ⇒
  wordSem$word_exp (s with memory := m) exp = word_exp s exp
Proof
  recInduct wordSemTheory.word_exp_ind>>rw[wordSemTheory.word_exp_def]>>
  fs[PULL_FORALL]>>fs[Once SWAP_FORALL_THM]>>
  first_x_assum $ qspec_then ‘m’ assume_tac>>gs[]>>
  ‘the_words (MAP (λa. word_exp (s with memory := m) a) wexps) =
   the_words (MAP (λa. word_exp s a) wexps)’
    by (Induct_on ‘wexps’>>gs[]>>rpt strip_tac>>gs[]>>
        Cases_on ‘word_exp s h’>>gs[]>>
        gs[wordSemTheory.the_words_def])>>gs[]
QED

Theorem mem_load_byte_aux_const_memory[simp]:
  fun2set (m,dm) = fun2set (m',dm) ⇒
  wordSem$mem_load_byte_aux m' dm be w =
  mem_load_byte_aux m dm be w
Proof
  strip_tac>>gs[wordSemTheory.mem_load_byte_aux_def]>>
  gs[set_sepTheory.fun2set_eq]>>
  first_x_assum $ qspec_then ‘byte_align w’ assume_tac>>
  rpt (CASE_TAC>>gs[])
QED

Theorem mem_store_byte_aux_const_memory:
  fun2set (m,dm) = fun2set (m',dm) ⇒
  (mem_store_byte_aux m dm be w b = NONE ⇔
     mem_store_byte_aux m' dm be w b = NONE) ∧
  (fun2set (THE (wordSem$mem_store_byte_aux m' dm be w b),dm) =
   fun2set (THE (mem_store_byte_aux m dm be w b), dm))
Proof
  gs[set_sepTheory.fun2set_eq]>>rpt strip_tac>>
  gs[wordSemTheory.mem_store_byte_aux_def]
  >- (first_x_assum $ qspec_then ‘byte_align w’ assume_tac>>
      rpt (CASE_TAC>>gs[]))>>
  first_assum $ qspec_then ‘a’ assume_tac>>
  first_x_assum $ qspec_then ‘byte_align w’ assume_tac>>
  rpt (CASE_TAC>>gs[])>>gs[UPDATE_def]>>IF_CASES_TAC>>gs[]
QED

Theorem read_bytearray_const_memory[simp]:
  fun2set (m,dm) = fun2set (m',dm) ⇒
  misc$read_bytearray ptr len (mem_load_byte_aux m dm be) =
  read_bytearray ptr len (mem_load_byte_aux m' dm be)
Proof
  strip_tac>>
  imp_res_tac mem_load_byte_aux_const_memory>>
  metis_tac[]
QED

Theorem write_bytearray_const_memory[simp]:
  ∀ls ptr m.
  fun2set (m,dm) = fun2set (m',dm) ⇒
  fun2set (wordSem$write_bytearray ptr ls m dm be, dm) =
  fun2set (write_bytearray ptr ls m' dm be, dm)
Proof
  Induct>>gs[wordSemTheory.write_bytearray_def]>>
  rpt strip_tac>>gs[]>>
  first_x_assum $ qspecl_then [‘ptr+1w’, ‘m’] assume_tac>>rfs[]>>
  drule mem_store_byte_aux_const_memory>>strip_tac>>
  first_x_assum $ qspecl_then [‘ptr’, ‘be’, ‘h’] assume_tac>>fs[]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem inst_const_memory:
  fun2set (s.memory,s.mdomain) = fun2set (m, s.mdomain) ⇒
  (inst i s = NONE ⇔ wordSem$inst i (s with memory := m) = NONE) ∧
  (inst i s ≠ NONE ⇒
   (∃m'. THE (wordSem$inst i (s with memory := m)) =
         (THE (inst i s)) with memory := m' ∧
         (let x = THE (inst i s) in
            fun2set (x.memory,x.mdomain) = fun2set (m',x.mdomain))))
Proof
  (* a bit slow *)
  Induct_on ‘i’>>gs[wordSemTheory.inst_def]>>
  strip_tac
  >- metis_tac[]
  >- (ntac 2 strip_tac>>
      gs[wordSemTheory.assign_def, wordSemTheory.set_var_def]>>
      CASE_TAC>>gs[word_exp_const_memory]>>gvs[]>>metis_tac[])
  >- (rpt strip_tac>>
      gs[wordSemTheory.assign_def, wordSemTheory.set_var_def]>>
      rpt (CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>gs[])>>
      gs[]>>rpt (FULL_CASE_TAC>>gs[])>>gvs[]>>metis_tac[])
  >- (rpt strip_tac>>
      rpt (CASE_TAC>>gs[])>>
      imp_res_tac mem_load_byte_aux_const_memory>>gs[]>>
      imp_res_tac mem_store_byte_aux_const_memory>>gs[]>>
      imp_res_tac mem_store_32_const_memory>>gs[]>>
      imp_res_tac mem_load_32_const_memory>>gs[]>>
      imp_res_tac mem_store_const_memory>>gs[]>>
      imp_res_tac mem_load_const_memory>>gs[]>>
      ntac 2 $ first_x_assum $ qspecl_then [‘w2w c’, ‘s.be’, ‘c''’] assume_tac>>
      ntac 2 $ first_x_assum $ qspecl_then [‘c''’, ‘s.be’, ‘w2w c’] assume_tac>>
      gs[wordSemTheory.set_var_def]>>
      gs[wordSemTheory.mem_store_def]>>
      rpt (FULL_CASE_TAC>>gs[])>>gvs[]>>TRY (metis_tac[])>>
      irule_at Any fun2set_update_eq>>gs[]>>metis_tac[])>>
  rpt strip_tac>>
  gs[wordSemTheory.get_fp_var_def,
     wordSemTheory.set_fp_var_def,
     wordSemTheory.get_var_def,
     wordSemTheory.set_var_def]>>
  rpt (CASE_TAC>>gs[])>>gvs[]>>
  rpt (FULL_CASE_TAC>>gs[])>>gvs[]>>
  metis_tac[]
QED

Theorem const_writes_const_memory:
  ∀c' c words m m' md.
  fun2set (m,md) = fun2set (m',md) ⇒
  fun2set (wordSem$const_writes c' c words m,md) =
  fun2set (wordSem$const_writes c' c words m',md)
Proof
  Induct_on ‘words’>>srw_tac[][wordSemTheory.const_writes_def]>>
  rename1 ‘h::words’>>Cases_on ‘h’>>
  gs[wordSemTheory.const_writes_def]
QED

Theorem share_inst_const_memory[simp]:
  ∀s op v c m.
  fun2set (s.memory,s.mdomain) = fun2set (m, s.mdomain) ∧
  share_inst op v c s = (res, t) ⇒
  t.memory = s.memory ∧ t.mdomain = s.mdomain ∧
  share_inst op v c (s with memory := m) = (res, t with memory := m)
Proof
  rpt strip_tac>>Cases_on ‘op’>>
  gs[wordSemTheory.share_inst_def,
     wordSemTheory.sh_mem_load_def,
     wordSemTheory.sh_mem_load_byte_def,
     wordSemTheory.sh_mem_load16_def,
     wordSemTheory.sh_mem_load32_def,
     wordSemTheory.sh_mem_store_def,
     wordSemTheory.sh_mem_store_byte_def,
     wordSemTheory.sh_mem_store16_def,
     wordSemTheory.sh_mem_store32_def,
     ffiTheory.call_FFI_def]>>
  every_case_tac>>gvs[]>>
  fs[wordSemTheory.sh_mem_set_var_def,
     wordSemTheory.set_var_def,
     wordSemTheory.flush_state_def]>>gvs[]
QED

Theorem mem_upd_lemma:
  ((s : ('a, 'b, 'c) wordSem$state) with memory := ARB) = (t with memory := ARB) ==>
  ?m. s = (t with memory := m)
Proof
  simp [wordSemTheory.state_component_equality]
QED

Theorem push_env_mem_upd:
  ! env params s.
  push_env env params (s with memory := m) =
  (push_env env params s with memory := m)
Proof
  recInduct wordSemTheory.push_env_ind
  \\ simp [wordSemTheory.push_env_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs []
QED

Theorem push_env_mem_const:
  ! env params s.
  (push_env env params s).memory = s.memory /\
  (push_env env params s).mdomain = s.mdomain
Proof
  recInduct wordSemTheory.push_env_ind
  \\ simp [wordSemTheory.push_env_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs []
QED

Theorem cut_state_with_mem_const:
  cut_state x ((s:('a, 'b, 'c) wordSem$state) with memory := m) =
  OPTION_MAP (λs'. s' with memory := m) (cut_state x s)
Proof
  simp [wordSemTheory.cut_state_def]
  \\ Cases_on ‘cut_env x s.locals’ \\ simp []
QED

(* memory update lemma for evaluate *)
Theorem memory_swap_lemma1:
  ∀prog st res rst m.
  wordSem$evaluate (prog, (st:(α,β,γ) wordSem$state)) = (res, rst) ∧
  fun2set (st.memory, st.mdomain) = fun2set (m, st.mdomain) ∧
  no_alloc_code st.code ∧ no_install_code st.code ∧
  no_alloc prog ∧ no_install prog ⇒
  (∃st'. evaluate (prog, st with memory := m) = (res, st') /\
        (st' with memory := ARB) = (rst with memory := ARB) /\
        fun2set (rst.memory, rst.mdomain) = fun2set (st'.memory, rst.mdomain))
Proof
  recInduct (name_ind_cases [] wordSemTheory.evaluate_ind)
  \\ srw_tac [] [wordSemTheory.evaluate_def]
  \\ fs [wordSemTheory.call_env_def, wordConvsTheory.no_alloc_def,
    wordConvsTheory.no_install_def, wordSemTheory.flush_state_def,
    wordSemTheory.dec_clock_def]
  >~ [`Case (Inst i, _)`]
  >- (
    imp_res_tac inst_const_memory
    \\ fs [CaseEq "option"] \\ gvs []
    \\ rpt (first_x_assum (qspec_then `i` assume_tac))
    \\ gs [GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
  )
  >~ [`Case (MustTerminate _, _)`]
  >- (
    fs [UNCURRY_eq_pair, CaseEq "bool"] \\ gvs []
    \\ first_x_assum (qspec_then `m` assume_tac) \\ fs []
    \\ imp_res_tac mem_upd_lemma
    \\ gs []
  )
  >~ [`Case (Seq _ _, _)`]
  >- (
    gs [UNCURRY_eq_pair]
    \\ first_x_assum (qspec_then `m` assume_tac)
    \\ gs [CaseEq "bool"]
    \\ imp_res_tac mem_upd_lemma
    \\ fs []
    \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code
    \\ fs []
  )
  >~ [`Case (Raise _, rst)`]
  >- (
    fs [CaseEq "option"] \\ gvs []
    \\ fs [wordSemTheory.jump_exc_def, CaseEq "list"]
    \\ Cases_on `rst.handler < LENGTH rst.stack` \\ fs []
    \\ gvs []
    \\ every_case_tac \\ fs []
    \\ gvs []
  )
  >~ [`Case (FFI _ _ _ _ _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc"] \\ gvs []
    \\ imp_res_tac read_bytearray_const_memory
    \\ gs []
    \\ every_case_tac \\ gvs []
  )
  >~ [`Case (ShareInst _ _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc"] \\ gvs []
    \\ drule_all share_inst_const_memory
    \\ SIMP_TAC bool_ss []
    \\ simp []
  )
  >~ [`Case (Call _ _ _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc", CaseEq "bool"] \\ gvs []
    \\ fs [CaseEq "prod"] \\ gvs []
    \\ drule wordPropsTheory.no_alloc_find_code
    \\ drule_at (Pos (el 2)) wordPropsTheory.no_install_find_code
    \\ simp [] \\ rpt strip_tac
    \\ fs [CaseEq "option", CaseEq "bool", CaseEq "prod"] \\ gvs []
    \\ fs [CaseEq "wordSem$result"] \\ gvs []
    \\ fs [push_env_mem_upd, push_env_mem_const]
    \\ last_x_assum (qspec_then `m` assume_tac)
    \\ gs[wordSemTheory.pop_env_def, wordSemTheory.set_var_def,
          wordSemTheory.set_vars_def, alist_insert_def]
    \\ fs [AllCaseEqs ()] \\ gvs []
    \\ imp_res_tac mem_upd_lemma \\ gs []
    \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code
    \\ gvs [PULL_EXISTS,SF DNF_ss]
  )
  >~ [`Case (Loop _ _ _, _)`]
  >- suspend "Loop"
  \\ (
    fs [wordSemTheory.get_var_def, wordSemTheory.set_var_def,
        wordSemTheory.unset_var_def, CaseEq "option", CaseEq "word_loc", CaseEq "bool",
        get_vars_const_memory, UNCURRY_eq_pair]
    \\ gvs []
    \\ imp_res_tac  mem_upd_lemma
    \\ gs [wordSemTheory.set_vars_def, wordSemTheory.set_store_def,
        const_writes_const_memory, wordSemTheory.mem_store_def]
    \\ gvs []
    \\ NO_TAC
  )
QED

Resume memory_swap_lemma1[Loop]:
  Cases_on ‘cut_state (names,LN) s’ \\ gvs []
  >- (qexists_tac ‘rst with memory := m’
      \\ simp [cut_state_with_mem_const,
               wordSemTheory.state_component_equality])
  \\ Cases_on ‘wordSem$evaluate (c,x)’ \\ gvs []
  \\ subgoal ‘fun2set (x.memory,x.mdomain) = fun2set (m,x.mdomain) ∧
              no_alloc_code x.code ∧ no_install_code x.code’
  >- (imp_res_tac wordPropsTheory.cut_state_const \\ gvs [])
  \\ first_x_assum (qspec_then ‘m’ mp_tac) \\ fs []
  \\ disch_then (qx_choose_then ‘st_v’ strip_assume_tac)
  \\ qabbrev_tac ‘mem' = st_v.memory’
  \\ subgoal ‘st_v = r with memory := mem'’
  >- (qpat_x_assum ‘st_v with memory := ARB = _ with memory := ARB’ mp_tac
      \\ simp [Abbr ‘mem'’, wordSemTheory.state_component_equality])
  \\ pop_assum SUBST_ALL_TAC
  \\ simp [cut_state_with_mem_const]
  \\ Cases_on ‘cont_loop q’ \\ gvs []
  >- (
    Cases_on ‘r.clock = 0’ \\ gvs []
    >- (
      first_x_assum (qspec_then ‘mem'’ mp_tac)
      \\ impl_tac
      >- (subgoal ‘x.code = r.code’
          >- (qspecl_then [‘c’,‘x’,‘q’,‘r’]
                mp_tac wordPropsTheory.no_install_evaluate_const_code
              \\ simp [])
          \\ simp [wordSemTheory.STOP_def, stackSemTheory.STOP_def,
                   Once wordConvsTheory.no_alloc_def,
                   Once wordConvsTheory.no_install_def]
          \\ gvs [])
      \\ disch_then (qx_choose_then ‘st_loop’ strip_assume_tac)
      \\ qexists_tac ‘st_loop’
      \\ gvs []
    )
    \\ qexists_tac ‘r with <|locals := LN; locals_size := SOME 0;
                             store := FEMPTY; stack := []; memory := mem'|>’
    \\ simp [wordSemTheory.state_component_equality]
  )
  \\ Cases_on ‘q = SOME (Break 0)’ \\ gvs []
  >- (
    Cases_on ‘cut_state (exit_names,LN) r’ \\ gvs []
    >- (imp_res_tac wordPropsTheory.cut_state_const \\ gvs [])
    \\ qexists_tac ‘r with memory := mem'’
    \\ simp [wordSemTheory.state_component_equality]
  )
  \\ qexists_tac ‘r with memory := mem'’
  \\ simp [wordSemTheory.state_component_equality]
QED

Finalise memory_swap_lemma1;

(* avoid changing subsequent proof by rephrasing back into earlier form *)
Theorem memory_swap_lemma:
  ∀prog st res rst m.
  wordSem$evaluate (prog, (st:(α,β,γ) wordSem$state)) = (res, rst) ∧
  fun2set (st.memory, st.mdomain) = fun2set (m, st.mdomain) ∧
  no_alloc_code st.code ∧ no_install_code st.code ∧
  no_alloc prog ∧ no_install prog ⇒
  (∃m'. evaluate (prog, st with memory := m) = (res, rst with memory := m') ∧
        fun2set (rst.memory, rst.mdomain) = fun2set (m', rst.mdomain))
Proof
  rw []
  \\ drule_all memory_swap_lemma1
  \\ rw []
  \\ imp_res_tac  mem_upd_lemma
  \\ simp []
  \\ metis_tac []
QED

Theorem word_semantics_memory_update:
  fun2set (s.memory,s.mdomain) = fun2set (m,s.mdomain) ∧
  no_alloc_code s.code ∧ no_install_code s.code ⇒
  wordSem$semantics ((s with memory := m):(α,β,'ffi) wordSem$state) start ≠ Fail ⇒
  wordSem$semantics s start =
  wordSem$semantics ((s with memory := m):(α,β,'ffi) wordSem$state) start
Proof
  strip_tac>>
  gs[wordSemTheory.semantics_def]>>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  strip_tac>>
  strip_tac
  >- (strip_tac>>gs[]>>
      IF_CASES_TAC>>gs[]
      >- (Cases_on ‘r=SOME TimeOut’>>gs[]>>
          qmatch_asmsub_abbrev_tac ‘FST ev’>>
          Cases_on ‘ev’>>gs[]>>rename1 ‘(q,r')’>>
          drule memory_swap_lemma>>
          fs[wordConvsTheory.no_alloc_def,
             wordConvsTheory.no_install_def]>>
          qexists_tac ‘m’>>gs[]>>
          strip_tac>>strip_tac>>
          ‘q = r’
            by (Cases_on ‘k < k'’>>gs[]
                >- (qpat_x_assum ‘evaluate _ = (r, _)’ assume_tac>>
                    drule wordPropsTheory.evaluate_add_clock>>
                    strip_tac>>pop_assum $ qspec_then ‘k' - k’ assume_tac>>gs[])>>
                gs[NOT_LESS]>>
                drule wordPropsTheory.evaluate_add_clock>>
                strip_tac>>pop_assum $ qspec_then ‘k - k'’ assume_tac>>gs[]>>
                Cases_on ‘q’>>rename1 ‘SOME x'’>>Cases_on ‘x'’>>gs[])>>
          Cases_on ‘r’>>rename1 ‘SOME x'’>>Cases_on ‘x'’>>gs[]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>gs[])>>
      DEEP_INTRO_TAC some_intro >> simp[] >>
      strip_tac

      >- (strip_tac>>
          first_x_assum $ qspec_then ‘k’ assume_tac>>
          qmatch_asmsub_abbrev_tac ‘FST ev’>>
          Cases_on ‘ev’>>gs[]>>rename1 ‘(q,r')’>>
          drule memory_swap_lemma>>fs[]>>
          fs[wordConvsTheory.no_alloc_def,
             wordConvsTheory.no_install_def]>>
          disch_then $ qspec_then ‘m’ assume_tac>>gs[]>>
          strip_tac>>gs[]>>
          Cases_on ‘r'' = SOME TimeOut’>>gs[]>>
          Cases_on ‘q = SOME TimeOut’>>gs[]>>
          ‘q = r'' ∧ t'.ffi.io_events = r'.ffi.io_events’
            by (Cases_on ‘k < k'’>>gs[]
                >- (qpat_x_assum ‘evaluate _ = (q, _)’ assume_tac>>
                    drule wordPropsTheory.evaluate_add_clock>>
                    strip_tac>>pop_assum $ qspec_then ‘k' - k’ assume_tac>>gs[])>>
                gs[NOT_LESS]>>
                drule wordPropsTheory.evaluate_add_clock>>
                strip_tac>>pop_assum $ qspec_then ‘k - k'’ assume_tac>>gs[])>>gs[]>>
          Cases_on ‘r''’>>gs[]>>rename1 ‘SOME x''’>>Cases_on ‘x''’>>gs[])>>
      first_x_assum $ qspec_then ‘k’ assume_tac>>
      qmatch_asmsub_abbrev_tac ‘FST ev’>>
      Cases_on ‘ev’>>gs[]>>rename1 ‘(q,r')’>>
      qexists_tac ‘k’>>gs[]>>
      drule memory_swap_lemma>>fs[]>>
      fs[wordConvsTheory.no_alloc_def,
         wordConvsTheory.no_install_def]>>
      disch_then $ qspec_then ‘m’ assume_tac>>gs[]>>metis_tac[])>>
  IF_CASES_TAC>>gs[]
  >- (qmatch_asmsub_abbrev_tac ‘FST ev’>>
      Cases_on ‘ev’>>gs[]>>rename1 ‘(q,r)’>>
      drule memory_swap_lemma>>fs[]>>
      fs[wordConvsTheory.no_alloc_def,
         wordConvsTheory.no_install_def]>>
      qexists_tac ‘m’>>gs[]>>
      strip_tac>>
      strip_tac>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[])>>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  strip_tac>>strip_tac
  >- (strip_tac>>
      drule memory_swap_lemma>>fs[]>>
      fs[wordConvsTheory.no_alloc_def,
         wordConvsTheory.no_install_def]>>
      qexists_tac ‘m’>>gs[]>>
      strip_tac>>
      strip_tac>>gs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[])>>
  irule lprefix_lubTheory.IMP_build_lprefix_lub_EQ>>
  conj_tac
  >- (rw[lprefix_chain_def]>>
      Cases_on ‘k < k'’
      >- (irule OR_INTRO_THM1>>gs[LPREFIX_fromList]>>
          gs[from_toList]>>
          irule IS_PREFIX_TRANS>>
          irule_at Any wordPropsTheory.evaluate_add_clock_io_events_mono>>gs[]>>
          qexists_tac ‘k' - k’>>gs[])>>
      irule OR_INTRO_THM2>>gs[LPREFIX_fromList]>>
      gs[from_toList]>>
      irule IS_PREFIX_TRANS>>
      irule_at Any wordPropsTheory.evaluate_add_clock_io_events_mono>>gs[]>>
      qexists_tac ‘k - k'’>>gs[])>>
  conj_tac
  >- (rw[lprefix_chain_def]>>
      Cases_on ‘k < k'’
      >- (irule OR_INTRO_THM1>>gs[LPREFIX_fromList]>>
          gs[from_toList]>>
          irule IS_PREFIX_TRANS>>
          irule_at Any wordPropsTheory.evaluate_add_clock_io_events_mono>>gs[]>>
          qexists_tac ‘k' - k’>>gs[])>>
      irule OR_INTRO_THM2>>gs[LPREFIX_fromList]>>
      gs[from_toList]>>
      irule IS_PREFIX_TRANS>>
      irule_at Any wordPropsTheory.evaluate_add_clock_io_events_mono>>gs[]>>
      qexists_tac ‘k - k'’>>gs[])>>
  conj_tac
  >- (gs[lprefix_rel_def]>>strip_tac>>strip_tac>>gs[LPREFIX_fromList]>>
      irule_at Any EQ_REFL>>gs[from_toList]>>
      qmatch_goalsub_abbrev_tac ‘SND ev’>>
      Cases_on ‘ev’>>gs[]>>
      qexists_tac ‘k’>>gs[]>>
      drule memory_swap_lemma>>gs[]>>strip_tac>>
      fs[wordConvsTheory.no_alloc_def,
         wordConvsTheory.no_install_def]>>
      first_x_assum $ qspec_then ‘m’ assume_tac>>gs[])>>
  gs[lprefix_rel_def]>>strip_tac>>strip_tac>>gs[LPREFIX_fromList]>>
  irule_at Any EQ_REFL>>gs[from_toList]>>
  qexists_tac ‘k’>>gs[]>>
  qpat_abbrev_tac ‘ev = evaluate (Call _ _ _ _, s with clock := _)’>>
  Cases_on ‘ev’>>gs[]>>
  drule memory_swap_lemma>>gs[]>>strip_tac>>
  fs[wordConvsTheory.no_alloc_def,
     wordConvsTheory.no_install_def]>>
  first_x_assum $ qspec_then ‘m’ assume_tac>>gs[]
QED

(* accounting for the resources *)

val _ = if null (hyp (memory_swap_lemma1)) then () else raise Fail "hypotheses: memory_swap_lemma1";
val _ = (print "memory_swap_lemma1_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (memory_swap_lemma1)); print "\n");
val _ = if null (hyp (memory_swap_lemma)) then () else raise Fail "hypotheses: memory_swap_lemma";
val _ = (print "memory_swap_lemma_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (memory_swap_lemma)); print "\n");
val _ = if null (hyp (word_semantics_memory_update)) then () else raise Fail "hypotheses: word_semantics_memory_update";
val _ = (print "word_semantics_memory_update_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_semantics_memory_update)); print "\n");
