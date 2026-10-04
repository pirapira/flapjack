load "preamble"; load "wordSemTheory"; load "set_sepTheory"; load "miscTheory"; load "wordPropsTheory"; load "wordConvsProofTheory"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble wordSemTheory;
val _ = new_theory "flapjack_pan_to_target_const_memory_replay";
val _ = Globals.linewidth := 1000000;
(* Literal source replay of pan_to_targetProofScript 336-605 (pan_to_targetProofTheory is not built here). *)
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

val _ = if null (hyp (fun2set_update_eq)) then () else raise Fail "hypotheses: fun2set_update_eq";
val _ = (print "fun2set_update_eq_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (fun2set_update_eq)); print "\n");
val _ = if null (hyp (get_var_const_memory)) then () else raise Fail "hypotheses: get_var_const_memory";
val _ = (print "get_var_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (get_var_const_memory)); print "\n");
val _ = if null (hyp (set_var_const_memory)) then () else raise Fail "hypotheses: set_var_const_memory";
val _ = (print "set_var_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (set_var_const_memory)); print "\n");
val _ = if null (hyp (unset_var_const_memory)) then () else raise Fail "hypotheses: unset_var_const_memory";
val _ = (print "unset_var_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (unset_var_const_memory)); print "\n");
val _ = if null (hyp (get_vars_const_memory)) then () else raise Fail "hypotheses: get_vars_const_memory";
val _ = (print "get_vars_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (get_vars_const_memory)); print "\n");
val _ = if null (hyp (set_vars_const_memory)) then () else raise Fail "hypotheses: set_vars_const_memory";
val _ = (print "set_vars_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (set_vars_const_memory)); print "\n");
val _ = if null (hyp (get_var_imm_const_memory)) then () else raise Fail "hypotheses: get_var_imm_const_memory";
val _ = (print "get_var_imm_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (get_var_imm_const_memory)); print "\n");
val _ = if null (hyp (mem_load_const_memory)) then () else raise Fail "hypotheses: mem_load_const_memory";
val _ = (print "mem_load_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (mem_load_const_memory)); print "\n");
val _ = if null (hyp (mem_store_const_memory)) then () else raise Fail "hypotheses: mem_store_const_memory";
val _ = (print "mem_store_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (mem_store_const_memory)); print "\n");
val _ = if null (hyp (mem_load_32_const_memory)) then () else raise Fail "hypotheses: mem_load_32_const_memory";
val _ = (print "mem_load_32_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (mem_load_32_const_memory)); print "\n");
val _ = if null (hyp (mem_store_32_const_memory)) then () else raise Fail "hypotheses: mem_store_32_const_memory";
val _ = (print "mem_store_32_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (mem_store_32_const_memory)); print "\n");
val _ = if null (hyp (word_exp_const_memory)) then () else raise Fail "hypotheses: word_exp_const_memory";
val _ = (print "word_exp_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_exp_const_memory)); print "\n");
val _ = if null (hyp (mem_load_byte_aux_const_memory)) then () else raise Fail "hypotheses: mem_load_byte_aux_const_memory";
val _ = (print "mem_load_byte_aux_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (mem_load_byte_aux_const_memory)); print "\n");
val _ = if null (hyp (mem_store_byte_aux_const_memory)) then () else raise Fail "hypotheses: mem_store_byte_aux_const_memory";
val _ = (print "mem_store_byte_aux_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (mem_store_byte_aux_const_memory)); print "\n");
val _ = if null (hyp (read_bytearray_const_memory)) then () else raise Fail "hypotheses: read_bytearray_const_memory";
val _ = (print "read_bytearray_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (read_bytearray_const_memory)); print "\n");
val _ = if null (hyp (write_bytearray_const_memory)) then () else raise Fail "hypotheses: write_bytearray_const_memory";
val _ = (print "write_bytearray_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (write_bytearray_const_memory)); print "\n");
val _ = if null (hyp (inst_const_memory)) then () else raise Fail "hypotheses: inst_const_memory";
val _ = (print "inst_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (inst_const_memory)); print "\n");
val _ = if null (hyp (const_writes_const_memory)) then () else raise Fail "hypotheses: const_writes_const_memory";
val _ = (print "const_writes_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (const_writes_const_memory)); print "\n");
val _ = if null (hyp (share_inst_const_memory)) then () else raise Fail "hypotheses: share_inst_const_memory";
val _ = (print "share_inst_const_memory_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (share_inst_const_memory)); print "\n");
val _ = if null (hyp (mem_upd_lemma)) then () else raise Fail "hypotheses: mem_upd_lemma";
val _ = (print "mem_upd_lemma_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (mem_upd_lemma)); print "\n");
val _ = if null (hyp (push_env_mem_upd)) then () else raise Fail "hypotheses: push_env_mem_upd";
val _ = (print "push_env_mem_upd_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (push_env_mem_upd)); print "\n");
val _ = if null (hyp (push_env_mem_const)) then () else raise Fail "hypotheses: push_env_mem_const";
val _ = (print "push_env_mem_const_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (push_env_mem_const)); print "\n");
val _ = if null (hyp (cut_state_with_mem_const)) then () else raise Fail "hypotheses: cut_state_with_mem_const";
val _ = (print "cut_state_with_mem_const_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (cut_state_with_mem_const)); print "\n");
