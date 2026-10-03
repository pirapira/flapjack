load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
open preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory
  wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["fromAList_def", "domain_union", "domain_insert",
  "domain_inter", "domain_map", "domain_difference", "sptree.map_def",
  "sptree.lookup_rwts", "sptree.insert_notEmpty", "misc.max3_def"];
val _ = numLib.temp_prefer_num();
val result = GEN_ALL(prove(``
   ∀ms s t r.
   state_rel ac k f f' s t lens 0 ∧
   (∀i v. r (SOME i) = SOME v ⇔ get_var (2*i) s = SOME v) ∧
   (∀v. r NONE = SOME v ⇒ get_var (k+1) t = SOME v) ∧
   IS_SOME (get_vars (MAP ($* 2 o THE) (FILTER IS_SOME (MAP SND ms))) s) ∧
   (case find_index NONE (MAP SND ms) 0 of
    | NONE => T
    | SOME i =>
      case find_index NONE (MAP FST ms) 0 of
      | NONE => IS_SOME (r NONE)
      | SOME j => i ≤ j ⇒ IS_SOME (r NONE)) ∧
   EVERY (λ(x,y). ∀a. (x = SOME a ∨ y = SOME a) ⇒ a < f' + k) ms ∧
   ALL_DISTINCT (FILTER IS_SOME (MAP FST ms))
   ⇒
   ∃t'.
     evaluate (wMoveAux (MAP (format_var k ## format_var k) ms) (k,f,f'),t) = (NONE,t') ∧
     state_rel ac k f f'
       (set_vars
         (MAP ($* 2 o THE) (FILTER IS_SOME (MAP FST (REVERSE ms))))
         (MAP THE (MAP (seqsem ms r) (FILTER IS_SOME (MAP FST (REVERSE ms)))))
         s) t' lens 0 /\
     LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space``,
  Induct
  \\ simp[wMoveAux_thm]
  >- simp[set_vars_def,alist_insert_def]
  \\ qx_gen_tac`h`
  \\ rpt gen_tac
  \\ Cases_on`h`
  \\ strip_tac
  \\ simp[]
  \\ simp[stackSemTheory.evaluate_def]
  \\ old_drule (GEN_ALL wMoveSingle_thm)
  \\ simp[]
  \\ qpat_abbrev_tac`wms = wMoveSingle _`
  \\ qmatch_assum_abbrev_tac`_ (y,x)`
  \\ disch_then(qspecl_then[`y`,`x`]mp_tac)
  \\ unabbrev_all_tac
  \\ fs[]
  \\ qho_match_abbrev_tac`(∀v. P v ⇒ Q v) ⇒ _`
  \\ `∃v. P v`
  by (
    simp[Abbr`P`,Abbr`Q`]
    \\ simp[LEFT_EXISTS_AND_THM]
    \\ conj_tac
    >- (
      TOP_CASE_TAC \\ fs[]
      >- (
        `IS_SOME (r NONE)` suffices_by metis_tac[IS_SOME_EXISTS]
        \\ fs[find_index_def]
        \\ FULL_CASE_TAC \\ fs[]
        \\ FULL_CASE_TAC \\ fs[])
      \\ fs[get_vars_def]
      \\ pop_assum mp_tac
      \\ TOP_CASE_TAC \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[] )
  \\ simp[Abbr`P`,Abbr`Q`] \\ fs[]
  \\ disch_then drule
  \\ strip_tac
  \\ simp[]
  \\ simp[parmoveTheory.seqsem_def]
  \\ first_x_assum drule
  \\ qpat_abbrev_tac`rr = (_ =+ r _) _`
  \\ disch_then(qspec_then`rr`mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`rr`,APPLY_UPDATE_THM]
    \\ conj_tac
    >- (
      rw[]
      >- (
        EVAL_TAC
        \\ simp[lookup_insert]
        \\ fs[]
        \\ FULL_CASE_TAC \\ fs[]
        \\ rw[EQ_IMP_THM]
        \\ fs[find_index_def]
        \\ FULL_CASE_TAC \\ fs[IS_SOME_EXISTS])
      \\ FULL_CASE_TAC \\ fs[]
      \\ EVAL_TAC
      \\ simp[lookup_insert]
      \\ fs[get_var_def] )
    \\ conj_tac
    >- (
      rw[] \\ fs[] \\ rw[]
      \\ FULL_CASE_TAC \\ fs[]
      \\ res_tac
      \\ fs[] )
    \\ conj_tac
    >- (
      qpat_x_assum`IS_SOME _`mp_tac
      \\ reverse IF_CASES_TAC \\ fs[get_vars_def]
      >- (
        CASE_TAC \\ simp[]
        \\ metis_tac[IS_SOME_get_vars_set_var] )
      \\ TOP_CASE_TAC \\ simp[]
      \\ TOP_CASE_TAC \\ simp[]
      \\ TOP_CASE_TAC \\ simp[]
      \\ metis_tac[IS_SOME_get_vars_set_var,IS_SOME_EXISTS])
    \\ reverse conj_tac
    >- (
      qhdtm_x_assum`ALL_DISTINCT`mp_tac
      \\ IF_CASES_TAC \\ simp[] )
    \\ TOP_CASE_TAC \\ simp[]
    \\ qpat_x_assum`option_CASE (find_index _ _ _) _ _`mp_tac
    \\ simp[find_index_def]
    \\ IF_CASES_TAC \\ fs[]
    \\ IF_CASES_TAC \\ rw[]
    >- (TOP_CASE_TAC \\ fs[])
    >- (
      pop_assum mp_tac
      \\ simp[Once find_index_shift_0]
      \\ strip_tac
      \\ TOP_CASE_TAC \\ fs[] )
    >- (
      fs[]
      \\ qmatch_assum_rename_tac`ss ≠ NONE`
      \\ Cases_on`r ss`
      \\ Cases_on`ss`\\ fs[]
      \\ CASE_TAC \\ fs[]
      \\ res_tac \\ fs[])
    >- (
      pop_assum mp_tac
      \\ simp[Once find_index_shift_0]
      \\ simp[Once find_index_shift_0]
      \\ strip_tac
      \\ TOP_CASE_TAC \\ fs[] ))
  \\ strip_tac
  \\ simp[]
  \\ qhdtm_x_assum `state_rel` mp_tac
  \\ qmatch_abbrev_tac`a ⇒ b`
  \\ `a = b` suffices_by rw[]
  \\ unabbrev_all_tac
  \\ rpt(AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ simp[set_vars_def]
  \\ simp[state_component_equality,set_var_def]
  \\ CASE_TAC \\ simp[] \\ fs[FILTER_APPEND]
  \\ simp[alist_insert_append]
  \\ simp[alist_insert_def]
  \\ rpt(AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ qpat_abbrev_tac`rr = _ r`
  \\ qispl_then[`SOME x`,`ms`,`rr`]mp_tac (Q.GEN`k`seqsem_move_unchanged)
  \\ impl_tac >- ( fs[MEM_FILTER] )
  \\ simp[] \\ disch_then kall_tac
  \\ simp[Abbr`rr`,APPLY_UPDATE_THM]
  \\ fs[find_index_def]
  \\ FULL_CASE_TAC \\ fs[]
  >- (
    FULL_CASE_TAC \\ fs[IS_SOME_EXISTS]
    \\ FULL_CASE_TAC \\ fs[] )
  \\ qmatch_rename_tac`v = THE (r z)`
  \\ Cases_on`z` \\ fs[]
  \\ res_tac \\ fs[]));
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open moveaux simulation";
val _ = (print "moveAuxSeqsem_statement="; print_term(concl result); print "\n");
val _ = print("moveAuxSeqsem_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("moveAuxSeqsem_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");

(* Full typed original terms for source/carrier review; original replay is unchanged. *)
val _ = (print "moveAuxSeqsem_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl result); print "\n");
