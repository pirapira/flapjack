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
   state_rel ac k f f' s t lens 0 ∧
   (case x of NONE => get_var (k+1) t = SOME v
    | SOME x => get_var (x * 2) s = SOME v ) ∧
   (case y of SOME x => x < f' + k | _ => T)
   ⇒
   ∃t'.
     evaluate (wMoveSingle (format_var k y,format_var k x) (k,f,f'), t) = (NONE,t') ∧
     state_rel ac k f f' (case y of NONE => s | SOME y => set_var (y*2) v s) t' lens 0 ∧
     (y = NONE ⇒ get_var (k+1) t' = SOME v) ∧
     (y ≠ NONE ⇒ get_var (k+1) t' = get_var (k+1) t) /\
     LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space``,

  rw[wMoveSingle_def]
  \\ Cases_on`y` \\ simp[format_var_def]
  \\ Cases_on`x` \\ fs[format_var_def]
  >- (
    rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    \\ fs[stackSemTheory.get_var_def]
    \\ fs[stackSemTheory.set_var_def,FLOOKUP_UPDATE])
  >- (
    rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    >- (
      imp_res_tac state_rel_get_var_imp
      \\ simp[] )
    \\ IF_CASES_TAC >- fs[state_rel_def]
    \\ IF_CASES_TAC
    THEN1 (simp[]\\ imp_res_tac state_rel_get_var_imp2)
    \\
      fs[state_rel_def,LET_THM,get_var_def,TWOxDIV2]>>
      res_tac>>
      `x'*2 DIV 2 = x'` by metis_tac[TWOxDIV2,MULT_COMM]>>
      fs[]>>
      rfs[]>>
      Cases_on`f'`>>fs[])
  >- (
    rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    >- (
      fs[stackSemTheory.get_var_def]
      \\ conj_tac
      >- (match_mp_tac state_rel_set_var
          \\ simp[] )
      \\ simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE] )
    \\ IF_CASES_TAC >- fs[state_rel_def]
    \\ IF_CASES_TAC >-
      (fs[state_rel_def,LET_THM]>>
      Cases_on`f'`>>fs[]>>
      `F` by DECIDE_TAC)
    \\ simp[]
    \\ conj_tac
    >- (
      match_mp_tac state_rel_set_var2
      \\ simp[])
    \\ fs[stackSemTheory.get_var_def])
  >- (
    rw[stackSemTheory.evaluate_def,stackSemTheory.inst_def]
    \\ TRY (
      imp_res_tac state_rel_get_var_imp \\ fs[]
      \\ conj_tac >- (
           match_mp_tac state_rel_set_var
          \\ simp[])
      \\ fs[stackSemTheory.get_var_def,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
      \\ rw[]
      \\ `F` by decide_tac)
    \\ (IF_CASES_TAC >- fs[state_rel_def])
    \\ IF_CASES_TAC
    \\
    TRY(
      fs[state_rel_def,LET_THM,get_var_def]>>
      res_tac>>
      `x''*2 DIV 2 = x''` by metis_tac[MULT_COMM,TWOxDIV2]>>
      fs[]>>rfs[]>>
      Cases_on`f'`>>fs[]>>
      `F` by DECIDE_TAC>>NO_TAC)
    \\ fs[]
    >- (
      imp_res_tac state_rel_get_var_imp2
      \\ reverse conj_tac
      >- (
        EVAL_TAC \\ rw[]
        \\ `F` by decide_tac )
      \\ rw[]
      \\ simp[]
      \\ match_mp_tac state_rel_set_var \\ simp[])
    >- (
      imp_res_tac state_rel_get_var_imp
      \\ fs[stackSemTheory.get_var_def]
      \\ simp[]
      \\ match_mp_tac state_rel_set_var2
      \\ simp[] )
    >- (
      IF_CASES_TAC
      >- (
        `F` suffices_by rw[]
        \\ fs[state_rel_def,LET_THM,wordSemTheory.get_var_def]
        \\ every_case_tac >> fs[]
        \\ rveq \\ fs[]
        \\ decide_tac )
      \\ rpt(qpat_x_assum`¬(_ < k)`mp_tac)
      \\ simp_tac (srw_ss()++ARITH_ss)[]
      \\ ntac 2 strip_tac
      \\ imp_res_tac state_rel_get_var_imp2
      \\ rveq
      \\ reverse conj_tac
      >- (
        EVAL_TAC \\ rw[]
        \\ `F` by decide_tac )
      \\ match_mp_tac state_rel_set_var2
      \\ simp[]))));
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open single move";
val _ = (print "wMoveSingle_statement="; print_term(concl result); print "\n");
val _ = print("wMoveSingle_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("wMoveSingle_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");

(* Full typed original terms for source/carrier review; original replay is unchanged. *)
val _ = (print "wMoveSingle_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl result); print "\n");
