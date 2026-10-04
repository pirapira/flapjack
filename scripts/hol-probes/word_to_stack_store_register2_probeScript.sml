load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val evaluate_wStackStore_wReg2_new = GEN_ALL(prove(``
  wReg2 r (k,f,f') = (x,r') ∧
  EVEN r ∧
  r < 2 * f' + 2 * k ∧
  (?t'.
  evaluate (kont,t) = (NONE,set_var r' c t') /\
  state_rel ac k f f' s t' lens 0 /\
  LENGTH t'.stack = LENGTH_t_stack ∧ t'.stack_space = t_stack_space)
  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(Seq kont (wStackStore x Skip),t) = (NONE,t') ∧
  state_rel ac k f f' (set_var r c s) t' lens 0 ∧
  LENGTH t'.stack = LENGTH_t_stack /\ t'.stack_space = t_stack_space``,
  rw[wReg2_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackStore_def,stackSemTheory.evaluate_def,LET_THM]>>simp[]>-
  (irule state_rel_set_var >> fs[]) >>
  IF_CASES_TAC >- fs[state_rel_def] >>
  IF_CASES_TAC >- (fs[state_rel_def] >>
     Cases_on `f' = 0` >> fs[])>>
  fs[Once stackSemTheory.set_var_def,FLOOKUP_UPDATE] >>
  qmatch_asmsub_abbrev_tac `evaluate _ = (NONE,t'')` >>
  full_simp_tac(bool_ss)[GSYM stackSemTheory.state_fupdcanon] >>
  irule state_rel_set_var2 >> fs[Abbr `t''`,GSYM stackSemTheory.set_var_def]));
val result = evaluate_wStackStore_wReg2_new;
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open second-register law";
val _ = (print "storeReg2Continuation_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl result));
val _ = print("storeReg2Continuation_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("storeReg2Continuation_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");
val evaluate_wRegWrite2_seq = GEN_ALL(prove(``
  evaluate (wRegWrite2 g r (k,f,f'),t) =
  (let (l,n) = wReg2 r (k,f,f') in
  evaluate ((Seq (g n) (wStackStore l Skip)),t))``,
  rw[] >> pairarg_tac >> fs[] >>
  simp[stackSemTheory.evaluate_def,wRegWrite2_def] >>
  IF_CASES_TAC >> gvs[wStackStore_def,wReg2_def]
  >-(pairarg_tac >> simp[] >>
    IF_CASES_TAC >> simp[stackSemTheory.evaluate_def])
  >-(
   pairarg_tac >> simp[] >>
   simp[el 10 $ CONJUNCTS stackSemTheory.evaluate_def] >>
   simp[el 1 $ CONJUNCTS stackSemTheory.evaluate_def])));
val result = evaluate_wRegWrite2_seq;
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open second-register law";
val _ = (print "writeReg2Sequence_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl result));
val _ = print("writeReg2Sequence_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("writeReg2Sequence_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");
