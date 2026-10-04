load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val evaluate_wStackLoad_wReg1 = GEN_ALL(prove(``
  wReg1 r (k,f,f') = (x ,r') ∧
  EVEN r ∧
  get_var r (s:('a,num # 'c,'ffi)state) = SOME c ∧
  state_rel ac k f f' s t lens 0 ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip,t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  state_rel ac k f f' s t' lens 0 ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space /\
  t'.bitmaps = t.bitmaps /\
   (∀r. r ≠ k ⇒ get_var r t' = get_var r t) ∧
  r' ≠ k+1 ∧
  get_var r' t' = SOME c``,
  rw[wReg1_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackLoad_def,stackSemTheory.evaluate_def,LET_THM,stackSemTheory.get_var_def]>>simp[]
    >-
    (drule_all state_rel_get_var_imp>>simp[]) >>
  IF_CASES_TAC>-fs[state_rel_def]>>
  reverse IF_CASES_TAC>-
    (fs[state_rel_def,LET_THM,get_var_def]>>
    res_tac>>fs[TWOxDIV2]>>rfs[]>>
    Cases_on`f'`>>fs[])>>
  imp_res_tac state_rel_get_var_imp2>>
  fs[]>>
  simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE]>>
  fs[TWOxDIV2]));
val evaluate_wStackLoad_wReg1_with_const = GEN_ALL(prove(``
  wReg1 r (k,f,f') = (x ,r') ∧
  EVEN r ∧
  word_exp (s:('a,num # 'c,'ffi)state) (Op Add [Var r;Const c]) = SOME (
Word w) ∧
  state_rel ac k f f' s t lens 0 ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip,t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  state_rel ac k f f' s t' lens 0 ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space /\
  r' ≠ k+1 ∧
  (stackSem$word_exp t' (Op Add [Var r';Const c])) = SOME (w)``,
  rw[] >>
  gvs[wordSemTheory.word_exp_def,wordSemTheory.the_words_def,AllCaseEqs()] >>
  drule_all evaluate_wStackLoad_wReg1 >>
  strip_tac >> fs[] >>
  fs[stackSemTheory.word_exp_def] >>
  (* TODO remove this line by changing word_exp_def*)
  fs[GSYM stackSemTheory.get_var_def]));
val result = evaluate_wStackLoad_wReg1_with_const;
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open offset load";
val _ = (print "loadReg1Offset_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl result));
val _ = print("loadReg1Offset_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("loadReg1Offset_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");
