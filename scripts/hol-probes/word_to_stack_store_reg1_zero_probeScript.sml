load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = (if null (hyp th) then () else raise Fail "open premise"; print (label ^ "="); print_thm th; print "\n");
val evaluate_wStackStore_wReg1 = GEN_ALL(prove(``  wReg1 r (k,f,f') = (x,r') ∧
  EVEN r ∧
  r < 2 * f' + 2 * k ∧
  state_rel ac k f f' (s:('a,num # 'c,'ffi) wordSem$state) (t:('a,'c,'ffi) stackSem$state) lens 0 ∧
  LENGTH t.stack = LENGTH_t_stack ∧
  t.stack_space = t_stack_space
  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackStore x Skip,(set_var r' c t)) = (NONE,t') ∧
  state_rel ac k f f' (set_var r c s) t' lens 0 ∧
  LENGTH t'.stack = LENGTH_t_stack /\ t'.stack_space = t_stack_space``,
  rw[wReg1_def,LET_THM,EVEN_EXISTS]>>
  fs[wStackStore_def,stackSemTheory.evaluate_def,LET_THM,stackSemTheory.get_var_def]>>simp[]>-
   (irule state_rel_set_var >> fs[]) >>
  IF_CASES_TAC >- fs[state_rel_def] >>
  IF_CASES_TAC >- (fs[state_rel_def] >>
     Cases_on `f' = 0` >> fs[])>>
  fs[Once stackSemTheory.set_var_def,FLOOKUP_UPDATE] >>
  irule state_rel_set_var2 >> fs[]));

val zero_store = GEN_ALL(prove(``  wReg1 r (k,f,f') = (x,r') ∧
  EVEN r ∧
  r < 2 * f' + 2 * k ∧
  state_rel ac k f f' (s:('a,num # 'c,'ffi) wordSem$state) (t:('a,'c,'ffi) stackSem$state) lens 0 ∧
  LENGTH t.stack = LENGTH_t_stack ∧
  t.stack_space = t_stack_space
  ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackStore x Skip,(set_var 0 c1 (set_var r' c t))) = (NONE,t') ∧
  state_rel ac k f f' (set_var 0 c1 (set_var r c s)) t' lens 0 ∧
  LENGTH t'.stack = LENGTH_t_stack /\ t'.stack_space = t_stack_space``,
  rw[] >>  Cases_on `r = 0`
  >-(`r' = 0` by gvs[wReg1_def,AllCaseEqs()] >>
    simp[set_var_cancel,set_var_cancel_word] >>
    match_mp_tac  evaluate_wStackStore_wReg1 >> gvs[])
  >-(
   `~(r' = 0)` by
        (gvs[wReg1_def,AllCaseEqs(),EVEN_EXISTS] >>
        fs[state_rel_def]) >>
    simp[Once set_var_swap,Once set_var_swap_word] >>
    match_mp_tac evaluate_wStackStore_wReg1 >> simp[] >>
    match_mp_tac state_rel_set_var' >> simp[] >>
    fs[state_rel_def])));
val _ = if null(hyp zero_store) andalso null(free_vars(concl zero_store)) then () else raise Fail "open zero store theorem";
val _ = (print "storeReg1Zero_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl zero_store));
val _ = print("storeReg1Zero_proved=" ^ term_to_string(rhs(concl(EQT_INTRO zero_store))) ^ "\n");
val _ = print("storeReg1Zero_hypotheses=" ^ Int.toString(length(hyp zero_store)) ^ "\n");
