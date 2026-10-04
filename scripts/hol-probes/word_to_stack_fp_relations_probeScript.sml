load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val state_rel_get_fp_var = GEN_ALL(prove(``
   state_rel ac k f f' s t lens extra ⇒
  get_fp_var n s = get_fp_var n t``,
  fs[state_rel_def,get_fp_var_def,stackSemTheory.get_fp_var_def]));
val result = state_rel_get_fp_var;
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open FP relation";
val _ = (print "fpRelationRead_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl result));
val _ = print("fpRelationRead_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("fpRelationRead_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");
val state_rel_set_fp_var = GEN_ALL(prove(``
  state_rel ac k f f' s t lens extra ⇒
  state_rel ac k f f' (set_fp_var n v s) (set_fp_var n v t) lens extra``,
  fs[state_rel_def,set_fp_var_def,stackSemTheory.set_fp_var_def]>>rw[]>>
  metis_tac[]));
val result = state_rel_set_fp_var;
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open FP relation";
val _ = (print "fpRelationUpdate_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl result));
val _ = print("fpRelationUpdate_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("fpRelationUpdate_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");
