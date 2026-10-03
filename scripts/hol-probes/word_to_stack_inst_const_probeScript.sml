load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val result = GEN_ALL (Q.SPEC `(asm$Const const_register (const_word : 'a word))` word_to_stackProofTheory.evaluate_wInst);
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open instruction Const case";
val _ = (print "evaluateWInstConst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl result));
val _ = print("evaluateWInstConst_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("evaluateWInstConst_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");
