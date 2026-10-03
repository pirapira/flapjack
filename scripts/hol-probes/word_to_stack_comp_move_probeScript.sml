load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory wordLangTheory;
val _ = Globals.linewidth := 1000000;
val result = GEN_ALL (Q.SPECL [`(wordLang$Move move_priority move_pairs : 'a wordLang$prog)`, `s`] word_to_stackProofTheory.comp_correct);
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open Move case";
val _ = (print "compCorrectMove_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl result));
val _ = print("compCorrectMove_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("compCorrectMove_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");
