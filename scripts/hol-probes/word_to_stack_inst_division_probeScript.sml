load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val result = GEN_ALL (Q.SPEC `(asm$Arith (asm$Div div_destination div_numerator div_denominator) : 'a asm$inst)` word_to_stackProofTheory.evaluate_wInst);
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open division case";
val _ = (print "division_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl result));
val _ = print("division_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("division_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");
