load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val arith_result = GEN_ALL (Q.SPEC `(asm$Arith operation : 'a asm$inst)` word_to_stackProofTheory.evaluate_wInst);
val _ = if null(hyp arith_result) andalso null(free_vars(concl arith_result)) then () else raise Fail "open Arith case";
val _ = (print "arith_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl arith_result));
val _ = print("arith_proved=" ^ term_to_string(rhs(concl(EQT_INTRO arith_result))) ^ "\n");
val _ = print("arith_hypotheses=" ^ Int.toString(length(hyp arith_result)) ^ "\n");
