load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory
 word_to_stackTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
val result = GEN_ALL(prove(``
   evaluate (wMoveAux [] kf,s) = (NONE,s) ∧
   evaluate (wMoveAux (x::xs) kf,s) =
   evaluate (Seq (wMoveSingle x kf) (wMoveAux xs kf), s)``,

  rw[wMoveAux_def] >- rw[stackSemTheory.evaluate_def]
  \\ Cases_on`xs` >> rw[wMoveAux_def]
  \\ rw[stackSemTheory.evaluate_def]
  \\ pairarg_tac
  \\ rw[]));
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open moveaux";
val _ = (print "wMoveAux_statement="; print_term(concl result); print "\n");
val _ = print("wMoveAux_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("wMoveAux_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");

(* Full typed original terms for source/carrier review; original replay is unchanged. *)
val _ = (print "wMoveAux_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl result); print "\n");
