(* Fresh closed original stored theorem/type capture; not a local proof replay
   or a cross-language equivalence proof. The full original theorem is retained. *)
load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val whole = GEN_ALL word_to_stackProofTheory.comp_correct;
val _ = if null(hyp whole) andalso null(free_vars(concl whole)) then ()
  else raise Fail "open original comp_correct";
val _ = (print "comp_correct_full_statement="; print_term(concl whole); print "\n");
val _ = print("comp_correct_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO whole))) ^ "\n");
val _ = print("comp_correct_full_hypotheses=" ^ Int.toString(length(hyp whole)) ^ "\n");
val _ = (Globals.show_types := true; print "comp_correct_full_statement_typed=";
  print_term(concl whole); print "\n"; Globals.show_types := false);
