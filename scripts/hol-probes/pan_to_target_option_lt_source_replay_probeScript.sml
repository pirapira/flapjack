load "bossLib";
open bossLib HolKernel Parse;
val _ = new_theory "flapjack_option_lt_source_replay";
(* Literal standalone source definition, pan_to_targetProofScript1157-1160.
   This is a local source replay, not an exported original theory capture. *)
val option_lt_source_def = Define `
  (option_lt n0 NONE <=> T) /\ (option_lt NONE (SOME n1) <=> F) /\
  (option_lt (SOME n1) (SOME n2) <=> n1 < n2:num)`;
val _ = show_types := true;
fun emit label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = print "option_lt_local_replay_type="; val _ = print (type_to_string (type_of ``option_lt``)); val _ = print "\n";
val _ = emit "option_lt_local_replay_def_typed" option_lt_source_def;
fun print_eval label q = (print (label ^ "="); print_term (#2 (boolSyntax.dest_eq (concl (EVAL q)))); print "\n");
val _ = print_eval "none_none" ``option_lt NONE NONE``;
val _ = print_eval "some_none" ``option_lt (SOME 4) NONE``;
val _ = print_eval "none_some" ``option_lt NONE (SOME 4)``;
val _ = print_eval "less" ``option_lt (SOME 3) (SOME 4)``;
val _ = print_eval "equal" ``option_lt (SOME 4) (SOME 4)``;
val _ = print_eval "greater" ``option_lt (SOME 5) (SOME 4)``;
