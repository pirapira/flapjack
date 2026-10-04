load "bossLib"; load "preamble"; load "loop_to_wordProofTheory";
open bossLib HolKernel Parse preamble loop_to_wordProofTheory;
val _ = show_types := true;
fun emit label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = print "state_rel_type=";
val _ = print (type_to_string (type_of ``loop_to_wordProof$state_rel``));
val _ = print "\n";
val _ = emit "state_rel_def_typed" (DB.fetch "loop_to_wordProof" "state_rel_def");
val _ = emit "state_rel_intro_typed" (DB.fetch "loop_to_wordProof" "state_rel_intro");
(* Source state_rel_IMP is local: replay its literal source proof at the
   full independently typed source/target carriers, not a fabricated DB export. *)
val clock_replay = prove
  (``!(s:('a,'b)loopSem$state) (t:('a,'c,'b)wordSem$state).
      loop_to_wordProof$state_rel s t ==> t.clock = s.clock``,
   fs [loop_to_wordProofTheory.state_rel_def] >> metis_tac []);
val _ = emit "state_rel_IMP_typed_replay" clock_replay;
val _ = emit "state_rel_with_clock_typed" (DB.fetch "loop_to_wordProof" "state_rel_with_clock");
