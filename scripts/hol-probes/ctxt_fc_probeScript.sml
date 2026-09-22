(* Direct HOL-EVAL probes for pan_to_crepProof$ctxt_fc. *)
load "bossLib";
load "preamble";
load "pan_to_crepProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "shaped_slots"
  ``pan_to_crepProof$ctxt_fc
      (FEMPTY |+ («f», ([], One)))
      (FEMPTY |+ («E», (3w : 8 word)))
      [«x»; «pair»] [One; Comb [One; One]] [0; 1; 2]``;
val _ = print_eval "zip_truncates_and_empty_slots"
  ``pan_to_crepProof$ctxt_fc FEMPTY FEMPTY [«x»; «ignored»] [One] []``;
val _ = print_eval "empty_maximum"
  ``pan_to_crepProof$ctxt_fc FEMPTY FEMPTY [] [] []``;
