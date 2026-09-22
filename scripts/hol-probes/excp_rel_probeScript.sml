(* Direct HOL-EVAL probes for pan_to_crepProof$excp_rel. *)
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

val _ = print_eval "empty_maps"
  ``pan_to_crepProof$excp_rel
      (FEMPTY : panLang$eid |-> 8 word)
      (FEMPTY : panLang$eid |-> panLang$shape)``;
val _ = print_eval "same_domain_injective"
  ``pan_to_crepProof$excp_rel
      (FEMPTY |+ («E», (0w : 8 word)) |+ («F», 1w))
      (FEMPTY |+ («E», panLang$One) |+ («F», panLang$Comb []))``;
val _ = print_eval "domain_mismatch"
  ``pan_to_crepProof$excp_rel
      (FEMPTY |+ («E», (0w : 8 word)))
      (FEMPTY |+ («F», panLang$One))``;
val _ = print_eval "noninjective_compiler_codes"
  ``pan_to_crepProof$excp_rel
      (FEMPTY |+ («E», (0w : 8 word)) |+ («F», 0w))
      (FEMPTY |+ («E», panLang$One) |+ («F», panLang$Comb []))``;
