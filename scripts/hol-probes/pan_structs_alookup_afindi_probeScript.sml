(* Direct HOL-EVAL observations for pan_structsProof$ALOOKUP_eq_afindi.
   Reference: cakeml/pancake/proofs/pan_structsProofScript.sml:405. *)
load "bossLib";
load "preamble";
load "pan_structsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_structsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "present_lookup_projection"
  ``ALOOKUP [("a", 10); ("b", 20); ("c", 30)] "b" =
    OPTION_MAP (\i. SND (EL i [("a", 10); ("b", 20); ("c", 30)]))
      (afindi "b" [("a", 10); ("b", 20); ("c", 30)])``;
val _ = print_eval "missing_lookup_projection"
  ``ALOOKUP [("a", 10); ("b", 20); ("c", 30)] "z" =
    OPTION_MAP (\i. SND (EL i [("a", 10); ("b", 20); ("c", 30)]))
      (afindi "z" [("a", 10); ("b", 20); ("c", 30)])``;
val _ = print_eval "duplicate_key_first_value"
  ``ALOOKUP [("x", 1); ("x", 2)] "x" =
    OPTION_MAP (\i. SND (EL i [("x", 1); ("x", 2)]))
      (afindi "x" [("x", 1); ("x", 2)])``;
