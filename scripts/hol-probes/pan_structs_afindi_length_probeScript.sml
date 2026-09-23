(* Direct HOL-EVAL observations for pan_structsProof$afindi_less_length.
   Reference: cakeml/pancake/proofs/pan_structsProofScript.sml:345. *)
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

val _ = print_eval "first_match_strictly_below_length"
  ``afindi "a" [("a", 10); ("b", 20)] = SOME 0 ==> 0 < LENGTH [("a", 10); ("b", 20)]``;
val _ = print_eval "last_match_strictly_below_length"
  ``afindi "c" [("a", 10); ("b", 20); ("c", 30)] = SOME 2 ==>
    2 < LENGTH [("a", 10); ("b", 20); ("c", 30)]``;
