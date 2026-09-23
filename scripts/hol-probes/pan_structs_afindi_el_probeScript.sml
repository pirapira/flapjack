(* Direct HOL-EVAL observations for pan_structsProof$afindi_EL.
   Reference: cakeml/pancake/proofs/pan_structsProofScript.sml:430. *)
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

val _ = print_eval "first_match_fst"
  ``afindi "a" [("a", 10); ("b", 20); ("c", 30)] = SOME 0 ==>
    FST (EL 0 [("a", 10); ("b", 20); ("c", 30)]) = "a"``;
val _ = print_eval "middle_match_fst"
  ``afindi "b" [("a", 10); ("b", 20); ("c", 30)] = SOME 1 ==>
    FST (EL 1 [("a", 10); ("b", 20); ("c", 30)]) = "b"``;
val _ = print_eval "last_match_fst"
  ``afindi "c" [("a", 10); ("b", 20); ("c", 30)] = SOME 2 ==>
    FST (EL 2 [("a", 10); ("b", 20); ("c", 30)]) = "c"``;
