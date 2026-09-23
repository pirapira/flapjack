(* Direct HOL-EVAL observations for pan_structsProof$afindi_MAP_eq.
   Reference: cakeml/pancake/proofs/pan_structsProofScript.sml:356. *)
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

val _ = print_eval "hit_preserves_key_index"
  ``afindi "c" (MAP (\(k,v). (k, v + 1)) [("a", 10); ("b", 20); ("c", 30)]) =
    afindi "c" [("a", 10); ("b", 20); ("c", 30)]``;
val _ = print_eval "missing_key_stays_missing"
  ``afindi "z" (MAP (\(k,v). (k, v + 1)) [("a", 10); ("b", 20); ("c", 30)]) =
    afindi "z" [("a", 10); ("b", 20); ("c", 30)]``;
