(* Direct HOL-EVAL observations for pan_structsProof$dropWhile_afindi.
   Reference: cakeml/pancake/proofs/pan_structsProofScript.sml:334. *)
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

val _ = print_eval "first_hit_drop"
  ``dropWhile (\(k,v). k <> "a") [("a", 10); ("b", 20); ("c", 30)] =
    (case afindi "a" [("a", 10); ("b", 20); ("c", 30)] of
       NONE => []
     | SOME n => DROP n [("a", 10); ("b", 20); ("c", 30)])``;
val _ = print_eval "later_hit_drop"
  ``dropWhile (\(k,v). k <> "b") [("a", 10); ("b", 20); ("c", 30)] =
    (case afindi "b" [("a", 10); ("b", 20); ("c", 30)] of
       NONE => []
     | SOME n => DROP n [("a", 10); ("b", 20); ("c", 30)])``;
val _ = print_eval "missing_hit_drop"
  ``dropWhile (\(k,v). k <> "z") [("a", 10); ("b", 20); ("c", 30)] =
    (case afindi "z" [("a", 10); ("b", 20); ("c", 30)] of
       NONE => []
     | SOME n => DROP n [("a", 10); ("b", 20); ("c", 30)])``;
