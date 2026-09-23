(* Direct HOL-EVAL observations for pan_structsProof$afindi_append.
   Reference: cakeml/pancake/proofs/pan_structsProofScript.sml:417. *)
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

val _ = print_eval "prefix_hit_keeps_first_index"
  ``afindi "b" ([("a", 1); ("b", 2)] ++ [("b", 99)]) =
    (case afindi "b" [("a", 1); ("b", 2)] of
       NONE => OPTION_MAP (\i. LENGTH [("a", 1); ("b", 2)] + i)
                 (afindi "b" [("b", 99)])
     | SOME i => SOME i)``;
val _ = print_eval "suffix_hit_adds_prefix_length"
  ``afindi "b" ([("a", 1)] ++ [("b", 2); ("b", 3)]) =
    (case afindi "b" [("a", 1)] of
       NONE => OPTION_MAP (\i. LENGTH [("a", 1)] + i)
                 (afindi "b" [("b", 2); ("b", 3)])
     | SOME i => SOME i)``;
val _ = print_eval "missing_key_stays_none"
  ``afindi "z" ([("a", 1)] ++ [("b", 2)]) =
    (case afindi "z" [("a", 1)] of
       NONE => OPTION_MAP (\i. LENGTH [("a", 1)] + i)
                 (afindi "z" [("b", 2)])
     | SOME i => SOME i)``;
