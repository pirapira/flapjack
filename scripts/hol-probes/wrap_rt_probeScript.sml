(* Direct HOL-EVAL probes for pan_to_crep$wrap_rt.
   Reference: cakeml/pancake/pan_to_crepScript.sml:131-136. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "none"
  ``pan_to_crep$wrap_rt NONE``;
val _ = print_eval "empty_one"
  ``pan_to_crep$wrap_rt (SOME (One, []))``;
val _ = print_eval "one_word"
  ``pan_to_crep$wrap_rt (SOME (One, [(1:num)]))``;
val _ = print_eval "comb_empty"
  ``pan_to_crep$wrap_rt (SOME (Comb [], []))``;
val _ = print_eval "named"
  ``pan_to_crep$wrap_rt (SOME (Named «S», []))``;
