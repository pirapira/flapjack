(* Direct HOL-EVAL probes for pan_to_crep$comp_field.
   Reference: cakeml/pancake/pan_to_crepScript.sml:28-33. *)
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

val _ = print_eval "first"
  ``pan_to_crep$comp_field 0
      [One; Comb [One; One]]
      [Const (1w : 8 word); Const 2w; Const 3w]``;
val _ = print_eval "second"
  ``pan_to_crep$comp_field 1
      [One; Comb [One; One]]
      [Const (1w : 8 word); Const 2w; Const 3w]``;
val _ = print_eval "fallback"
  ``pan_to_crep$comp_field 2
      [One]
      [Const (4w : 8 word)]``;
