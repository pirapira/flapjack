(*
  Direct HOL observations for Pancake panLang$with_shape.
  Reference: cakeml/pancake/panLangScript.sml:216-219.
*)
load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "empty_shapes"
  ``with_shape ([] : panLang$shape list) [1; 2; 3]``
val _ = print_eval "one_comb_named"
  ``with_shape [One; Comb [One; One]; Named (strlit "n")]
      [1; 2; 3; 4; 5]``
val _ = print_eval "short_input"
  ``with_shape [Comb [One; One]; One] [7]``
