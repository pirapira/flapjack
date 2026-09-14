(*
  Direct HOL-EVAL observations for Pancake panLang$size_of_shape.
  Reference: cakeml/pancake/panLangScript.sml:174-178.
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

val _ = print_eval "one"
  ``size_of_shape One``;
val _ = print_eval "empty_comb"
  ``size_of_shape (Comb [])``;
val _ = print_eval "named"
  ``size_of_shape (Named (strlit "Pair"))``;
val _ = print_eval "nested_comb"
  ``size_of_shape (Comb [One; Comb [One; One]; Named (strlit "Pair")])``;
