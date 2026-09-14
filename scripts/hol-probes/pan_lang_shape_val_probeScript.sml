(*
  Direct HOL observations for Pancake panLang$shape_val.
  Reference: cakeml/pancake/panLangScript.sml:190-195.
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
  ``shape_val (One : panLang$shape)``
val _ = print_eval "comb"
  ``shape_val (Comb [One; Named (strlit "n"); One] : panLang$shape)``
val _ = print_eval "named"
  ``shape_val (Named (strlit "n") : panLang$shape)``
