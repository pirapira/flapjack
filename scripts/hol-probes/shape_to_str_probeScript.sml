(* Direct HOL-EVAL observations for Pancake shape_to_str.
   Reference: cakeml/pancake/panLangScript.sml:180-187. *)
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
  ``shape_to_str (One : panLang$shape)``;
val _ = print_eval "empty_comb"
  ``shape_to_str (Comb [] : panLang$shape)``;
val _ = print_eval "nested"
  ``shape_to_str (Comb [One; Named (strlit "Pair"); Comb [One; One]] : panLang$shape)``;
val _ = print_eval "named"
  ``shape_to_str (Named (strlit "Pair") : panLang$shape)``;
