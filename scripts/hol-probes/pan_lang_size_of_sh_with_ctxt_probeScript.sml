(*
  Direct HOL-EVAL observations for Pancake panLang$size_of_sh_with_ctxt.
  Reference: cakeml/pancake/panLangScript.sml:164-171.
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

val pair_context =
  ``[(strlit "Pair", <| fields := [(strlit "left", One);
                                     (strlit "right", One)]; size := 2 |>)]``;

val _ = print_eval "one"
  ``size_of_sh_with_ctxt
      ([] : (mlstring # panLang$struct_info) list) One``;
val _ = print_eval "known_named"
  ``size_of_sh_with_ctxt ^pair_context (Named (strlit "Pair"))``;
val _ = print_eval "missing_named"
  ``size_of_sh_with_ctxt ^pair_context (Named (strlit "Missing"))``;
val _ = print_eval "nested_comb"
  ``size_of_sh_with_ctxt ^pair_context
      (Comb [One; Named (strlit "Pair"); Comb [One; One]])``;
