(*
  Direct HOL-EVAL observations for Pancake panLang$is_wf_shape.
  Reference: cakeml/pancake/panLangScript.sml:139-144.
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
  ``is_wf_shape ([] : (mlstring # panLang$struct_info) list) One``
val _ = print_eval "empty_comb"
  ``is_wf_shape ([] : (mlstring # panLang$struct_info) list) (Comb [])``
val _ = print_eval "known_named"
  ``is_wf_shape
      [(strlit "Pair", <| fields := [(strlit "left", One);
                                       (strlit "right", One)]; size := 2 |>)]
      (Named (strlit "Pair"))``
val _ = print_eval "unknown_named"
  ``is_wf_shape
      [(strlit "Pair", <| fields := [(strlit "left", One);
                                       (strlit "right", One)]; size := 2 |>)]
      (Named (strlit "Missing"))``
val _ = print_eval "nested_comb"
  ``is_wf_shape
      [(strlit "Pair", <| fields := [(strlit "left", One);
                                       (strlit "right", One)]; size := 2 |>)]
      (Comb [One; Named (strlit "Pair"); Comb [One]])``
val _ = print_eval "nested_unknown"
  ``is_wf_shape
      [(strlit "Pair", <| fields := [(strlit "left", One);
                                       (strlit "right", One)]; size := 2 |>)]
      (Comb [Named (strlit "Pair"); Named (strlit "Missing")])``
