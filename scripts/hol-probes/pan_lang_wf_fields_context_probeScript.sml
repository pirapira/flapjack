(*
  Direct HOL-EVAL observations for Pancake panLang$is_wf_flds and
  panLang$is_wf_ctxt.
  Reference: cakeml/pancake/panLangScript.sml:148-160.
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

val forward_context =
  ``[(strlit "Outer", <| fields := [(strlit "inner", Named (strlit "Inner"))];
                                   size := 1 |>);
      (strlit "Inner", <| fields := [(strlit "value", One)]; size := 1 |>)]``;

val duplicate_context =
  ``[(strlit "Dup", <| fields := []; size := 0 |>);
      (strlit "Dup", <| fields := []; size := 0 |>)]``;

val self_reference_context =
  ``[(strlit "Self", <| fields := [(strlit "value", Named (strlit "Self"))];
                                  size := 1 |>)]``;

val _ = print_eval "empty_fields"
  ``is_wf_flds ([] : (mlstring # panLang$struct_info) list) []``;
val _ = print_eval "pair_fields"
  ``is_wf_flds ^pair_context
      [(strlit "left", One); (strlit "right", One)]``;
val _ = print_eval "unknown_field_shape"
  ``is_wf_flds ^pair_context
      [(strlit "missing", Named (strlit "Missing"))]``;
val _ = print_eval "forward_context"
  ``is_wf_ctxt ^forward_context``;
val _ = print_eval "duplicate_context"
  ``is_wf_ctxt ^duplicate_context``;
val _ = print_eval "self_reference_context"
  ``is_wf_ctxt ^self_reference_context``;
