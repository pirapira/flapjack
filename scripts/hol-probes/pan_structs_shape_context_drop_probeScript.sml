(* Direct HOL EVAL rows for pan_structsProof$size_of_sh_with_ctxt_drop. *)
load "bossLib";
load "preamble";
load "pan_structsTheory";
load "pan_structsProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory pan_structsTheory pan_structsProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val ctxt =
  ``[(strlit "Prefix", <| fields := []; size := 1 |>);
     (strlit "Target", <| fields := []; size := 3 |>)]``;
val named = ``Named (strlit "Target")``;
val nested = ``Comb [One; Named (strlit "Target");
    Comb [Named (strlit "Target"); One]]``;

val _ = print_eval "size_sh_with_ctxt_drop_one"
  ``(is_wf_shape (DROP 1 ^ctxt) One,
     ALL_DISTINCT (MAP FST ^ctxt),
     size_of_sh_with_ctxt (DROP 1 ^ctxt) One = size_of_sh_with_ctxt ^ctxt One)``;
val _ = print_eval "size_sh_with_ctxt_drop_named"
  ``(is_wf_shape (DROP 1 ^ctxt) ^named,
     ALL_DISTINCT (MAP FST ^ctxt),
     size_of_sh_with_ctxt (DROP 1 ^ctxt) ^named = size_of_sh_with_ctxt ^ctxt ^named)``;
val _ = print_eval "size_sh_with_ctxt_drop_nested_comb"
  ``(is_wf_shape (DROP 1 ^ctxt) ^nested,
     ALL_DISTINCT (MAP FST ^ctxt),
     size_of_sh_with_ctxt (DROP 1 ^ctxt) ^nested = size_of_sh_with_ctxt ^ctxt ^nested)``;
