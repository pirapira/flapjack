(* Direct HOL-EVAL rows for the Bool-valued value predicates used by
   pan_structsProofScript.sml's compile_correct theorem. *)
load "bossLib";
load "preamble";
load "panSemTheory";
load "pan_structsTheory";
load "pan_structsProofTheory";
load "panPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val context =
  ``[(strlit "Pair",
      <| fields := [(strlit "left", panLang$One);
                    (strlit "right", panLang$Comb [])];
         size := 2 |>)]``;
val duplicate_context =
  ``[(strlit "Pair", <| fields := [(strlit "wrong", panLang$One)]; size := 1 |>);
    (strlit "Pair",
      <| fields := [(strlit "left", panLang$One);
                    (strlit "right", panLang$Comb [])];
         size := 2 |>)]``;
val matching_value =
  ``panSem$NStruct (strlit "Pair")
      [(strlit "left", ValWord 2w);
       (strlit "right", panSem$RStruct [])]``;
val mismatching_value =
  ``panSem$NStruct (strlit "Pair")
      [(strlit "left", ValWord 2w);
       (strlit "wrong", panSem$RStruct [])]``;
val duplicate_context_first =
  ``[(strlit "Pair",
      <| fields := [(strlit "left", panLang$One);
                    (strlit "right", panLang$Comb [])];
         size := 2 |>);
    (strlit "Pair", <| fields := [(strlit "wrong", panLang$One)]; size := 1 |>)]``;
val nested_context =
  ``[(strlit "Pair",
      <| fields := [(strlit "left", panLang$One);
                    (strlit "right", panLang$Comb [])];
         size := 2 |>);
    (strlit "Outer",
      <| fields := [(strlit "inner", panLang$Named (strlit "Pair"));
                    (strlit "tag", panLang$One)];
         size := 2 |>)]``;
val nested_value =
  ``panSem$NStruct (strlit "Outer")
      [(strlit "inner",
          panSem$NStruct (strlit "Pair")
            [(strlit "left", ValWord 2w);
             (strlit "right", panSem$RStruct [])]);
       (strlit "tag", ValWord 3w)]``;

val _ = print_eval "v_flds_ok_word"
  ``pan_structsProof$v_flds_ok ^context (ValWord 1w)``;
val _ = print_eval "v_flds_ok_named_match"
  ``pan_structsProof$v_flds_ok ^context ^matching_value``;
val _ = print_eval "v_flds_ok_named_mismatch"
  ``pan_structsProof$v_flds_ok ^context ^mismatching_value``;
val _ = print_eval "v_flds_ok_named_missing"
  ``pan_structsProof$v_flds_ok [] ^matching_value``;
val _ = print_eval "v_flds_ok_duplicate_first"
  ``pan_structsProof$v_flds_ok ^duplicate_context ^matching_value``;

val _ = print_eval "is_wf_shape_v_word"
  ``panProps$is_wf_shape_v ^context (ValWord 1w)``;
val _ = print_eval "is_wf_shape_v_named_match"
  ``panProps$is_wf_shape_v ^context ^matching_value``;
val _ = print_eval "is_wf_shape_v_named_missing"
  ``panProps$is_wf_shape_v [] ^matching_value``;
val _ = print_eval "is_wf_shape_v_named_mismatch"
  ``panProps$is_wf_shape_v ^context ^mismatching_value``;
val _ = print_eval "v_flds_ok_duplicate_second"
  ``pan_structsProof$v_flds_ok ^duplicate_context_first ^matching_value``;
val _ = print_eval "is_wf_shape_v_duplicate_second"
  ``panProps$is_wf_shape_v ^duplicate_context_first ^matching_value``;
val _ = print_eval "v_flds_ok_nested_match"
  ``pan_structsProof$v_flds_ok ^nested_context ^nested_value``;
val _ = print_eval "is_wf_shape_v_nested_match"
  ``panProps$is_wf_shape_v ^nested_context ^nested_value``;
val _ = print_eval "value_validity_done" ``0``;
