(*
  Direct HOL observations for is_valid_value_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:67-74.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "is_valid_value_local"
  ``is_valid_value (^s with locals := FEMPTY |+
      (strlit "x", ValWord 1w)) panLang$Local (strlit "x") (ValWord 9w)``;

val _ = print_eval "is_valid_value_global"
  ``is_valid_value (^s with globals := FEMPTY |+
      (strlit "g", RStruct [ValWord 2w; ValWord 3w])) panLang$Global
      (strlit "g") (RStruct [ValWord 4w; ValWord 5w])``;

val _ = print_eval "is_valid_value_missing"
  ``is_valid_value (^s with locals := FEMPTY) panLang$Local
      (strlit "missing") (ValWord 9w)``;

val _ = print_eval "is_valid_value_mismatch"
  ``is_valid_value (^s with globals := FEMPTY |+
      (strlit "g", RStruct [ValWord 2w; ValWord 3w])) panLang$Global
      (strlit "g") (ValWord 9w)``;
