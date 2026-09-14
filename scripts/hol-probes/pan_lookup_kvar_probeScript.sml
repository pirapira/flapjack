(*
  Direct HOL observations for lookup_kvar_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:60-64.
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

val _ = print_eval "lookup_kvar_local"
  ``lookup_kvar panLang$Local (strlit "x")
      (^s with locals := FEMPTY |+ (strlit "x", ValWord 1w)) =
      SOME (ValWord 1w)``;

val _ = print_eval "lookup_kvar_global"
  ``lookup_kvar panLang$Global (strlit "g")
      (^s with globals := FEMPTY |+ (strlit "g", ValWord 2w)) =
      SOME (ValWord 2w)``;

val _ = print_eval "lookup_kvar_missing"
  ``lookup_kvar panLang$Local (strlit "missing")
      (^s with locals := FEMPTY) = NONE``;
