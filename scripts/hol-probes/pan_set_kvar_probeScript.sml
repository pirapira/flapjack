(*
  Direct HOL observations for set_kvar_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:53-58.
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

val _ = print_eval "set_kvar_local"
  ``FLOOKUP (set_kvar panLang$Local (strlit "x") (ValWord 5w)
      (^s with locals := FEMPTY)).locals (strlit "x") = SOME (ValWord 5w)``;

val _ = print_eval "set_kvar_global"
  ``FLOOKUP (set_kvar panLang$Global (strlit "g") (ValWord 7w)
      (^s with globals := FEMPTY)).globals (strlit "g") = SOME (ValWord 7w)``;

val _ = print_eval "set_kvar_local_globals"
  ``(set_kvar panLang$Local (strlit "x") (ValWord 5w)
      (^s with globals := FEMPTY |+ (strlit "g", ValWord 2w))).globals =
      FEMPTY |+ (strlit "g", ValWord 2w)``;

val _ = print_eval "set_kvar_global_locals"
  ``(set_kvar panLang$Global (strlit "g") (ValWord 7w)
      (^s with locals := FEMPTY |+ (strlit "x", ValWord 1w))).locals =
      FEMPTY |+ (strlit "x", ValWord 1w)``;
