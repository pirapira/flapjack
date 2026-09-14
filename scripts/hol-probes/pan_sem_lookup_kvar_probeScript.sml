(*
  Direct HOL observations for panSem$lookup_kvar_def.
  Reference: cakeml/pancake/semantics/panSemScript.sml:415-421.
*)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val s = ``(s:(8,unit) panSem$state)``;
val base = ``(^s with <|locals := FEMPTY |+ (strlit "x", ValWord 5w);
                         globals := FEMPTY |+ (strlit "g", ValWord 7w)|>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "lookup_kvar_local"
  ``panSem$lookup_kvar panLang$Local (strlit "x") ^base =
      SOME (ValWord 5w)``;

val _ = print_eval "lookup_kvar_global"
  ``panSem$lookup_kvar panLang$Global (strlit "g") ^base =
      SOME (ValWord 7w)``;

val _ = print_eval "lookup_kvar_missing"
  ``panSem$lookup_kvar panLang$Local (strlit "missing") ^base = NONE``;
