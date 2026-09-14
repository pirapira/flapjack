(*
  Direct HOL observations for panSem$is_valid_value_def.
  Reference: cakeml/pancake/semantics/panSemScript.sml:469-475.
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

val _ = print_eval "is_valid_value_local_shape"
  ``panSem$is_valid_value ^base panLang$Local (strlit "x")
      (ValWord (9w:8 word))``;

val _ = print_eval "is_valid_value_global_shape"
  ``panSem$is_valid_value ^base panLang$Global (strlit "g")
      (ValWord (9w:8 word))``;

val _ = print_eval "is_valid_value_mismatch"
  ``panSem$is_valid_value ^base panLang$Local (strlit "x")
      (RStruct [])``;

val _ = print_eval "is_valid_value_missing"
  ``panSem$is_valid_value ^base panLang$Local (strlit "missing")
      (ValWord (9w:8 word))``;
