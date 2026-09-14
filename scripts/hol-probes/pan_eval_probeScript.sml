(*
  Direct HOL observations for eval_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:79-158.
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

val _ = print_eval "eval_const"
  ``eval ^s (panLang$Const (7w:8 word)) = SOME (ValWord 7w)``;

val _ = print_eval "eval_local"
  ``eval (^s with locals := FEMPTY |+ (strlit "x", ValWord 5w))
      (panLang$Var panLang$Local (strlit "x")) = SOME (ValWord 5w)``;

val _ = print_eval "eval_global"
  ``eval (^s with globals := FEMPTY |+ (strlit "g", ValWord 6w))
      (panLang$Var panLang$Global (strlit "g")) = SOME (ValWord 6w)``;

val _ = print_eval "eval_field"
  ``eval ^s (panLang$RField 1
      (panLang$RStruct [panLang$Const (2w:8 word);
                       panLang$Const (9w:8 word)])) = SOME (ValWord 9w)``;

val _ = print_eval "eval_missing"
  ``eval (^s with locals := FEMPTY)
      (panLang$Var panLang$Local (strlit "missing")) = NONE``;
