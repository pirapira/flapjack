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

val pairStructs = ``[(strlit "Pair",
  <| fields := [(strlit "left", One); (strlit "right", One)]; size := 2 |>)]``;

val _ = print_eval "eval_nstruct_ok"
  ``eval (^s with structs := ^pairStructs)
      (panLang$NStruct (strlit "Pair")
        [(strlit "left", panLang$Const (3w:8 word));
         (strlit "right", panLang$Const (4w:8 word))]) =
      SOME (NStruct (strlit "Pair")
        [(strlit "left", ValWord 3w); (strlit "right", ValWord 4w)])``;

val _ = print_eval "eval_nstruct_name_mismatch"
  ``eval (^s with structs := ^pairStructs)
      (panLang$NStruct (strlit "Pair")
        [(strlit "left", panLang$Const (3w:8 word));
         (strlit "bad", panLang$Const (4w:8 word))]) = NONE``;

val _ = print_eval "eval_nstruct_shape_mismatch"
  ``eval (^s with structs := ^pairStructs)
      (panLang$NStruct (strlit "Pair")
        [(strlit "left", panLang$Const (3w:8 word));
         (strlit "right", panLang$RStruct [])]) = NONE``;

val _ = print_eval "eval_missing_struct"
  ``eval (^s with structs := [])
      (panLang$NStruct (strlit "Pair") []) = NONE``;

val _ = print_eval "eval_probe_done" ``0``;
