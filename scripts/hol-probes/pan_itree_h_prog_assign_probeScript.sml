(*
  Direct HOL observations for h_prog_assign_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:254-262.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;
val base = ``(^s with locals := FEMPTY |+ (strlit "x", ValWord (0w:8 word)))``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "assign_valid"
  ``case h_prog_assign panLang$Local (strlit "x")
      (panLang$Const (7w:8 word)) ^base of
      | itreeTau$Ret (INR (NONE,s')) =>
          FLOOKUP s'.locals (strlit "x") = SOME (ValWord 7w)
      | _ => F``;

val _ = print_eval "assign_invalid_destination"
  ``case h_prog_assign panLang$Local (strlit "missing")
      (panLang$Const (7w:8 word)) (^s with locals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "assign_invalid_global"
  ``case h_prog_assign panLang$Global (strlit "g")
      (panLang$Const (7w:8 word)) (^s with globals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "assign_failed_eval"
  ``case h_prog_assign panLang$Local (strlit "x")
      (panLang$Var panLang$Local (strlit "missing"))
      (^base with locals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;
