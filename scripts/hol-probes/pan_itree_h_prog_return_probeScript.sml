(*
  Direct HOL observations for h_prog_return_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:456-464.
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

val _ = print_eval "return_valid_locals"
  ``case h_prog_return (panLang$Const (7w:8 word)) ^s of
      | itreeTau$Ret (INR (SOME (Return value),s')) => s'.locals = FEMPTY
      | _ => F``;

val _ = print_eval "return_invalid"
  ``case h_prog_return (panLang$Var panLang$Local (strlit "missing"))
      (^s with locals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;
