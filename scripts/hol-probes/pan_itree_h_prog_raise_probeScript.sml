(*
  Direct HOL observations for h_prog_raise_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:445-454.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;
val valid_s = ``(^s with eshapes := FEMPTY |+ (strlit "E", One))``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "raise_valid_locals"
  ``case h_prog_raise (strlit "E") (panLang$Const (7w:8 word)) ^valid_s of
      | itreeTau$Ret (INR (SOME (Exception eid value),s')) =>
          s'.locals = FEMPTY
      | _ => F``;

val _ = print_eval "raise_invalid"
  ``case h_prog_raise (strlit "E") (panLang$Const (7w:8 word))
      (^s with eshapes := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;
