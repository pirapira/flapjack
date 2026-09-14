(*
  Direct HOL observations for h_prog_deccall_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:404-411.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``((s:(8) pan_itreeSem$bstate) with code := FEMPTY)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "argument_failure"
  ``case h_prog_deccall (strlit "result") One (strlit "callee") []
      panLang$Skip ^s of
      | itreeTau$Ret (INR (SOME Error,s')) => s' = ^s
      | _ => F``;

val _ = print_eval "lookup_failure"
  ``case h_prog_deccall (strlit "result") One (strlit "missing")
      [panLang$Const (7w:8 word)] panLang$Skip ^s of
      | itreeTau$Ret (INR (SOME Error,s')) => s' = ^s
      | _ => F``;
