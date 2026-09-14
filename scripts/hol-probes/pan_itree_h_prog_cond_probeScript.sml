(*
  Direct HOL observations for h_prog_cond_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:307-317.
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

val _ = print_eval "cond_true_branch"
  ``case h_prog_cond (panLang$Const (1w:8 word)) panLang$Skip
      panLang$Tick ^s of
      | itreeTau$Vis (INL (panLang$Skip,s')) k => T
      | _ => F``;

val _ = print_eval "cond_false_branch"
  ``case h_prog_cond (panLang$Const (0w:8 word)) panLang$Skip
      panLang$Tick ^s of
      | itreeTau$Vis (INL (panLang$Tick,s')) k => T
      | _ => F``;

val _ = print_eval "cond_invalid_guard"
  ``case h_prog_cond
      (panLang$Var panLang$Local (strlit "missing")) panLang$Skip
      panLang$Tick (^s with locals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "cond_returned_state"
  ``case h_prog_cond (panLang$Const (1w:8 word)) panLang$Skip
      panLang$Tick ^s of
      | itreeTau$Vis (INL (p,s')) k =>
          (case k (INR (NONE,s')) of
             | itreeTau$Ret (INR (NONE,s'')) => s'' = s'
             | _ => F)
      | _ => F``;

val _ = print_eval "cond_failed_source"
  ``case h_prog_cond (panLang$Const (1w:8 word)) panLang$Skip
      panLang$Tick ^s of
      | itreeTau$Vis (INL (p,s')) k =>
          (case k (INL FFI_failed) of
             | itreeTau$Ret (INR (SOME Error,s'')) => s'' = s
             | _ => F)
      | _ => F``;
