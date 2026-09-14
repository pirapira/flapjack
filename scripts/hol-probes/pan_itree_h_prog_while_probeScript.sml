(*
  Direct HOL observations for h_prog_while_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:318-336.
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
    val th = SIMP_CONV (srw_ss()) [h_prog_while_def, eval_def,
      Once itreeTauTheory.itree_iter_thm,
      Once itreeTauTheory.itree_iter_thm,
      itreeTauTheory.itree_bind_thm] q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "while_zero_guard"
  ``case h_prog_while (panLang$Const (0w:8 word)) panLang$Skip ^s of
      | itreeTau$Ret (INR (NONE,s')) => T
      | _ => F``;

val _ = print_eval "while_body_event"
  ``case h_prog_while (panLang$Const (1w:8 word)) panLang$Skip ^s of
      | itreeTau$Vis (INL (panLang$Skip,s')) k => T
      | _ => F``;

val _ = print_eval "while_break"
  ``case h_prog_while (panLang$Const (1w:8 word)) panLang$Skip ^s of
      | itreeTau$Vis (INL (p,s')) k =>
          (case k (INR (SOME Break,s')) of
             | itreeTau$Ret (INR (NONE,s'')) => T
             | _ => F)
      | _ => F``;

val _ = print_eval "while_continue"
  ``case h_prog_while (panLang$Const (1w:8 word)) panLang$Skip ^s of
      | itreeTau$Vis (INL (p,s')) k =>
          (case k (INR (SOME Continue,s')) of
             | itreeTau$Tau _ => T
             | itreeTau$Vis (INL (panLang$Skip,s'')) k' => T
             | _ => F)
      | _ => F``;

val _ = print_eval "while_normal"
  ``case h_prog_while (panLang$Const (1w:8 word)) panLang$Skip ^s of
      | itreeTau$Vis (INL (p,s')) k =>
          (case k (INR (NONE,s')) of
             | itreeTau$Tau _ => T
             | itreeTau$Vis (INL (panLang$Skip,s'')) k' => T
             | _ => F)
      | _ => F``;

val _ = print_eval "while_failed"
  ``case h_prog_while (panLang$Const (1w:8 word)) panLang$Skip ^s of
      | itreeTau$Vis (INL (p,s')) k =>
          (case k (INL FFI_failed) of
             | itreeTau$Ret (INR (SOME Error,s'')) => T
             | _ => F)
      | _ => F``;

val _ = print_eval "while_invalid_guard"
  ``case h_prog_while
      (panLang$Var panLang$Local (strlit "missing")) panLang$Skip
      (^s with locals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;
