(*
  Direct HOL observations for h_prog_dec_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:226-238.
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

val _ = print_eval "dec_valid_event"
  ``case h_prog_dec (strlit "x") panLang$One
      (panLang$Const (7w:8 word)) panLang$Skip (^s with locals := FEMPTY) of
      | itreeTau$Vis (INL (p,s')) k =>
          s'.locals = FEMPTY |+ (strlit "x", ValWord 7w)
      | _ => F``;

val _ = print_eval "dec_valid_restore"
  ``case h_prog_dec (strlit "x") panLang$One
      (panLang$Const (7w:8 word)) panLang$Skip (^s with locals := FEMPTY) of
      | itreeTau$Vis (INL (p,s')) k =>
          (case k (INR (NONE,s')) of
             | itreeTau$Ret (INR (res,s'')) =>
                 res = NONE /\
                 FLOOKUP s''.locals (strlit "x") = NONE
             | _ => F)
      | _ => F``;

val _ = print_eval "dec_invalid_eval"
  ``case h_prog_dec (strlit "x") panLang$One
      (panLang$Var panLang$Local (strlit "missing")) panLang$Skip
      (^s with locals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "dec_wrong_shape"
  ``case h_prog_dec (strlit "x") (panLang$Comb [])
      (panLang$Const (7w:8 word)) panLang$Skip (^s with locals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "dec_failed_response"
  ``case h_prog_dec (strlit "x") panLang$One
      (panLang$Const (7w:8 word)) panLang$Skip (^s with locals := FEMPTY) of
      | itreeTau$Vis (INL (p,s')) k =>
          (case k (INL FFI_failed) of
             | itreeTau$Ret (INR (SOME Error,s'')) =>
                 s''.locals = FEMPTY
             | _ => F)
      | _ => F``;
