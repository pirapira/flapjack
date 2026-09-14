(*
  Direct HOL observations for h_prog_seq_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:240-254.
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

val _ = print_eval "seq_second_event"
  ``case h_prog_seq panLang$Skip (panLang$Return (panLang$Const 0w)) ^s of
      | itreeTau$Vis (INL (p1,s')) k =>
          (case k (INR (NONE,s')) of
             | itreeTau$Vis (INL (p2,s'')) k2 => T
             | _ => F)
      | _ => F``;

val _ = print_eval "seq_first_error"
  ``case h_prog_seq panLang$Skip (panLang$Return (panLang$Const 0w)) ^s of
      | itreeTau$Vis (INL (p1,s')) k =>
          (case k (INR (SOME Error,s')) of
             | itreeTau$Ret (INR (SOME Error,s'')) => T
             | _ => F)
      | _ => F``;

val _ = print_eval "seq_first_failure"
  ``case h_prog_seq panLang$Skip (panLang$Return (panLang$Const 0w)) ^s of
      | itreeTau$Vis (INL (p1,s')) k =>
          (case k (INL FFI_failed) of
             | itreeTau$Ret (INR (SOME Error,s'')) => T
             | _ => F)
      | _ => F``;

val _ = print_eval "seq_second_failure"
  ``case h_prog_seq panLang$Skip (panLang$Return (panLang$Const 0w)) ^s of
      | itreeTau$Vis (INL (p1,s')) k =>
          (case k (INR (NONE,s')) of
             | itreeTau$Vis (INL (p2,s'')) k2 =>
                 (case k2 (INL FFI_failed) of
                    | itreeTau$Ret (INR (SOME Error,s''')) => T
                    | _ => F)
             | _ => F)
      | _ => F``;

val _ = print_eval "seq_second_normal"
  ``case h_prog_seq panLang$Skip (panLang$Return (panLang$Const 0w)) ^s of
      | itreeTau$Vis (INL (p1,s')) k =>
          (case k (INR (NONE,s')) of
             | itreeTau$Vis (INL (p2,s'')) k2 =>
                 (case k2 (INR (NONE,s'')) of
                    | itreeTau$Ret (INR (NONE,s''')) => T
                    | _ => F)
             | _ => F)
      | _ => F``;
