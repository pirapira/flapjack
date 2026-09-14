(*
  Direct HOL observations for h_handle_deccall_ret_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:388-401.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``((s:(8) pan_itreeSem$bstate) with
  locals := (FEMPTY : (mlstring |-> 8 v)))``;
val empty_s = ``(^s with locals := (FEMPTY : (mlstring |-> 8 v)))``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "failed_caller"
  ``case h_handle_deccall_ret (strlit "result") One panLang$Skip One ^s
      (INL FFI_failed) of
      | itreeTau$Ret (INR (SOME Error,s')) => s' = ^s
      | _ => F``;

val _ = print_eval "returned_event"
  ``case h_handle_deccall_ret (strlit "result") One panLang$Skip One ^s
      (INR (SOME (Return (ValWord (8w:8 word))),^empty_s)) of
      | itreeTau$Vis (INL (panLang$Skip,s')) k => T
      | _ => F``;

val _ = print_eval "shape_mismatch"
  ``case h_handle_deccall_ret (strlit "result") (Comb []) panLang$Skip One ^s
      (INR (SOME (Return (ValWord (8w:8 word))),^s)) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "raised_clears_locals"
  ``case h_handle_deccall_ret (strlit "result") One panLang$Skip One ^s
      (INR (SOME (Exception (strlit "E") (ValWord (9w:8 word))),^s)) of
      | itreeTau$Ret (INR (SOME (Exception (strlit "E") (ValWord 9w)),s')) => T
      | _ => F``;
