(*
  Direct HOL observations for h_handle_call_ret_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:340-374.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;
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
  ``case h_handle_call_ret NONE One ^s (INL FFI_failed) of
      | itreeTau$Ret (INR (SOME Error,s')) => s' = ^s
      | _ => F``;

val _ = print_eval "returned_empty_locals"
  ``case h_handle_call_ret NONE One ^s
      (INR (SOME (Return (ValWord (7w:8 word))),^empty_s)) of
      | itreeTau$Ret (INR (SOME (Return (ValWord 7w)),s')) =>
          s'.locals = FEMPTY
      | _ => F``;

val _ = print_eval "return_shape_error"
  ``case h_handle_call_ret NONE (Comb []) ^s
      (INR (SOME (Return (ValWord (7w:8 word))),^s)) of
      | itreeTau$Ret (INR (SOME Error,s')) => s' = ^s
      | _ => F``;

val _ = print_eval "uncaught_exception"
  ``case h_handle_call_ret NONE One ^s
      (INR (SOME (Exception (strlit "E") (ValWord (8w:8 word))),^s)) of
      | itreeTau$Ret (INR (SOME (Exception (strlit "E") (ValWord 8w)),s')) =>
          s'.locals = FEMPTY
      | _ => F``;
