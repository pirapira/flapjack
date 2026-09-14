(*
  Direct HOL observations for h_prog_call_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:377-385.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;
open panLangTheory;
open panSemTheory;

val s = ``(s:'a pan_itreeSem$bstate)``;
val base = ``(^s with <|locals := FEMPTY; code := FEMPTY|>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "call_eval_failure"
  ``case h_prog_call NONE «callee» [Var Local «missing»] ^base of
      | Ret (INR (SOME Error,^s)) => T
      | _ => F``;

val _ = print_eval "call_lookup_failure"
  ``case h_prog_call NONE «missing» [] ^base of
      | Ret (INR (SOME Error,^s)) => T
      | _ => F``;

val code_entry =
  ``([(«arg»,One)],Skip,One)``;

val _ = print_eval "call_success"
  ``case h_prog_call NONE «callee» [Const 1w]
      (^base with code := FEMPTY |+ («callee»,^code_entry)) of
      | Vis (INL (Skip,s')) k =>
          (case FLOOKUP s'.locals «arg» of
             | SOME (ValWord 1w) =>
                 (case k (INL ()) of
                    | Ret (INR (SOME Error,_)) => T
                    | _ => F)
             | _ => F)
      | _ => F``;
