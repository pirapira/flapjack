(*
  Direct HOL observations for crepSem$evaluate.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:240-446.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;
val s1 = ``(^s with locals := ^s.locals |+ (0, Word (7w:8 word)))``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "evaluate_skip_result"
  ``case crepSem$evaluate (Skip,^s) of
      (res,s') => res = NONE``;
val _ = print_eval "evaluate_skip_clock"
  ``case crepSem$evaluate (Skip,^s) of
      (res,s') => s'.clock = ^s.clock``;
val _ = print_eval "evaluate_assign_state"
  ``case crepSem$evaluate (Assign 0 (Const (3w:8 word)),^s1) of
      (res,s') => FLOOKUP s'.locals 0 = SOME (Word (3w:8 word))``;
val _ = print_eval "evaluate_seq_return"
  ``case crepSem$evaluate
       (Seq (Assign 0 (Const (3w:8 word))) (Return [Var 0]),^s1) of
      (res,s') => res = SOME (Return [Word (3w:8 word)])``;
val _ = print_eval "evaluate_break"
  ``case crepSem$evaluate (Break 3,^s) of
      (res,s') => res = SOME (Break 3)``;
val _ = print_eval "evaluate_missing"
  ``case crepSem$evaluate (Return [Var 99],^s with locals := FEMPTY) of
      (res,s') => res = SOME Error``;
