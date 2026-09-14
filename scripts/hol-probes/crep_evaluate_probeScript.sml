(*
  Direct HOL observations for crepSem$evaluate_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:240-389.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "evaluate_skip"
  ``crepSem$evaluate (Skip, ^s)``;

val _ = print_eval "evaluate_assign"
  ``case crepSem$evaluate
      (Assign 1 (Const (7w : 8 word)),
       ^s with <|locals := FEMPTY |+ (1, Word 0w); clock := 5|>) of
      (res,s') => (res, FLOOKUP s'.locals 1, s'.clock)``;

val _ = print_eval "evaluate_seq_return"
  ``case crepSem$evaluate
      (Seq (Assign 1 (Const (7w : 8 word))) (Return [Var 1]),
       ^s with <|locals := FEMPTY |+ (1, Word 0w); clock := 5|>) of
      (res,s') => (res, FLOOKUP s'.locals 1, s'.clock)``;

val _ = print_eval "evaluate_tick_timeout"
  ``case crepSem$evaluate
      (Tick, ^s with <|locals := FEMPTY |+ (1, Word 7w); clock := 0|>) of
      (res,s') => (res, FLOOKUP s'.locals 1, s'.clock)``;
