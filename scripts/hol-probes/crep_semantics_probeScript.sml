(*
  Direct HOL observations for crepSem$semantics_def's clock-indexed
  classification.  The top-level existential/LUB expression is intentionally
  observed through the same finite evaluate projections used by semantics_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:448-472.
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

val _ = print_eval "semantics_timeout_is_nonterminal"
  ``case crepSem$evaluate (Tick,^s with clock := 0) of
      (res,s') => res = SOME TimeOut``;
val _ = print_eval "semantics_return_is_success"
  ``case crepSem$evaluate (Return [Const (7w:8 word)],^s) of
      (res,s') => res = SOME (Return [Word (7w:8 word)])``;
val _ = print_eval "semantics_break_is_nonterminal"
  ``case crepSem$evaluate (Break 2,^s) of
      (res,s') => res = SOME (Break 2)``;
