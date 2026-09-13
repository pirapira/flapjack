(*
  Direct HOL-EVAL fixture for Pancake loopSem cut_res_def.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:189-197.
  The observations cover result short-circuiting, a failed cut, timeout local
  clearing, and successful local restriction plus clock decrement.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(32,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "result_short_circuit"
  ``case loopSem$cut_res (insert 1 T LN)
      (SOME (Break 3), ^s with clock := 7) of
      (res,s') => (res, s'.clock)``
val _ = print_eval "cut_missing_error"
  ``case loopSem$cut_res (insert 1 T (insert 3 T LN))
      (NONE, ^s with <| locals := insert 1 (Word 5w) LN; clock := 7 |>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "clock_zero_timeout"
  ``case loopSem$cut_res (insert 1 T LN)
      (NONE, ^s with <| locals := insert 1 (Word 5w) LN; clock := 0 |>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "clock_decrement_and_cut"
  ``case loopSem$cut_res (insert 1 T LN)
      (NONE, ^s with <| locals := insert 1 (Word 5w)
                         (insert 2 (Word 7w) LN); clock := 5 |>) of
      (res,s') => (res, lookup 1 s'.locals, lookup 2 s'.locals, s'.clock)``
