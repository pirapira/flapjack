(*
  Direct HOL-EVAL fixture for Pancake loopSem cut_state_def.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:182-186.
  The observations cover successful restriction, missing live locals, the
  empty live set, and removal of a non-live sibling.
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

val _ = print_eval "hit_first"
  ``case loopSem$cut_state (insert 1 T (insert 2 T LN))
      (^s with locals := insert 1 (Word 5w)
        (insert 2 (Word 7w) (insert 3 (Word 9w) LN))) of
      NONE => NONE | SOME s' => lookup 1 s'.locals``
val _ = print_eval "hit_second"
  ``case loopSem$cut_state (insert 1 T (insert 2 T LN))
      (^s with locals := insert 1 (Word 5w)
        (insert 2 (Word 7w) (insert 3 (Word 9w) LN))) of
      NONE => NONE | SOME s' => lookup 2 s'.locals``
val _ = print_eval "hit_sibling_removed"
  ``case loopSem$cut_state (insert 1 T (insert 2 T LN))
      (^s with locals := insert 1 (Word 5w)
        (insert 2 (Word 7w) (insert 3 (Word 9w) LN))) of
      NONE => NONE | SOME s' => lookup 3 s'.locals``
val _ = print_eval "missing_live"
  ``loopSem$cut_state (insert 1 T (insert 3 T LN))
      (^s with locals := insert 1 (Word 5w) LN)``
val _ = print_eval "empty_live"
  ``case loopSem$cut_state LN (^s with locals := insert 1 (Word 5w) LN) of
      NONE => NONE | SOME s' => lookup 1 s'.locals``
val _ = print_eval "loc_preserved"
  ``case loopSem$cut_state (insert 1 T LN)
      (^s with locals := insert 1 (Loc 9 0) (insert 2 (Word 7w) LN)) of
      NONE => NONE | SOME s' => lookup 1 s'.locals``
