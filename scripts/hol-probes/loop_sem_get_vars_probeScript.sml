(*
  Probe outputs for the original CakeML Pancake loopSem definition get_vars.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is regenerated with scripts/hol-probes/regenerate.sh.

  Reference: cakeml/pancake/semantics/loopSemScript.sml:98-106 (get_vars_def).
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:('a,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "get_vars_hit"
  ``get_vars [1;2] (^s with locals := insert 1 (Word 5w) (insert 2 (Word 7w) LN))``
val _ = print_eval "get_vars_miss"
  ``get_vars [1;3] (^s with locals := insert 1 (Word 5w) LN)``
val _ = print_eval "get_vars_empty" ``get_vars [] ^s``
val _ = print_eval "get_vars_order"
  ``get_vars [2;1] (^s with locals := insert 1 (Word 5w) (insert 2 (Word 7w) LN))``
val _ = print_eval "get_vars_loc"
  ``get_vars [1] (^s with locals := insert 1 (wordLang$Loc 9 0) LN)``
