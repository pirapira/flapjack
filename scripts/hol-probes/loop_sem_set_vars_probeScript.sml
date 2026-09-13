(*
  Probe outputs for the original CakeML Pancake loopSem definition set_vars.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is regenerated with scripts/hol-probes/regenerate.sh.

  Reference: cakeml/pancake/semantics/loopSemScript.sml:113-116 (set_vars_def),
  which uses sptree$alist_insert (sptreeScript.sml:2085-2089).

  alist_insert inserts the head pair outermost, so the FIRST occurrence of a
  repeated name wins, and it truncates to the shorter of the two lists.
  The observations read the resulting locals back through the original
  get_vars definition (lookup itself is [nocompute] and does not EVAL).
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

val _ = print_eval "set_vars_basic"
  ``get_vars [1;2] (set_vars [1;2] [Word 5w; Word 7w] (^s with locals := LN))``
val _ = print_eval "set_vars_missing"
  ``get_vars [3] (set_vars [1;2] [Word 5w; Word 7w] (^s with locals := LN))``
val _ = print_eval "set_vars_duplicate"
  ``get_vars [1] (set_vars [1;1] [Word 5w; Word 7w] (^s with locals := LN))``
val _ = print_eval "set_vars_short_values"
  ``get_vars [1;2] (set_vars [1;2] [Word 5w] (^s with locals := LN))``
val _ = print_eval "set_vars_overwrite"
  ``get_vars [1] (set_vars [1] [Word 9w] (^s with locals := insert 1 (Word 1w) LN))``
val _ = print_eval "set_vars_empty"
  ``get_vars [1] (set_vars [] [] (^s with locals := LN))``
val _ = print_eval "set_vars_clock"
  ``(set_vars [1] [Word 5w] (^s with locals := LN)).clock``