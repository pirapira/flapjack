(*
  Probe outputs for the original CakeML Pancake loopSem definition
  set_globals. This is intentionally a HOL script rather than a second
  implementation. The checked-in output is regenerated with
  scripts/hol-probes/regenerate.sh.

  Reference: cakeml/pancake/semantics/loopSemScript.sml:52-55 (set_globals_def).
  The original state field is globals : 5 word |-> 'a word_loc, read with
  FLOOKUP (loopSemScript.sml:74), so the probe observes FLOOKUP after update.
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

val _ = print_eval "set_globals_new"
  ``FLOOKUP (set_globals 3w (Word 5w) ^s).globals 3w``
val _ = print_eval "set_globals_overwrite"
  ``FLOOKUP (set_globals 3w (Word 5w) (^s with globals := (s.globals |+ (3w,Word 1w)))).globals 3w``
val _ = print_eval "set_globals_miss"
  ``FLOOKUP (set_globals 3w (Word 5w) (^s with globals := FEMPTY)).globals 4w``
val _ = print_eval "set_globals_sibling"
  ``FLOOKUP (set_globals 4w (Word 7w) (^s with globals := (s.globals |+ (3w,Word 1w)))).globals 3w``
