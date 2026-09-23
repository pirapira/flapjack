(*
  Minimal source-execution probe for the original CakeML Pancake `Skip`
  equation.  The probe observes the result, clock, and locals directly, so the
  expected result is independent of the Lean evaluator: `Skip` yields the
  normal (NONE) result with the whole state, including the clock and locals,
  carried verbatim.

  Reference: cakeml/pancake/semantics/panSemScript.sml:557 (`Skip`).
*)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val s = ``(s:(8,'ffi) panSem$state)``;

val _ = print_eval "skip_result"
  ``FST (panSem$evaluate (panLang$Skip, (^s with clock := 5)))``;
val _ = print_eval "skip_clock"
  ``(SND (panSem$evaluate (panLang$Skip, (^s with clock := 5)))).clock``;
val _ = print_eval "skip_locals_preserved"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Skip, (^s with <| clock := 5;
        locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word)) |>)))).locals
      (strlit "x")``;
