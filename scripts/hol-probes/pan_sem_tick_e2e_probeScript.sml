(*
  Minimal source-execution probe for the original CakeML Pancake `Tick`
  equation.  The probe observes both branches directly, so the expected result
  is independent of the Lean evaluator: at clock zero `Tick` yields
  `SOME TimeOut` with cleared locals; at positive clock it yields `NONE` with
  the clock decremented and locals preserved.

  Reference: cakeml/pancake/semantics/panSemScript.sml:653-655 (`Tick`),
  :441-443 (`dec_clock_def`), and `empty_locals_def`.
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

val _ = print_eval "tick_zero_result"
  ``FST (panSem$evaluate (panLang$Tick, (^s with clock := 0)))``;
val _ = print_eval "tick_zero_clock"
  ``(SND (panSem$evaluate (panLang$Tick, (^s with clock := 0)))).clock``;
val _ = print_eval "tick_zero_locals_cleared"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Tick, (^s with <| clock := 0;
        locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word)) |>)))).locals
      (strlit "x")``;
val _ = print_eval "tick_succ_result"
  ``FST (panSem$evaluate (panLang$Tick, (^s with clock := 5)))``;
val _ = print_eval "tick_succ_clock"
  ``(SND (panSem$evaluate (panLang$Tick, (^s with clock := 5)))).clock``;
val _ = print_eval "tick_succ_locals_preserved"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Tick, (^s with <| clock := 5;
        locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word)) |>)))).locals
      (strlit "x")``;
