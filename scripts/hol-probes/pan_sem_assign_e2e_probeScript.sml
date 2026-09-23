(*
  Minimal source-execution probe for the original CakeML Pancake `Assign`
  equation.  The probe observes the result, clock, and locals directly, so the
  expected result is independent of the Lean evaluator:

  * an assignment whose source evaluates and whose destination is already bound
    with the same shape succeeds (`NONE`), preserves the clock, and writes the
    value;
  * an assignment to a fresh, unbound destination is rejected (`SOME Error`);
  * an assignment whose source expression does not evaluate is rejected.

  Reference: cakeml/pancake/semantics/panSemScript.sml:566-572 (`Assign`).
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

val _ = print_eval "assign_local_ok_result"
  ``FST (panSem$evaluate
      (panLang$Assign Local (strlit "x") (panLang$Const (7w:8 word)),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))``;
val _ = print_eval "assign_local_ok_clock"
  ``(SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") (panLang$Const (7w:8 word)),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).clock``;
val _ = print_eval "assign_local_ok_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") (panLang$Const (7w:8 word)),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).locals
      (strlit "x")``;
val _ = print_eval "assign_local_ok_other"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") (panLang$Const (7w:8 word)),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).locals
      (strlit "y")``;
val _ = print_eval "assign_fresh_invalid_result"
  ``FST (panSem$evaluate
      (panLang$Assign Local (strlit "y") (panLang$Const (7w:8 word)),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))``;
val _ = print_eval "assign_eval_missing_result"
  ``FST (panSem$evaluate
      (panLang$Assign Local (strlit "x") (panLang$Var Local (strlit "z")),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))``;
val _ = print_eval "assign_fresh_invalid_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Assign Local (strlit "y") (panLang$Const (7w:8 word)),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).locals
      (strlit "x")``;
val _ = print_eval "assign_fresh_invalid_clock"
  ``(SND (panSem$evaluate
      (panLang$Assign Local (strlit "y") (panLang$Const (7w:8 word)),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).clock``;
val _ = print_eval "assign_eval_missing_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") (panLang$Var Local (strlit "z")),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).locals
      (strlit "x")``;
val _ = print_eval "assign_eval_missing_clock"
  ``(SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") (panLang$Var Local (strlit "z")),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).clock``;
