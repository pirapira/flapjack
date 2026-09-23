(*
  Minimal source-execution probe for the original CakeML Pancake `Dec`
  equation.  The probe observes the result, clock, and locals directly, so the
  expected result is independent of the Lean evaluator:

  * a declaration whose initialiser evaluates to the declared shape runs the
    body (`NONE`, clock preserved) and then restores the declared variable to
    its previous binding, so a body assignment to the same variable does not
    leak out;
  * a declaration whose shape does not match the initialiser value is rejected
    (`SOME Error`);
  * a declaration whose initialiser expression does not evaluate is rejected.

  Reference: cakeml/pancake/semantics/panSemScript.sml:558-565 (`Dec`).
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

val _ = print_eval "dec_ok_result"
  ``FST (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (7w:8 word))
        (panLang$Assign Local (strlit "x") (panLang$Const (7w:8 word))),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))``;
val _ = print_eval "dec_ok_clock"
  ``(SND (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (7w:8 word))
        (panLang$Assign Local (strlit "x") (panLang$Const (7w:8 word))),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).clock``;
val _ = print_eval "dec_ok_locals_restored"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (7w:8 word))
        (panLang$Assign Local (strlit "x") (panLang$Const (7w:8 word))),
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).locals
      (strlit "x")``;
val _ = print_eval "dec_shape_mismatch_result"
  ``FST (panSem$evaluate
      (panLang$Dec (strlit "x") (panLang$Named (strlit "Other"))
        (panLang$Const (7w:8 word)) panLang$Skip,
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))``;
val _ = print_eval "dec_eval_missing_result"
  ``FST (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Var Local (strlit "z"))
        panLang$Skip,
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))``;
val _ = print_eval "dec_shape_mismatch_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Dec (strlit "x") (panLang$Named (strlit "Other"))
        (panLang$Const (7w:8 word)) panLang$Skip,
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).locals
      (strlit "x")``;
val _ = print_eval "dec_shape_mismatch_clock"
  ``(SND (panSem$evaluate
      (panLang$Dec (strlit "x") (panLang$Named (strlit "Other"))
        (panLang$Const (7w:8 word)) panLang$Skip,
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).clock``;
val _ = print_eval "dec_eval_missing_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Var Local (strlit "z"))
        panLang$Skip,
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).locals
      (strlit "x")``;
val _ = print_eval "dec_eval_missing_clock"
  ``(SND (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Var Local (strlit "z"))
        panLang$Skip,
        (^s with <| clock := 5;
          locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)))).clock``;
