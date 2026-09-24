(*
  Direct HOL observations for the original Pancake evaluator's Break and
  Continue clauses. Both return their result with the source state unchanged.
  Reference: cakeml/pancake/semantics/panSemScript.sml:590-591.
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

val _ = print_eval "break_result"
  ``FST (panSem$evaluate (panLang$Break, (^s with clock := 5)))``;
val _ = print_eval "break_clock"
  ``(SND (panSem$evaluate (panLang$Break, (^s with clock := 5)))).clock``;
val _ = print_eval "break_locals_preserved"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Break, (^s with <| clock := 5;
        locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word)) |>)))).locals
      (strlit "x")``;

val _ = print_eval "continue_result"
  ``FST (panSem$evaluate (panLang$Continue, (^s with clock := 5)))``;
val _ = print_eval "continue_clock"
  ``(SND (panSem$evaluate (panLang$Continue, (^s with clock := 5)))).clock``;
val _ = print_eval "continue_locals_preserved"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Continue, (^s with <| clock := 5;
        locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word)) |>)))).locals
      (strlit "x")``;
