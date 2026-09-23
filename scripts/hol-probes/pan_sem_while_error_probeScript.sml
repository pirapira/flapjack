(*
  Minimal source-execution probe for the original CakeML Pancake `While`
  equation.  The probe observes result, clock, and locals directly, so the
  expected result is independent of the Lean evaluator:

  * a `While` whose condition evaluates to a non-word (unbound local) is
    rejected (`SOME Error`) leaving the state unchanged;
  * a `While` whose condition is zero completes normally at the same clock;
  * a `While` whose condition stays nonzero runs the body until the clock is
    exhausted, ending in `SOME TimeOut` with cleared locals;
  * a `While` whose body clears the condition exits normally after one
    iteration, decrementing the clock once.

  Reference: cakeml/pancake/semantics/panSemScript.sml:630-660.
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

val baseState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {};
  sh_memaddrs := {} |>)``;

val loopState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |+ (strlit "c", ValWord (1w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {};
  sh_memaddrs := {} |>)``;

val _ = print_eval "while_bad_result"
  ``FST (panSem$evaluate
      (panLang$While (panLang$Var Local (strlit "z")) panLang$Skip, ^baseState))``;
val _ = print_eval "while_bad_clock"
  ``(SND (panSem$evaluate
      (panLang$While (panLang$Var Local (strlit "z")) panLang$Skip, ^baseState))).clock``;
val _ = print_eval "while_bad_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$While (panLang$Var Local (strlit "z")) panLang$Skip, ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "while_zero_result"
  ``FST (panSem$evaluate
      (panLang$While (panLang$Const (0w:8 word)) panLang$Skip, ^baseState))``;
val _ = print_eval "while_zero_clock"
  ``(SND (panSem$evaluate
      (panLang$While (panLang$Const (0w:8 word)) panLang$Skip, ^baseState))).clock``;
val _ = print_eval "while_timeout_result"
  ``FST (panSem$evaluate
      (panLang$While (panLang$Const (1w:8 word)) panLang$Skip, ^baseState))``;
val _ = print_eval "while_timeout_clock"
  ``(SND (panSem$evaluate
      (panLang$While (panLang$Const (1w:8 word)) panLang$Skip, ^baseState))).clock``;
val _ = print_eval "while_one_iter_result"
  ``FST (panSem$evaluate
      (panLang$While (panLang$Var Local (strlit "c"))
        (panLang$Assign Local (strlit "c") (panLang$Const (0w:8 word))), ^loopState))``;
val _ = print_eval "while_one_iter_clock"
  ``(SND (panSem$evaluate
      (panLang$While (panLang$Var Local (strlit "c"))
        (panLang$Assign Local (strlit "c") (panLang$Const (0w:8 word))), ^loopState))).clock``;
val _ = print_eval "while_one_iter_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$While (panLang$Var Local (strlit "c"))
        (panLang$Assign Local (strlit "c") (panLang$Const (0w:8 word))), ^loopState))).locals
      (strlit "c")``;
