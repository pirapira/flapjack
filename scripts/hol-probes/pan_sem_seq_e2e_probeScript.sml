(*
  Minimal source-execution probe for the original CakeML Pancake `Seq`
  equation.  The probe observes result, clock, and locals directly, so the
  expected result is independent of the Lean evaluator:

  * a `Seq` of two `Skip`s completes normally at the same clock with locals
    preserved;
  * a `Seq` whose first command is `Break`/`Continue` returns that outcome and
    does not run the second command;
  * a `Seq` whose first command is rejected (shape mismatch) returns
    `SOME Error`;
  * a `Seq` whose first command is `Tick` clamps the entry clock to the
    decremented clock (`fix_clock`) before running the second command.

  Reference: cakeml/pancake/semantics/panSemScript.sml:615-618.
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

val _ = print_eval "seq_normal_result"
  ``FST (panSem$evaluate
      (panLang$Seq panLang$Skip panLang$Skip, ^baseState))``;
val _ = print_eval "seq_normal_clock"
  ``(SND (panSem$evaluate
      (panLang$Seq panLang$Skip panLang$Skip, ^baseState))).clock``;
val _ = print_eval "seq_normal_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Seq panLang$Skip panLang$Skip, ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "seq_break_result"
  ``FST (panSem$evaluate
      (panLang$Seq panLang$Break
        (panLang$Assign Local (strlit "x") (panLang$Const (9w:8 word))), ^baseState))``;
val _ = print_eval "seq_break_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Seq panLang$Break
        (panLang$Assign Local (strlit "x") (panLang$Const (9w:8 word))), ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "seq_continue_result"
  ``FST (panSem$evaluate
      (panLang$Seq panLang$Continue panLang$Skip, ^baseState))``;
val _ = print_eval "seq_error_result"
  ``FST (panSem$evaluate
      (panLang$Seq
        (panLang$Dec (strlit "x") (panLang$Named (strlit "Other"))
          (panLang$Const (7w:8 word)) panLang$Skip)
        panLang$Skip, ^baseState))``;
val _ = print_eval "seq_error_clock"
  ``(SND (panSem$evaluate
      (panLang$Seq
        (panLang$Dec (strlit "x") (panLang$Named (strlit "Other"))
          (panLang$Const (7w:8 word)) panLang$Skip)
        panLang$Skip, ^baseState))).clock``;
val _ = print_eval "seq_tick_result"
  ``FST (panSem$evaluate
      (panLang$Seq panLang$Tick panLang$Skip, ^baseState))``;
val _ = print_eval "seq_tick_clock"
  ``(SND (panSem$evaluate
      (panLang$Seq panLang$Tick panLang$Skip, ^baseState))).clock``;
