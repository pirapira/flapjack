(*
  Minimal source-execution probe for the original CakeML Pancake `If`
  equation.  The probe observes result, clock, and locals directly, so the
  expected result is independent of the Lean evaluator:

  * a nonzero word condition runs the then branch;
  * a zero word condition runs the else branch;
  * a non-word (unbound local) condition is rejected with `SOME Error` leaving
    the state unchanged;
  * a condition expression that itself fails to evaluate (a load from an empty
    memory domain) is rejected with `SOME Error` leaving the state unchanged.

  Reference: cakeml/pancake/semantics/panSemScript.sml:617-620.
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

val baseStateNonword = ``(^baseState with
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word))
            |+ (strlit "y", RStruct []))``;

val baseStateZero = ``(^baseState with
  locals := FEMPTY |+ (strlit "x", ValWord (0w:8 word)))``;

val thenAssign = ``panLang$Assign Local (strlit "x") (panLang$Const (9w:8 word))``;

val _ = print_eval "if_true_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) ^thenAssign panLang$Skip, ^baseState))``;
val _ = print_eval "if_true_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) ^thenAssign panLang$Skip, ^baseState))).clock``;
val _ = print_eval "if_true_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) ^thenAssign panLang$Skip, ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "if_false_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Const (0w:8 word)) ^thenAssign panLang$Skip, ^baseState))``;
val _ = print_eval "if_false_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Const (0w:8 word)) ^thenAssign panLang$Skip, ^baseState))).clock``;
val _ = print_eval "if_false_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$Const (0w:8 word)) ^thenAssign panLang$Skip, ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "if_nonword_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "z")) ^thenAssign panLang$Skip, ^baseState))``;
val _ = print_eval "if_nonword_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "z")) ^thenAssign panLang$Skip, ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "if_nonword_value_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "y")) ^thenAssign panLang$Skip,
        ^baseStateNonword))``;
val _ = print_eval "if_nonword_value_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "y")) ^thenAssign panLang$Skip,
        ^baseStateNonword))).locals (strlit "x")``;
val _ = print_eval "if_fail_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Load panLang$One (panLang$Const (0w:8 word))) ^thenAssign panLang$Skip,
        ^baseState))``;
val _ = print_eval "if_fail_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Load panLang$One (panLang$Const (0w:8 word))) ^thenAssign panLang$Skip,
        ^baseState))).clock``;
val _ = print_eval "if_fail_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$Load panLang$One (panLang$Const (0w:8 word))) ^thenAssign panLang$Skip,
        ^baseState))).locals
      (strlit "x")``;

(* Direct branch-selection rows for the total structural If fragment. *)
val _ = print_eval "if_const_true_tick_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) panLang$Tick panLang$Skip,
        ^baseState))).clock``;
val _ = print_eval "if_const_false_tick_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Const (0w:8 word)) panLang$Tick panLang$Skip,
        ^baseState))).clock``;
val _ = print_eval "if_local_true_tick_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "x")) panLang$Tick panLang$Skip,
        ^baseState))).clock``;
val _ = print_eval "if_local_zero_tick_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "x")) panLang$Tick panLang$Skip,
        ^baseStateZero))).clock``;
val _ = print_eval "if_op_add_true_tick_clock"
  ``(SND (panSem$evaluate
      (panLang$If
        (panLang$Op Add [panLang$Const (1w:8 word);
                         panLang$Const (2w:8 word)])
        panLang$Tick panLang$Skip, ^baseState))).clock``;
val _ = print_eval "if_op_sub_zero_tick_clock"
  ``(SND (panSem$evaluate
      (panLang$If
        (panLang$Op Sub [panLang$Const (3w:8 word);
                         panLang$Const (3w:8 word)])
        panLang$Tick panLang$Skip, ^baseState))).clock``;

(* Direct result/state rows consumed by the exact-state recursive If dispatcher. *)
val _ = print_eval "exact_if_nonzero_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) panLang$Tick panLang$Skip, ^baseState))``;
val _ = print_eval "exact_if_nonzero_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) panLang$Tick panLang$Skip, ^baseState))).clock``;
val _ = print_eval "exact_if_zero_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Const (0w:8 word)) panLang$Tick panLang$Skip, ^baseState))``;
val _ = print_eval "exact_if_zero_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Const (0w:8 word)) panLang$Tick panLang$Skip, ^baseState))).clock``;
val _ = print_eval "exact_if_nonword_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$RStruct []) ^thenAssign panLang$Skip, ^baseState))``;
val _ = print_eval "exact_if_nonword_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$RStruct []) ^thenAssign panLang$Skip, ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "exact_if_failed_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "z")) ^thenAssign panLang$Skip,
        ^baseState))``;
val _ = print_eval "exact_if_failed_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "z")) ^thenAssign panLang$Skip,
        ^baseState))).clock``;
val _ = print_eval "exact_if_failed_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "z")) ^thenAssign panLang$Skip,
        ^baseState))).locals (strlit "x")``;
