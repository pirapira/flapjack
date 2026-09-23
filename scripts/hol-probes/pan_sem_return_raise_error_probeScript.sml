(*
  Minimal source-execution probe for the original CakeML Pancake `Return` and
  `Raise` failure handling.  The probe observes the raw result directly, so the
  expected values are independent of the Lean evaluator:

  * `Return e` whose expression fails to evaluate yields `SOME Error` with the
    unchanged state (clock and locals preserved);
  * `Return e` whose payload shape exceeds the 32-word limit yields `SOME Error`
    with the unchanged state;
  * a well-sized `Return e` yields `SOME (Return v)` with cleared locals;
  * `Raise eid e` whose `eid` has no declared exception shape yields `SOME Error`
    with the unchanged state;
  * `Raise eid e` whose expression fails to evaluate yields `SOME Error` with
    the unchanged state;
  * `Raise eid e` whose payload shape does not match the declared shape, or
    whose size exceeds the limit, yields `SOME Error`;
  * a well-matched `Raise eid e` yields `SOME (Exception eid v)` with cleared
    locals.

  Reference: cakeml/pancake/semantics/panSemScript.sml:633-650.
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
  sh_memaddrs := {};
  structs := [];
  eshapes := FEMPTY |>)``;

val raiseState = ``(^baseState with
  eshapes := FEMPTY |+ (strlit "E", panLang$One))``;

val raiseOversizedState = ``(^baseState with
  eshapes := FEMPTY |+
    (strlit "E", panLang$Comb (REPLICATE 33 panLang$One)))``;

val _ = print_eval "ret_eval_fail_result"
  ``FST (panSem$evaluate
      (panLang$Return (panLang$Var panLang$Local (strlit "z")), ^baseState))``;
val _ = print_eval "ret_eval_fail_clock"
  ``(SND (panSem$evaluate
      (panLang$Return (panLang$Var panLang$Local (strlit "z")), ^baseState))).clock``;
val _ = print_eval "ret_eval_fail_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Return (panLang$Var panLang$Local (strlit "z")), ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "ret_oversized_result"
  ``FST (panSem$evaluate
      (panLang$Return (panLang$RStruct (REPLICATE 33 (panLang$Const (0w:8 word)))),
        ^baseState))``;
val _ = print_eval "ret_oversized_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Return (panLang$RStruct (REPLICATE 33 (panLang$Const (0w:8 word)))),
        ^baseState))).locals (strlit "x")``;
val _ = print_eval "ret_ok_result"
  ``FST (panSem$evaluate
      (panLang$Return (panLang$Const (7w:8 word)), ^baseState))``;
val _ = print_eval "ret_ok_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Return (panLang$Const (7w:8 word)), ^baseState))).locals
      (strlit "x")``;

val _ = print_eval "raise_missing_shape_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E") (panLang$Const (7w:8 word)), ^baseState))``;
val _ = print_eval "raise_missing_shape_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Raise (strlit "E") (panLang$Const (7w:8 word)), ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "raise_eval_fail_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E") (panLang$Var panLang$Local (strlit "z")),
        ^raiseState))``;
val _ = print_eval "raise_eval_fail_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Raise (strlit "E") (panLang$Var panLang$Local (strlit "z")),
        ^raiseState))).locals (strlit "x")``;
val _ = print_eval "raise_oversized_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$RStruct (REPLICATE 33 (panLang$Const (0w:8 word)))),
        ^raiseOversizedState))``;
val _ = print_eval "raise_shape_mismatch_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$RStruct [panLang$Const (7w:8 word)]), ^raiseState))``;
val _ = print_eval "raise_ok_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E") (panLang$Const (7w:8 word)), ^raiseState))``;
val _ = print_eval "raise_ok_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Raise (strlit "E") (panLang$Const (7w:8 word)), ^raiseState))).locals
      (strlit "x")``;