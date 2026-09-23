(*
  Minimal source-execution probe for the original CakeML Pancake `DecCall`
  equation.  The probe observes result, clock, and locals directly, so the
  expected result is independent of the Lean evaluator:

  * a `DecCall` whose callee returns a value of the declared shape runs the
    continuation and restores the declared local;
  * a `DecCall` whose callee returns a value of the wrong shape is rejected
    (`SOME Error`);
  * a `DecCall` whose callee body itself fails is rejected (`SOME Error`);
  * a `DecCall` naming an unknown function is rejected (`SOME Error`).

  Reference: cakeml/pancake/semantics/panSemScript.sml:694-713.
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

val okCode = ``FEMPTY |+ (strlit "f",
  ([] : (mlstring # panLang$shape) list,
   panLang$Return (panLang$Const (7w:8 word)),
   panLang$One))``;

val errCode = ``FEMPTY |+ (strlit "f",
  ([] : (mlstring # panLang$shape) list,
   panLang$Assign Local (strlit "q") (panLang$Const (7w:8 word)),
   panLang$One))``;

val baseState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {};
  sh_memaddrs := {};
  code := ^okCode |>)``;

val errState = ``(^baseState with code := ^errCode)``;

val _ = print_eval "deccall_ok_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "f") []
        panLang$Skip, ^baseState))``;
val _ = print_eval "deccall_ok_clock"
  ``(SND (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "f") []
        panLang$Skip, ^baseState))).clock``;
val _ = print_eval "deccall_ok_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "f") []
        panLang$Skip, ^baseState))).locals (strlit "x")``;
val _ = print_eval "deccall_shape_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") (panLang$Named (strlit "Other"))
        (strlit "f") [] panLang$Skip, ^baseState))``;
val _ = print_eval "deccall_error_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "f") []
        panLang$Skip, ^errState))``;
val _ = print_eval "deccall_missing_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "g") []
        panLang$Skip, ^baseState))``;