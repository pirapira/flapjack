(*
  Minimal source-execution probe for the original CakeML Pancake `Primitive`
  equation.  The probe observes the result, clock, and locals directly, so the
  expected result is independent of the Lean evaluator:

  * an `AddCarry` whose three arguments are words and whose destination local
    holds a matching struct shape updates that local with the primitive result
    (`NONE`, clock preserved);
  * a primitive whose destination local is unbound is rejected (`SOME Error`);
  * a primitive whose argument expression does not evaluate is rejected.

  Reference: cakeml/pancake/semantics/panSemScript.sml:573-582 (`Primitive`).
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

val okState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", RStruct [ValWord (0w:8 word); ValWord (0w:8 word)]) |>)``;

val okProgram = ``panLang$Primitive (strlit "x") AddCarry
  [panLang$Const (1w:8 word); panLang$Const (2w:8 word); panLang$Const (0w:8 word)]``;

val _ = print_eval "prim_ok_result"
  ``FST (panSem$evaluate (^okProgram, ^okState))``;
val _ = print_eval "prim_ok_clock"
  ``(SND (panSem$evaluate (^okProgram, ^okState))).clock``;
val _ = print_eval "prim_ok_locals"
  ``FLOOKUP (SND (panSem$evaluate (^okProgram, ^okState))).locals (strlit "x")``;
val _ = print_eval "prim_fresh_invalid_result"
  ``FST (panSem$evaluate
      (panLang$Primitive (strlit "y") AddCarry
        [panLang$Const (1w:8 word); panLang$Const (2w:8 word); panLang$Const (0w:8 word)],
        ^okState))``;
val _ = print_eval "prim_arg_missing_result"
  ``FST (panSem$evaluate
      (panLang$Primitive (strlit "x") AddCarry
        [panLang$Const (1w:8 word); panLang$Const (2w:8 word); panLang$Var Local (strlit "z")],
        ^okState))``;
