(*
  Direct HOL oracle for CakeML Pancake `Primitive` rejection branches that the
  existing `pan_sem_primitive_e2e_probe` does not exercise: a `pan_primop`
  failure (wrong argument count) and a destination whose shape does not match
  the primitive result.  Both yield `SOME Error` with the unchanged state.

  Reference: cakeml/pancake/semantics/panSemScript.sml:573-582.
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

val wordState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (1w:8 word)) |>)``;

val wrongArityProgram = ``panLang$Primitive (strlit "x") AddCarry
  [panLang$Const (1w:8 word)]``;

val shapeMismatchProgram = ``panLang$Primitive (strlit "x") AddCarry
  [panLang$Const (1w:8 word); panLang$Const (2w:8 word); panLang$Const (0w:8 word)]``;

val _ = print_eval "prim_wrong_arity_result"
  ``FST (panSem$evaluate (^wrongArityProgram, ^okState))``;
val _ = print_eval "prim_wrong_arity_locals"
  ``FLOOKUP (SND (panSem$evaluate (^wrongArityProgram, ^okState))).locals (strlit "x")``;
val _ = print_eval "prim_wrong_arity_clock"
  ``(SND (panSem$evaluate (^wrongArityProgram, ^okState))).clock``;
val _ = print_eval "prim_shape_mismatch_result"
  ``FST (panSem$evaluate (^shapeMismatchProgram, ^wordState))``;
val _ = print_eval "prim_shape_mismatch_locals"
  ``FLOOKUP (SND (panSem$evaluate (^shapeMismatchProgram, ^wordState))).locals (strlit "x")``;
val _ = print_eval "prim_shape_mismatch_clock"
  ``(SND (panSem$evaluate (^shapeMismatchProgram, ^wordState))).clock``