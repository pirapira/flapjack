(*
  Minimal source-execution probe for the original CakeML Pancake `Call` error
  path where the argument list does not match the callee's parameter shapes.
  HOL `lookup_code` (panSemScript.sml:458-467) requires the parameter names to
  be distinct and each argument's `shape_of` to equal the declared shape; a
  mismatch rejects the call with `(SOME Error, s)` and the unchanged caller
  state.  A matching argument list is included as the control case.

  Reference: cakeml/pancake/semantics/panSemScript.sml:458-467, 657-662.
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

val paramCode = ``FEMPTY |+ (strlit "f",
  ([(strlit "p", panLang$One)] : (mlstring # panLang$shape) list,
   panLang$Return (panLang$Const (0w:8 word)), panLang$One))``;

val paramState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  code := ^paramCode |>) : (8,'ffi) panSem$state``;

val _ = print_eval "call_arity_miss_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [], ^paramState))``;
val _ = print_eval "call_arity_miss_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [], ^paramState))).locals (strlit "x")``;
val _ = print_eval "call_arity_miss_clock"
  ``(SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [], ^paramState))).clock``;
val _ = print_eval "call_arity_ok_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)], ^paramState))``;
val _ = print_eval "call_arity_shape_miss_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$RStruct []], ^paramState))``;
