(*
  Minimal source-execution probe for the original CakeML Pancake `Call` error
  path where the callee returns a value whose shape does not match the declared
  return shape.  HOL `evaluate (Call ...)` compares `shape_of retv` with the
  function's `return_sh` (panSemScript.sml:668-670) and returns
  `(SOME Error, st)` with the callee post-call state (locals already cleared by
  the callee `Return`, clock at the decremented callee clock).

  Reference: cakeml/pancake/semantics/panSemScript.sml:657-693.
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

val invalidCode = ``FEMPTY |+ (strlit "f",
  ([(strlit "p", panLang$One)] : (mlstring # panLang$shape) list,
   panLang$Return (panLang$Const (0w:8 word)),
   panLang$Named (strlit "Other")))``;

val invalidState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  code := ^invalidCode |>) : (8,'ffi) panSem$state``;

val _ = print_eval "call_retinvalid_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^invalidState))``;
val _ = print_eval "call_retinvalid_param_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^invalidState))).locals (strlit "p")``;
val _ = print_eval "call_retinvalid_caller_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^invalidState))).locals (strlit "x")``;
val _ = print_eval "call_retinvalid_clock"
  ``(SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^invalidState))).clock``;
