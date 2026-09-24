(*
  Minimal source-execution probe for the original CakeML Pancake `Call` error
  path where the callee falls through (its body terminates normally, i.e.
  `NONE`).  HOL `evaluate (Call ...)` maps `(NONE,st) => (SOME Error,st)`
  (panSemScript.sml:668), preserving the callee's post-call locals (the bound
  parameters) and the decremented clock.

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

val normalCode = ``FEMPTY |+ (strlit "f",
  ([(strlit "p", panLang$One)] : (mlstring # panLang$shape) list,
   panLang$If (panLang$Const (0w:8 word)) panLang$Skip panLang$Skip,
   panLang$One))``;

val normalState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  code := ^normalCode |>) : (8,'ffi) panSem$state``;

val _ = print_eval "call_normal_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)], ^normalState))``;
val _ = print_eval "call_normal_param_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^normalState))).locals (strlit "p")``;
val _ = print_eval "call_normal_caller_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^normalState))).locals (strlit "x")``;
val _ = print_eval "call_normal_clock"
  ``(SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^normalState))).clock``;
