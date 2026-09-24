(*
  Minimal source-execution probe for the original CakeML Pancake `Call` error
  paths where the callee finishes with `Break` or `Continue`.  HOL
  `evaluate (Call ...)` maps `(SOME Break,st) => (SOME Error,st)` and
  `(SOME Continue,st) => (SOME Error,st)` (panSemScript.sml:669-670),
  preserving the callee's post-call locals (the bound parameters) and the
  decremented clock.

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

val breakCode = ``FEMPTY |+ (strlit "f",
  ([(strlit "p", panLang$One)] : (mlstring # panLang$shape) list,
   panLang$If (panLang$Const (1w:8 word)) panLang$Break panLang$Skip,
   panLang$One))``;

val continueCode = ``FEMPTY |+ (strlit "f",
  ([(strlit "p", panLang$One)] : (mlstring # panLang$shape) list,
   panLang$If (panLang$Const (1w:8 word)) panLang$Continue panLang$Skip,
   panLang$One))``;

val breakState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  code := ^breakCode |>) : (8,'ffi) panSem$state``;

val continueState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  code := ^continueCode |>) : (8,'ffi) panSem$state``;

val _ = print_eval "call_break_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)], ^breakState))``;
val _ = print_eval "call_break_param_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^breakState))).locals (strlit "p")``;
val _ = print_eval "call_break_caller_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^breakState))).locals (strlit "x")``;
val _ = print_eval "call_break_clock"
  ``(SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^breakState))).clock``;

val _ = print_eval "call_continue_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)], ^continueState))``;
val _ = print_eval "call_continue_param_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^continueState))).locals (strlit "p")``;
val _ = print_eval "call_continue_clock"
  ``(SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^continueState))).clock``;
