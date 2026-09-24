(*
  Minimal source-execution probe for the original CakeML Pancake `Call` error
  path where the callee itself finishes with an error.  HOL
  `evaluate (Call ...)` maps the catch-all `(res,st) => (res,empty_locals st)`
  (panSemScript.sml:689) so a callee `SOME Error` becomes
  `(SOME Error, empty_locals st)`: the caller-visible locals are cleared while
  the clock keeps the decremented callee clock.

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

val errorCode = ``FEMPTY |+ (strlit "f",
  ([(strlit "p", panLang$One)] : (mlstring # panLang$shape) list,
   panLang$Assign panLang$Local (strlit "p")
     (panLang$Load panLang$One (panLang$Const (11w:8 word))),
   panLang$One))``;

val errorState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  code := ^errorCode |>) : (8,'ffi) panSem$state``;

val _ = print_eval "call_error_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)], ^errorState))``;
val _ = print_eval "call_error_param_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^errorState))).locals (strlit "p")``;
val _ = print_eval "call_error_caller_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^errorState))).locals (strlit "x")``;
val _ = print_eval "call_error_clock"
  ``(SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Const (1w:8 word)],
       ^errorState))).clock``;
