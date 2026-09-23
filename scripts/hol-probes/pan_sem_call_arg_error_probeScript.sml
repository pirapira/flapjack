(*
  Minimal source-execution probe for failed `DecCall` argument evaluation in
  the original CakeML Pancake semantics.  HOL evaluates the argument list with
  `OPT_MMAP (eval s) argexps` before looking up the callee, so a failing
  argument rejects the call with `SOME Error` and the unchanged state.

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

val baseState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {};
  sh_memaddrs := {};
  code := ^okCode |>)``;

val _ = print_eval "call_arg_fail_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "f")
        [panLang$Var Local (strlit "z")] panLang$Skip, ^baseState))``;
val _ = print_eval "call_arg_fail_clock"
  ``(SND (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "f")
        [panLang$Var Local (strlit "z")] panLang$Skip, ^baseState))).clock``;
val _ = print_eval "call_arg_fail_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "f")
        [panLang$Var Local (strlit "z")] panLang$Skip, ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "call_arg_fail_missing_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "g")
        [panLang$Var Local (strlit "z")] panLang$Skip, ^baseState))``;