(*
  Minimal source-execution probe for the original CakeML Pancake `Call` error
  path where the argument evaluation fails.  HOL evaluates the argument list
  with `OPT_MMAP (eval s) argexps` through the source state's `memaddrs`, so a
  `Load` of an address outside `memaddrs` rejects the call with `SOME Error`
  and the unchanged state.  A call naming an unknown function is likewise
  rejected.

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

val okCode = ``FEMPTY |+ (strlit "f",
  ([] : (mlstring # panLang$shape) list,
   panLang$Return (panLang$Const (0w:8 word)), panLang$One))``;

val domainState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  code := ^okCode |>) : (8,'ffi) panSem$state``;

val emptyDomainState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {};
  sh_memaddrs := {};
  code := ^okCode |>) : (8,'ffi) panSem$state``;

val _ = print_eval "call_error_load_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Load panLang$One (panLang$Const (11w:8 word))],
        ^domainState))``;
val _ = print_eval "call_error_load_clock"
  ``(SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Load panLang$One (panLang$Const (11w:8 word))],
        ^domainState))).clock``;
val _ = print_eval "call_error_load_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Load panLang$One (panLang$Const (11w:8 word))],
        ^domainState))).locals (strlit "x")``;
val _ = print_eval "call_error_domain_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Load panLang$One (panLang$Const (8w:8 word))],
        ^emptyDomainState))``;
val _ = print_eval "call_error_domain_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "f") [panLang$Load panLang$One (panLang$Const (8w:8 word))],
        ^emptyDomainState))).locals (strlit "x")``;
val _ = print_eval "call_error_missing_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "g") [panLang$Const (1w:8 word)],
        ^domainState))``;
val _ = print_eval "call_error_missing_clock"
  ``(SND (panSem$evaluate
      (panLang$Call NONE (strlit "g") [panLang$Const (1w:8 word)],
        ^domainState))).clock``;
