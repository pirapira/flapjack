(*
  Minimal source-execution probe for the original CakeML Pancake Store,
  Store32, StoreByte, ShMemLoad, ShMemStore, and If equations.  The probe
  observes result, clock, and locals directly, so the expected result is
  independent of the Lean evaluator:

  * a successful store (Store32 into a mapped address) runs to completion;
  * a store whose address is not mapped is rejected (`SOME Error`), leaving the
    state unchanged;
  * a ShMemLoad whose source local is unbound is rejected;
  * a ShMemLoad whose address is not in the shared domain is rejected;
  * a ShMemStore whose address is not in the shared domain is rejected;
  * an If with a non-word (unbound) condition is rejected;
  * an If with a word condition selects a branch and completes.

  Reference: cakeml/pancake/semantics/panSemScript.sml:583-620.
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

val errorState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {};
  sh_memaddrs := {} |>)``;

val okState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {(0w:8 word)};
  sh_memaddrs := {} |>)``;

val _ = print_eval "if_ok_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) panLang$Skip panLang$Skip, ^errorState))``;
val _ = print_eval "if_ok_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) panLang$Skip panLang$Skip, ^errorState))).clock``;
val _ = print_eval "if_bad_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "z")) panLang$Skip panLang$Skip, ^errorState))``;
val _ = print_eval "if_bad_clock"
  ``(SND (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "z")) panLang$Skip panLang$Skip, ^errorState))).clock``;
val _ = print_eval "if_bad_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$Var Local (strlit "z")) panLang$Skip panLang$Skip, ^errorState))).locals
      (strlit "x")``;
val _ = print_eval "store_domain_result"
  ``FST (panSem$evaluate
      (panLang$Store (panLang$Const (0w:8 word)) (panLang$Const (7w:8 word)), ^errorState))``;
val _ = print_eval "store_domain_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Store (panLang$Const (0w:8 word)) (panLang$Const (7w:8 word)), ^errorState))).locals
      (strlit "x")``;
val _ = print_eval "store32_domain_result"
  ``FST (panSem$evaluate
      (panLang$Store32 (panLang$Const (0w:8 word)) (panLang$Const (7w:8 word)), ^errorState))``;
val _ = print_eval "storebyte_domain_result"
  ``FST (panSem$evaluate
      (panLang$StoreByte (panLang$Const (0w:8 word)) (panLang$Const (7w:8 word)), ^errorState))``;
val _ = print_eval "store32_ok_result"
  ``FST (panSem$evaluate
      (panLang$Store32 (panLang$Const (0w:8 word)) (panLang$Const (7w:8 word)), ^okState))``;
val _ = print_eval "store32_ok_clock"
  ``(SND (panSem$evaluate
      (panLang$Store32 (panLang$Const (0w:8 word)) (panLang$Const (7w:8 word)), ^okState))).clock``;
val _ = print_eval "shmemload_unbound_result"
  ``FST (panSem$evaluate
      (panLang$ShMemLoad Op8 Local (strlit "z") (panLang$Const (0w:8 word)), ^errorState))``;
val _ = print_eval "shmemload_domain_result"
  ``FST (panSem$evaluate
      (panLang$ShMemLoad Op8 Local (strlit "x") (panLang$Const (0w:8 word)), ^errorState))``;
val _ = print_eval "shmemstore_domain_result"
  ``FST (panSem$evaluate
      (panLang$ShMemStore Op8 (panLang$Const (0w:8 word)) (panLang$Const (7w:8 word)), ^errorState))``;