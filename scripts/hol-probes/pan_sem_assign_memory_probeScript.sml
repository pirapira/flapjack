(*
  Direct source-execution probe for the CakeML Pancake `Assign` equation when
  the source expression reads source memory.  The probe observes the result and
  the destination local directly, so the expected values are independent of the
  Lean evaluator:

  * `Assign Local "x" (Load One (Const 8w))` over a present word cell writes the
    whole cell value;
  * the same assignment with an address outside `memaddrs` is rejected with
    `SOME Error` and the locals unchanged (the source-evaluation Error path);
  * `Assign Local "x" (LoadByte (Const 8w))` selects a different byte for the
    same cell under little-endian and big-endian `be`, so `be` drives the value.

  Reference: cakeml/pancake/semantics/panSemScript.sml:566-572 (`Assign`) and
  cakeml/pancake/semantics/panSemScript.sml:86-108 (mem_load/mem_load_byte).
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

val s = ``(s:(64,'ffi) panSem$state)``;

val stateNZ = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:64 word));
  globals := FEMPTY;
  memory := (\(a : 64 word). if a = 8w then Word (0x1122334455667788w:64 word) else Word (0w:64 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  be := F |>)``;

val stateBE = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:64 word));
  globals := FEMPTY;
  memory := (\(a : 64 word). if a = 8w then Word (0x8800000000000000w:64 word) else Word (0w:64 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  be := T |>)``;

val stateLE = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:64 word));
  globals := FEMPTY;
  memory := (\(a : 64 word). if a = 8w then Word (0x8800000000000000w:64 word) else Word (0w:64 word));
  memaddrs := {8w};
  sh_memaddrs := {};
  be := F |>)``;

val loadSource = ``panLang$Load panLang$One (panLang$Const (8w:64 word))``;
val loadMissSource = ``panLang$Load panLang$One (panLang$Const (9w:64 word))``;
val byteSource = ``panLang$LoadByte (panLang$Const (8w:64 word))``;

val _ = print_eval "assign_mem_load_result"
  ``FST (panSem$evaluate
      (panLang$Assign Local (strlit "x") ^loadSource, ^stateNZ))``;
val _ = print_eval "assign_mem_load_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") ^loadSource, ^stateNZ))).locals (strlit "x")``;
val _ = print_eval "assign_mem_domain_result"
  ``FST (panSem$evaluate
      (panLang$Assign Local (strlit "x") ^loadMissSource, ^stateNZ))``;
val _ = print_eval "assign_mem_domain_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") ^loadMissSource, ^stateNZ))).locals (strlit "x")``;
val _ = print_eval "assign_mem_domain_clock"
  ``(SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") ^loadMissSource, ^stateNZ))).clock``;
val _ = print_eval "assign_mem_byte_le_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") ^byteSource, ^stateLE))).locals (strlit "x")``;
val _ = print_eval "assign_mem_byte_be_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Assign Local (strlit "x") ^byteSource, ^stateBE))).locals (strlit "x")``;
