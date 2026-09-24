(*
  Direct source-execution probe for the CakeML Pancake `If` equation when the
  condition itself reads source memory.  The probe observes result and locals
  directly, so the expected result is independent of the Lean evaluator:

  * a `Load` condition over a present, nonzero word cell selects the then
    branch;
  * a `Load` condition over a present, zero word cell selects the else branch;
  * a `Load` condition whose address is outside `memaddrs` is rejected with
    `SOME Error` and the state unchanged;
  * a `LoadByte` condition differs between little-endian and big-endian
    interpretations of the same cell (`be` drives the byte selected).

  Reference: cakeml/pancake/semantics/panSemScript.sml:617-620 and
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

val stateZ = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:64 word));
  globals := FEMPTY;
  memory := (\(a : 64 word). Word (0w:64 word));
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

val thenAssign = ``panLang$Assign Local (strlit "x") (panLang$Const (9w:64 word))``;
val elseAssign = ``panLang$Assign Local (strlit "x") (panLang$Const (0w:64 word))``;

val loadCond = ``panLang$Load panLang$One (panLang$Const (8w:64 word))``;
val loadMissCond = ``panLang$Load panLang$One (panLang$Const (9w:64 word))``;
val byteCond = ``panLang$LoadByte (panLang$Const (8w:64 word))``;

val _ = print_eval "if_mem_nonzero_result"
  ``FST (panSem$evaluate
      (panLang$If ^loadCond ^thenAssign ^elseAssign, ^stateNZ))``;
val _ = print_eval "if_mem_nonzero_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If ^loadCond ^thenAssign ^elseAssign, ^stateNZ))).locals (strlit "x")``;
val _ = print_eval "if_mem_zero_result"
  ``FST (panSem$evaluate
      (panLang$If ^loadCond ^thenAssign ^elseAssign, ^stateZ))``;
val _ = print_eval "if_mem_zero_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If ^loadCond ^thenAssign ^elseAssign, ^stateZ))).locals (strlit "x")``;
val _ = print_eval "if_mem_domain_fail_result"
  ``FST (panSem$evaluate
      (panLang$If ^loadMissCond ^thenAssign ^elseAssign, ^stateNZ))``;
val _ = print_eval "if_mem_domain_fail_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If ^loadMissCond ^thenAssign ^elseAssign, ^stateNZ))).locals (strlit "x")``;
val _ = print_eval "if_mem_byte_le_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If ^byteCond ^thenAssign ^elseAssign, ^stateLE))).locals (strlit "x")``;
val _ = print_eval "if_mem_byte_be_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If ^byteCond ^thenAssign ^elseAssign, ^stateBE))).locals (strlit "x")``;
