import Flapjack.Pancake.Semantics.PanSem.StoreExact
import Flapjack.Test.PanValueFfiSemantics

/-! Direct parity for the exact panSem `Store`/`Store32`/`StoreByte` clause
    steps against the original-HOL rows in
    `scripts/hol-probes/pan_sem_e2e_probe.out`
    (`store_clause_hit`, `store_clause_out_of_domain`, `store32_clause_hit`,
    `storebyte_clause_hit`).  The clause steps are callback-parameterised
    (untagged); this module pins their behaviour. -/

namespace Flapjack.Test.PanSemStoreExactParity

open Flapjack
open Flapjack.Pancake.PanLang (ExpHOL)

private abbrev W := RiscV.Word 64

private abbrev zeroMemory : W → HolWordLab 64 := fun _ => .word 0

/-- `memaddrs` containing address `0` only. -/
private abbrev hitDomain : W → Prop := fun address => address = 0

/-- `memaddrs` empty. -/
private abbrev emptyDomain : W → Prop := fun _ => False

private abbrev hitState : PanSemStateExact 64 Unit :=
  { locals := fun _ => none, globals := fun _ => none, structs := []
    code := fun _ => none, eshapes := fun _ => none
    memory := zeroMemory, memaddrs := hitDomain, shMemaddrs := fun _ => False
    clock := 5, be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0, topAddr := 0 }

private abbrev emptyState : PanSemStateExact 64 Unit :=
  { hitState with memaddrs := emptyDomain }

private def evalExpressionFixture (_state : PanSemStateExact 64 Unit) :
    ExpHOL 64 → Option (ValueHOL 64)
  | .const value => some (.val (.word value))
  | _ => none

private def isNoneResult : Option (PanSemResultExact 64) → Bool
  | none => true
  | _ => false

private def isErrorResult : Option (PanSemResultExact 64) → Bool
  | some .error => true
  | _ => false

private def memoryWord? (memory : W → HolWordLab 64) (address : W) : Option Nat :=
  match memory address with
  | .word value => some value.toNat

private def storeHitGuard : Bool :=
  let result := storeStepHOLExact hitState
    (ExpHOL.const (0 : BitVec 64)) (ExpHOL.const (7 : BitVec 64)) evalExpressionFixture
  isNoneResult result.1 && (memoryWord? result.2.memory 0 == some 7)

private def storeOutOfDomainGuard : Bool :=
  let result := storeStepHOLExact emptyState
    (ExpHOL.const (0 : BitVec 64)) (ExpHOL.const (7 : BitVec 64)) evalExpressionFixture
  isErrorResult result.1 && (memoryWord? result.2.memory 0 == some 0)

private def store32HitGuard : Bool :=
  let result := store32StepHOLExact hitState
    (ExpHOL.const (0 : BitVec 64)) (ExpHOL.const (0x11223344 : BitVec 64))
    evalExpressionFixture
  isNoneResult result.1 && (memoryWord? result.2.memory 0 == some 0x11223344)

private def storeByteHitGuard : Bool :=
  let result := storeByteStepHOLExact hitState
    (ExpHOL.const (0 : BitVec 64)) (ExpHOL.const (0xAB : BitVec 64))
    evalExpressionFixture
  isNoneResult result.1 && (memoryWord? result.2.memory 0 == some 0xAB)

/-- All four direct-HOL rows. -/
def storeExactGuard : Bool :=
  storeHitGuard && storeOutOfDomainGuard && store32HitGuard && storeByteHitGuard

#guard storeHitGuard
#guard storeOutOfDomainGuard
#guard store32HitGuard
#guard storeByteHitGuard
#guard storeExactGuard

def runChecks : IO Bool := do
  if storeExactGuard then
    IO.println "PASS exact panSem Store/Store32/StoreByte clauses (4 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem Store/Store32/StoreByte clauses"
    pure false

end Flapjack.Test.PanSemStoreExactParity
