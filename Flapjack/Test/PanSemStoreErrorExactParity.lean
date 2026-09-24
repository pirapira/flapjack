import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Exact-source PanSem `Store` Error parity

The original HOL `panSemScript$evaluate_def` `Store` case returns `SOME Error`
with the unchanged state when the address expression fails to evaluate, when
the stored-value expression fails to evaluate, or when the word store fails
(for example when the address is outside the store's domain).  This module
checks the corresponding untagged exact-state equations in
`Flapjack.Pancake.Semantics.PanSem` against the direct HOL oracle
`scripts/hol-probes/pan_sem_store_error_probe.out` for both the clocked and the
non-clocked evaluators.
-/

namespace Flapjack.Test.PanSemStoreErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain (address : Word64) : Bool := address == 8

/-- A memory access whose store never succeeds: the domain is empty. -/
private def emptyAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel (fun _ => false) (fun _ => false) false

private def exactMemory : Word64 → Option (PanValue Word64) := fun _ => some (.word 0)

private def exactLegacy (locals : VarName → Option (PanValue Word64)) :
    PanSemEvaluateState Word64 Unit :=
  { structs := []
    functions := []
    locals := locals
    globals := fun _ => none
    memory := exactMemory
    ffi := statefulTestFfiState
    clock := 5
    baseAddress := 0
    topAddress := 100
    bytesInWord := BitVec.ofNat 64 8 }

private def exactStateWith (access : PanValueMemoryAccess Word64)
    (locals : VarName → Option (PanValue Word64)) : PanSemExactState Word64 Unit :=
  { legacy := exactLegacy locals, memoryAccess := access }

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

private def evaluate (state : PanSemExactState Word64 Unit) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateExactState statefulTestContext statefulTestPrimitive statefulTestHandler
    state program

private def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [] 0 100 (BitVec.ofNat 64 8) 5 localsWordX (fun _ => none) exactMemory
    statefulTestFfiState program (memoryAccess := memoryAccess)

private def isWordOption (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

/-- Matches an `Error` control result at `clock` whose `x` local is unchanged. -/
private def isErrorKeepingX (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control (.error locals globals _ _), n) =>
      n == clock && isWordOption value (locals "x") && (globals "g").isNone
  | _ => false

private def isErrorKeepingXStepped (value : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals globals _ _, _) =>
      isWordOption value (locals "x") && (globals "g").isNone
  | _ => false

private def storeAddressFailProgram : Prog Word64 :=
  .store (.var .local "z") (.const 7)

private def storeValueFailProgram : Prog Word64 :=
  .store (.const 0) (.var .local "z")

private def storeDomainFailProgram : Prog Word64 :=
  .store (.const 0) (.const 7)

private def storeKeywordState : PanSemExactState Word64 Unit :=
  exactStateWith (panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain
    (fun _ => false) false) localsWordX

private def storeAddressFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate storeKeywordState storeAddressFailProgram)

private def storeValueFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate storeKeywordState storeValueFailProgram)

private def storeDomainFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactStateWith emptyAccess localsWordX) storeDomainFailProgram)

private def storeNonClockedAddressFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate storeAddressFailProgram
    (memoryAccess := some (panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain
      (fun _ => false) false)))

private def storeNonClockedDomainFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate storeDomainFailProgram
    (memoryAccess := some emptyAccess))

private def storeErrorGuard : Bool :=
  storeAddressFailGuard && storeValueFailGuard && storeDomainFailGuard &&
    storeNonClockedAddressFailGuard && storeNonClockedDomainFailGuard

#guard storeErrorGuard

example :
    panSemEvaluateExactState statefulTestContext statefulTestPrimitive statefulTestHandler
        (exactStateWith (panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain
          (fun _ => false) false) localsWordX) (.store (.var .local "z") (.const 7)) =
      some (.control (.error (exactLegacy localsWordX).locals
        (exactLegacy localsWordX).globals (exactLegacy localsWordX).memory
        (exactLegacy localsWordX).ffi), (exactLegacy localsWordX).clock) :=
  panSemEvaluateExactState_store_error_of_address_none statefulTestContext
    statefulTestPrimitive statefulTestHandler _ _ _ (by simp [exactStateWith, exactLegacy, localsWordX, evalPanValueExp])

def runChecks : IO Bool := do
  if storeAddressFailGuard then
    IO.println "PASS exact-state Store failing address keeps state and clock"
  else
    IO.println "FAIL exact-state Store failing address keeps state and clock"
  if storeValueFailGuard then
    IO.println "PASS exact-state Store failing value keeps state and clock"
  else
    IO.println "FAIL exact-state Store failing value keeps state and clock"
  if storeDomainFailGuard then
    IO.println "PASS exact-state Store domain failure keeps state and clock"
  else
    IO.println "FAIL exact-state Store domain failure keeps state and clock"
  if storeNonClockedAddressFailGuard then
    IO.println "PASS non-clocked Store failing address rejected with Error"
  else
    IO.println "FAIL non-clocked Store failing address rejected with Error"
  if storeNonClockedDomainFailGuard then
    IO.println "PASS non-clocked Store domain failure rejected with Error"
  else
    IO.println "FAIL non-clocked Store domain failure rejected with Error"
  pure storeErrorGuard

end Flapjack.Test.PanSemStoreErrorExactParity