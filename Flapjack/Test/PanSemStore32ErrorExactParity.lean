import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Exact-source PanSem `Store32`/`StoreByte` Error parity

The original HOL `panSemScript$evaluate_def` `Store32` and `StoreByte` cases
return `SOME Error` with the unchanged state when the address expression fails
to evaluate, when the stored-value expression fails to evaluate, or when the
sized store fails (for example when the aligned address is outside the store's
domain).  This module checks the corresponding untagged exact-state equations
in `Flapjack.Pancake.Semantics.PanSem` against the direct HOL oracle
`scripts/hol-probes/pan_sem_store_error_probe.out` for both the clocked and the
non-clocked evaluators.
-/

namespace Flapjack.Test.PanSemStore32ErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain (address : Word64) : Bool := address == 8

/-- A memory access whose store never succeeds: the domain is empty. -/
private def emptyAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel (fun _ => false) (fun _ => false) false

private def keywordAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain (fun _ => false) false

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

private def store32AddressFailProgram : Prog Word64 :=
  .store32 (.var .local "z") (.const 7)

private def store32ValueFailProgram : Prog Word64 :=
  .store32 (.const 0) (.var .local "z")

private def store32DomainFailProgram : Prog Word64 :=
  .store32 (.const 0) (.const 7)

private def storeByteAddressFailProgram : Prog Word64 :=
  .storeByte (.var .local "z") (.const 7)

private def storeByteValueFailProgram : Prog Word64 :=
  .storeByte (.const 0) (.var .local "z")

private def storeByteDomainFailProgram : Prog Word64 :=
  .storeByte (.const 0) (.const 7)

private def store32AddressFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactStateWith keywordAccess localsWordX)
    store32AddressFailProgram)

private def store32ValueFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactStateWith keywordAccess localsWordX)
    store32ValueFailProgram)

private def store32DomainFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactStateWith emptyAccess localsWordX)
    store32DomainFailProgram)

private def storeByteAddressFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactStateWith keywordAccess localsWordX)
    storeByteAddressFailProgram)

private def storeByteValueFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactStateWith keywordAccess localsWordX)
    storeByteValueFailProgram)

private def storeByteDomainFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactStateWith emptyAccess localsWordX)
    storeByteDomainFailProgram)

private def store32NonClockedAddressFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate store32AddressFailProgram
    (memoryAccess := some keywordAccess))

private def store32NonClockedDomainFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate store32DomainFailProgram
    (memoryAccess := some emptyAccess))

private def storeByteNonClockedAddressFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate storeByteAddressFailProgram
    (memoryAccess := some keywordAccess))

private def storeByteNonClockedDomainFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate storeByteDomainFailProgram
    (memoryAccess := some emptyAccess))

private def store32ErrorGuard : Bool :=
  store32AddressFailGuard && store32ValueFailGuard && store32DomainFailGuard &&
    storeByteAddressFailGuard && storeByteValueFailGuard && storeByteDomainFailGuard &&
    store32NonClockedAddressFailGuard && store32NonClockedDomainFailGuard &&
    storeByteNonClockedAddressFailGuard && storeByteNonClockedDomainFailGuard

#guard store32ErrorGuard

example :
    panSemEvaluateExactState statefulTestContext statefulTestPrimitive statefulTestHandler
        (exactStateWith keywordAccess localsWordX) (.store32 (.var .local "z") (.const 7)) =
      some (.control (.error (exactLegacy localsWordX).locals
        (exactLegacy localsWordX).globals (exactLegacy localsWordX).memory
        (exactLegacy localsWordX).ffi), (exactLegacy localsWordX).clock) :=
  panSemEvaluateExactState_store32_error_of_address_none statefulTestContext
    statefulTestPrimitive statefulTestHandler _ _ _
    (by simp [exactStateWith, exactLegacy, localsWordX, evalPanValueExp])

example :
    panSemEvaluateExactState statefulTestContext statefulTestPrimitive statefulTestHandler
        (exactStateWith keywordAccess localsWordX) (.storeByte (.var .local "z") (.const 7)) =
      some (.control (.error (exactLegacy localsWordX).locals
        (exactLegacy localsWordX).globals (exactLegacy localsWordX).memory
        (exactLegacy localsWordX).ffi), (exactLegacy localsWordX).clock) :=
  panSemEvaluateExactState_storeByte_error_of_address_none statefulTestContext
    statefulTestPrimitive statefulTestHandler _ _ _
    (by simp [exactStateWith, exactLegacy, localsWordX, evalPanValueExp])

def runChecks : IO Bool := do
  if store32AddressFailGuard then
    IO.println "PASS exact-state Store32 failing address keeps state and clock"
  else
    IO.println "FAIL exact-state Store32 failing address keeps state and clock"
  if store32ValueFailGuard then
    IO.println "PASS exact-state Store32 failing value keeps state and clock"
  else
    IO.println "FAIL exact-state Store32 failing value keeps state and clock"
  if store32DomainFailGuard then
    IO.println "PASS exact-state Store32 domain failure keeps state and clock"
  else
    IO.println "FAIL exact-state Store32 domain failure keeps state and clock"
  if storeByteAddressFailGuard then
    IO.println "PASS exact-state StoreByte failing address keeps state and clock"
  else
    IO.println "FAIL exact-state StoreByte failing address keeps state and clock"
  if storeByteValueFailGuard then
    IO.println "PASS exact-state StoreByte failing value keeps state and clock"
  else
    IO.println "FAIL exact-state StoreByte failing value keeps state and clock"
  if storeByteDomainFailGuard then
    IO.println "PASS exact-state StoreByte domain failure keeps state and clock"
  else
    IO.println "FAIL exact-state StoreByte domain failure keeps state and clock"
  if store32NonClockedAddressFailGuard then
    IO.println "PASS non-clocked Store32 failing address rejected with Error"
  else
    IO.println "FAIL non-clocked Store32 failing address rejected with Error"
  if store32NonClockedDomainFailGuard then
    IO.println "PASS non-clocked Store32 domain failure rejected with Error"
  else
    IO.println "FAIL non-clocked Store32 domain failure rejected with Error"
  if storeByteNonClockedAddressFailGuard then
    IO.println "PASS non-clocked StoreByte failing address rejected with Error"
  else
    IO.println "FAIL non-clocked StoreByte failing address rejected with Error"
  if storeByteNonClockedDomainFailGuard then
    IO.println "PASS non-clocked StoreByte domain failure rejected with Error"
  else
    IO.println "FAIL non-clocked StoreByte domain failure rejected with Error"
  pure store32ErrorGuard

end Flapjack.Test.PanSemStore32ErrorExactParity