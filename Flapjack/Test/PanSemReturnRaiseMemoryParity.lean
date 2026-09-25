import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
Direct regression for the exact source `PanSemExactState` `Return`/`Raise`
equations.  The payload expressions read the source state's memory, so a
present word cell exercises the state-derived `memoryAccess` path while an
address outside `memaddrs` exercises the `SOME Error` rejection.  The expected
values are the original-HOL `EVAL` rows in
`scripts/hol-probes/pan_sem_return_raise_memory_probe.out`:

* `ret_mem_fail_result=SOME Error`, `ret_mem_fail_locals=SOME (ValWord 3w)`,
  `ret_mem_fail_clock=5`;
* `ret_mem_ok_result=SOME (Return (ValWord 119w))`, `ret_mem_ok_locals=NONE`;
* `raise_mem_fail_result=SOME Error`, `raise_mem_fail_locals=SOME (ValWord 3w)`;
* `raise_mem_badshape_result=SOME Error`,
  `raise_mem_badshape_locals=SOME (ValWord 3w)`;
* `raise_mem_ok_result=SOME (Exception «E» (ValWord 119w))`,
  `raise_mem_ok_locals=NONE`.

This module is untagged infrastructure: the reduced `PanValueFfiClockResult`
encoding is not literally HOL's `(result option # state)` type, so no `@[hol]`
attribute is attached.
-/

namespace Flapjack.Test.PanSemReturnRaiseMemoryParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- Source memory with a present word cell at address `8` and a zero fallback. -/
private def exactMemory : Word64 → Option (PanValue Word64) :=
  fun address =>
    if address == 8 then some (.word (BitVec.ofNat 64 0x77)) else some (.word 0)

private def exactDomain : Word64 → Bool :=
  fun address => address == 8

private def exactAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain
    (fun _ => false) false

private def exactLegacy (clock : Nat) (locals : VarName → Option (PanValue Word64))
    (memory : Word64 → Option (PanValue Word64))
    (contracts : Option PanValueCallContracts) :
    PanSemEvaluateState Word64 Unit :=
  { structs := []
    functions := []
    locals := locals
    globals := fun _ => none
    memory := memory
    ffi := statefulTestFfiState
    clock := clock
    baseAddress := 0
    topAddress := 100
    bytesInWord := 8
    memoryAccess := none
    contracts := contracts
    memoryHandler := none }

private def exactStateOf (legacy : PanSemEvaluateState Word64 Unit) :
    PanSemExactState Word64 Unit :=
  { legacy := legacy, memoryAccess := exactAccess }

/-- State used by the memory-reading guards: local `x` holds a word and memory
    has a present cell at address `8`. -/
private def memoryState (clock : Nat) (contracts : Option PanValueCallContracts) :
    PanSemExactState Word64 Unit :=
  exactStateOf <| exactLegacy clock
    (fun name => if name == "x" then some (.word 3) else none) exactMemory contracts

/-- State whose source evaluation fails immediately (no locals, no memory). -/
private def emptyState : PanSemExactState Word64 Unit :=
  exactStateOf <| exactLegacy 5 (fun _ => none) (fun _ => none) none

/-- State whose source evaluation succeeds with `.word 7`. -/
private def wordState (contracts : Option PanValueCallContracts) :
    PanSemExactState Word64 Unit :=
  exactStateOf <| exactLegacy 5 (fun _ => some (.word 7)) (fun _ => none) contracts

private def evaluate (state : PanSemExactState Word64 Unit) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateExactState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

private def contractsOne : Option PanValueCallContracts :=
  some { returnShapes := [], exceptionShapes := [("E", Shape.one)] }

private def contractsBadShape : Option PanValueCallContracts :=
  some { returnShapes := [], exceptionShapes := [("E", Shape.named "Other")] }

private def isWordValue (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

private def isNoneOption : Option (PanValue Word64) → Bool
  | none => true
  | some _ => false

private def isErrorKeeping (clock localValue : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ => n == clock && isWordValue localValue (locals "x")
      | _ => false
  | _ => false

private def isReturnedWith (clock expected : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .returned locals _ _ _ [value] =>
          n == clock && isNoneOption (locals "x") && isWordValue expected value
      | _ => false
  | _ => false

private def isRaisedWith (clock : Nat) (exceptionId : String) (expected : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .raised locals _ _ _ exception value =>
          n == clock && isNoneOption (locals "x") && exception == exceptionId &&
            isWordValue expected value
      | _ => false
  | _ => false

private def loadHit : Exp Word64 := .load Shape.one (.const 8)

private def loadMiss : Exp Word64 := .load Shape.one (.const 11)

private def returnMissGuard : Bool :=
  isErrorKeeping 5 3 (evaluate (memoryState 5 none) (.return loadMiss))

private def returnHitGuard : Bool :=
  isReturnedWith 5 119 (evaluate (memoryState 5 none) (.return loadHit))

private def raiseMissGuard : Bool :=
  isErrorKeeping 5 3 (evaluate (memoryState 5 contractsOne) (.raise "E" loadMiss))

private def raiseBadShapeGuard : Bool :=
  isErrorKeeping 5 3
    (evaluate (memoryState 5 contractsBadShape) (.raise "E" loadHit))

private def raiseHitGuard : Bool :=
  isRaisedWith 5 "E" 119 (evaluate (memoryState 5 contractsOne) (.raise "E" loadHit))

private def exactGuard : Bool :=
  returnMissGuard && returnHitGuard && raiseMissGuard && raiseBadShapeGuard &&
    raiseHitGuard

#guard exactGuard

/-- `Return` whose payload fails to evaluate returns `SOME Error` over the full
    exact state. -/
theorem returnMiss_eq :
    evaluate emptyState (.return (.var .local "z")) =
      some (.control (.error emptyState.legacy.locals emptyState.legacy.globals
        emptyState.legacy.memory emptyState.legacy.ffi), emptyState.legacy.clock) := by
  apply panSemEvaluateExactState_return_error_of_eval_none
  simp [emptyState, exactStateOf, exactLegacy, evalPanValueExp]

/-- `Raise` whose payload fails to evaluate returns `SOME Error` over the full
    exact state. -/
theorem raiseMiss_eq :
    evaluate emptyState (.raise "E" (.var .local "z")) =
      some (.control (.error emptyState.legacy.locals emptyState.legacy.globals
        emptyState.legacy.memory emptyState.legacy.ffi), emptyState.legacy.clock) := by
  apply panSemEvaluateExactState_raise_error_of_eval_none
  simp [emptyState, exactStateOf, exactLegacy, evalPanValueExp]

/-- `Raise` whose payload shape does not match the declared shape returns
    `SOME Error` over the full exact state. -/
theorem raiseBadShape_eq :
    evaluate (wordState contractsBadShape) (.raise "E" (.var .local "x")) =
      some (.control (.error (wordState contractsBadShape).legacy.locals
        (wordState contractsBadShape).legacy.globals
        (wordState contractsBadShape).legacy.memory
        (wordState contractsBadShape).legacy.ffi),
        (wordState contractsBadShape).legacy.clock) := by
  apply panSemEvaluateExactState_raise_error_of_invalid (value := .word 7)
  · simp [wordState, exactStateOf, exactLegacy, evalPanValueExp]
  · simp [wordState, exactStateOf, exactLegacy, contractsBadShape,
      panValueExceptionValid, panValueShape, panShapeMatches, lookupInfo]

def runChecks : IO Bool := do
  if returnMissGuard then
    IO.println "PASS exact-state Return eval failure keeps state and clock"
  else IO.println "FAIL exact-state Return eval failure keeps state and clock"
  if returnHitGuard then
    IO.println "PASS exact-state Return memory read returns the cell"
  else IO.println "FAIL exact-state Return memory read returns the cell"
  if raiseMissGuard then
    IO.println "PASS exact-state Raise eval failure keeps state and clock"
  else IO.println "FAIL exact-state Raise eval failure keeps state and clock"
  if raiseBadShapeGuard then
    IO.println "PASS exact-state Raise shape mismatch keeps state and clock"
  else IO.println "FAIL exact-state Raise shape mismatch keeps state and clock"
  if raiseHitGuard then
    IO.println "PASS exact-state Raise memory read raises the matched value"
  else IO.println "FAIL exact-state Raise memory read raises the matched value"
  pure exactGuard

end Flapjack.Test.PanSemReturnRaiseMemoryParity
