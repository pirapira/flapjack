import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
Direct regression for the exact source `PanSemExactState` `Dec` error
equations.  HOL `panSemScript.sml:558-565` rejects a `Dec` whose initialiser
expression fails to evaluate, or whose value does not match the declared
shape, with `SOME Error` over the unchanged state.  The expected values are the
original-HOL `EVAL` rows in `scripts/hol-probes/pan_sem_dec_e2e_probe.out`:

* `dec_eval_missing_result=SOME Error`, `dec_eval_missing_locals=SOME (ValWord 3w)`,
  `dec_eval_missing_clock=5`;
* `dec_shape_mismatch_result=SOME Error`,
  `dec_shape_mismatch_locals=SOME (ValWord 3w)`,
  `dec_shape_mismatch_clock=5`.

This module is untagged infrastructure: the reduced `PanValueFfiClockResult`
encoding is not literally HOL's `(result option # state)` type, so no `@[hol]`
attribute is attached.
-/

namespace Flapjack.Test.PanSemDecErrorExactParity

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

/-- Access whose `memaddrs`-style domain is empty, so every read misses. -/
private def emptyAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel (fun _ => false)
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

private def localsWithX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

/-- State with a present memory cell at address `8` and local `x`. -/
private def memoryState : PanSemExactState Word64 Unit :=
  exactStateOf <| exactLegacy 5 localsWithX exactMemory none

private def decEvalFailProgram : Prog Word64 :=
  .dec "d" Shape.one (.load Shape.one (.const 11)) .skip

private def decShapeMismatchProgram : Prog Word64 :=
  .dec "d" (Shape.named "Other") (.const 7) .skip

private def evaluate (state : PanSemExactState Word64 Unit) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateExactState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

private def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 (BitVec.ofNat 64 8) 5 localsWithX
    (fun _ => none) exactMemory statefulTestFfiState program
    (memoryAccess := memoryAccess)

/-- An `Error` control result at `clock` that keeps local `x` at `localValue`. -/
private def isErrorKeeping (clock localValue : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock &&
            (match locals "x" with
             | some (.word value) => value == BitVec.ofNat 64 localValue
             | _ => false)
      | _ => false
  | _ => false

/-- A stepped `Error` that keeps local `x` at `localValue`. -/
private def isErrorKeepingStepped (localValue : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals _ _ _, _) =>
      (match locals "x" with
       | some (.word value) => value == BitVec.ofNat 64 localValue
       | _ => false)
  | _ => false

private def decEvalFailGuard : Bool :=
  isErrorKeeping 5 3 (evaluate memoryState decEvalFailProgram)

private def decShapeMismatchGuard : Bool :=
  isErrorKeeping 5 3 (evaluate memoryState decShapeMismatchProgram)

private def decNonClockedEvalFailGuard : Bool :=
  isErrorKeepingStepped 3 (nonClockedEvaluate decEvalFailProgram (some emptyAccess))

private def decNonClockedShapeMismatchGuard : Bool :=
  isErrorKeepingStepped 3 (nonClockedEvaluate decShapeMismatchProgram)

private def decErrorGuard : Bool :=
  decEvalFailGuard && decShapeMismatchGuard &&
    decNonClockedEvalFailGuard && decNonClockedShapeMismatchGuard

#guard decErrorGuard

def runChecks : IO Bool := do
  IO.println (if decEvalFailGuard then
    "PASS exact-state Dec failing initialiser keeps state and clock"
   else "FAIL exact-state Dec failing initialiser keeps state and clock")
  IO.println (if decShapeMismatchGuard then
    "PASS exact-state Dec shape mismatch keeps state and clock"
   else "FAIL exact-state Dec shape mismatch keeps state and clock")
  IO.println (if decNonClockedEvalFailGuard then
    "PASS non-clocked Dec failing initialiser rejected with Error"
   else "FAIL non-clocked Dec failing initialiser rejected with Error")
  IO.println (if decNonClockedShapeMismatchGuard then
    "PASS non-clocked Dec shape mismatch rejected with Error"
   else "FAIL non-clocked Dec shape mismatch rejected with Error")
  pure decErrorGuard

end Flapjack.Test.PanSemDecErrorExactParity