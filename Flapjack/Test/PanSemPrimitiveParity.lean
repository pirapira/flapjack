/-
  Direct parity checks for the production source-state `Primitive` equation
  against the original CakeML HOL oracle in
  `scripts/hol-probes/pan_sem_primitive_e2e_probe.out`.

  The oracle observes `AddCarry` on three words with a matching struct-valued
  destination, a fresh destination, and a missing argument expression.  The
  Lean checks below reproduce those observations with a handler whose
  `AddCarry` result matches the HOL `pan_primop` result for the probe inputs
  (`RStruct [ValWord 3w; ValWord 0w]`).
-/
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

namespace Flapjack.Test.PanSemPrimitiveParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- An `AddCarry` handler mirroring the HOL `pan_primop` result shape for the
    probe inputs: the low word is the sum and the high word is the carry. -/
def addCarryPrimitive : PanPrimitiveHandler Word64 :=
  fun operator values =>
    match operator, values with
    | .addCarry, [.word left, .word right, .word carryIn] =>
        some (.rStruct [.word (left + right + carryIn), .word 0])
    | _, _ => none

/-- Source state with `x` bound to a two-field struct, `g` bound to a word, and
    the given clock. -/
def primState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.rStruct [.word 0, .word 0])
      else if name == "g" then some (.word 4)
      else none
    globals := fun name => if name == "g" then some (.word 4) else none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := 0
    topAddress := 100 }

def primEvaluate (clock fuel : Nat) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateCodeStateWithFuel statefulTestContext addCarryPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (fuel + 1) (primState clock) program

def primUpdatedLocals : VarName → Option (PanValue Word64) :=
  updatePanValueMap (primState 5).locals "x" (.rStruct [.word 3, .word 0])

def primOkOutcome : PanValueFfiClockResult Word64 Unit :=
  (.control (.normal primUpdatedLocals (primState 5).globals
      (primState 5).memory (primState 5).ffi), 5)

theorem prim_ok_eq :
    primEvaluate 5 3 (.primitive "x" .addCarry
        [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
          .const (BitVec.ofNat 64 0)]) =
      some primOkOutcome := by
  unfold primEvaluate primOkOutcome
  rw [panSemEvaluateCodeStateWithFuel_primitive]
  simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp,
    primState, panValueShape, panShapeMatches, panShapeMatches.panShapeListMatches,
    addCarryPrimitive, primUpdatedLocals]

theorem prim_fresh_invalid_eq :
    primEvaluate 5 3 (.primitive "y" .addCarry
        [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
          .const (BitVec.ofNat 64 0)]) = none := by
  unfold primEvaluate
  rw [panSemEvaluateCodeStateWithFuel_primitive]
  simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp,
    primState, addCarryPrimitive]

theorem prim_arg_missing_eq :
    primEvaluate 5 3 (.primitive "x" .addCarry
        [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
          .var .local "z"]) = none := by
  unfold primEvaluate
  rw [panSemEvaluateCodeStateWithFuel_primitive]
  simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp,
    primState]

def isStruct3 : Option (PanValue Word64) → Bool
  | some (.rStruct [.word low, .word high]) =>
      low == BitVec.ofNat 64 3 && high == BitVec.ofNat 64 0
  | _ => false

def primOkGuard : Bool :=
  match primEvaluate 5 3 (.primitive "x" .addCarry
      [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
        .const (BitVec.ofNat 64 0)]) with
  | some (.control (.normal locals _ _ _), 5) => isStruct3 (locals "x")
  | _ => false

def primFreshGuard : Bool :=
  (primEvaluate 5 3 (.primitive "y" .addCarry
      [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
        .const (BitVec.ofNat 64 0)])).isNone

def primMissingGuard : Bool :=
  (primEvaluate 5 3 (.primitive "x" .addCarry
      [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
        .var .local "z"])).isNone

def primGuard : Bool :=
  primOkGuard && primFreshGuard && primMissingGuard

#guard primGuard

def runChecks : IO Bool := do
  if primOkGuard then
    IO.println "PASS panSem Primitive accepted AddCarry updates destination"
  else
    IO.println "FAIL panSem Primitive accepted AddCarry updates destination"
  if primFreshGuard then
    IO.println "PASS panSem Primitive fresh destination rejected"
  else
    IO.println "FAIL panSem Primitive fresh destination rejected"
  if primMissingGuard then
    IO.println "PASS panSem Primitive argument evaluation failure rejected"
  else
    IO.println "FAIL panSem Primitive argument evaluation failure rejected"
  pure primGuard

end Flapjack.Test.PanSemPrimitiveParity
