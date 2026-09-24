import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
Direct regression for the exact source `PanSemExactState` `Primitive` error
equations.  HOL `panSemScript.sml:573-582` rejects a `Primitive` whose argument
list fails to evaluate, whose `pan_primop` produces nothing (including a wrong
argument count), whose destination local is unbound, or whose result shape does
not match the destination, with `SOME Error` over the unchanged state.

The expected values extend the original-HOL `EVAL` rows.  The existing
`scripts/hol-probes/pan_sem_primitive_e2e_probe.out` covers the success case,
an argument-evaluation failure and an unbound destination; the paired
`scripts/hol-probes/pan_sem_primitive_error_probe.out` covers the remaining two
branches:

* `prim_wrong_arity_result=SOME Error`,
  `prim_wrong_arity_locals=SOME (RStruct [ValWord 0w; ValWord 0w])`,
  `prim_wrong_arity_clock=5`;
* `prim_shape_mismatch_result=SOME Error`,
  `prim_shape_mismatch_locals=SOME (ValWord 1w)`,
  `prim_shape_mismatch_clock=5`.

This module is untagged infrastructure: the reduced `PanValueFfiClockResult`
encoding is not literally HOL's `(result option # state)` type, so no `@[hol]`
attribute is attached.
-/

namespace Flapjack.Test.PanSemPrimitiveErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- `AddCarry` for three words, as in HOL `pan_primop`; every other arity or
non-word operand yields `none`. -/
private def addCarryPrimitive : PanPrimitiveHandler Word64 :=
  fun operator values =>
    match operator, values with
    | .addCarry, [.word left, .word right, .word carryIn] =>
        some (.rStruct [.word (left + right + carryIn), .word 0])
    | _, _ => none

private def exactDomain : Word64 → Bool :=
  fun address => address == 8

private def exactAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain
    (fun _ => false) false

private def exactLegacy (locals : VarName → Option (PanValue Word64)) :
    PanSemEvaluateState Word64 Unit :=
  { structs := []
    functions := []
    locals := locals
    globals := fun _ => none
    memory := fun _ => some (.word 0)
    ffi := statefulTestFfiState
    clock := 5
    baseAddress := 0
    topAddress := 100
    bytesInWord := 8
    memoryAccess := none }

private def exactState (locals : VarName → Option (PanValue Word64)) :
    PanSemExactState Word64 Unit :=
  { legacy := exactLegacy locals, memoryAccess := exactAccess }

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 1) else none

private def localsStructX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.rStruct [.word 0, .word 0]) else none

private def evaluate (state : PanSemExactState Word64 Unit) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateExactState statefulTestContext addCarryPrimitive statefulTestHandler
    state program

/-- Error at `clock` whose preserved `"x"` local is the given word. -/
private def isWordX (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock &&
            (match locals "x" with
             | some (.word word) => word == BitVec.ofNat 64 value
             | _ => false)
      | _ => false
  | _ => false

/-- Error at `clock` whose preserved `"x"` local is the zero `RStruct`. -/
private def isStructX (clock : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock &&
            (match locals "x" with
             | some (.rStruct [.word left, .word right]) => left == 0 && right == 0
             | _ => false)
      | _ => false
  | _ => false

private def wrongArityProgram : Prog Word64 :=
  .primitive "x" .addCarry [.const 1]

private def shapeMismatchProgram : Prog Word64 :=
  .primitive "x" .addCarry [.const 1, .const 2, .const 0]

private def destinationNoneProgram : Prog Word64 :=
  .primitive "y" .addCarry [.const 1, .const 2, .const 0]

private def argumentsNoneProgram : Prog Word64 :=
  .primitive "x" .addCarry [.const 1, .const 2, .var .local "z"]

private def primWrongArityGuard : Bool :=
  isStructX 5 (evaluate (exactState localsStructX) wrongArityProgram)

private def primShapeMismatchGuard : Bool :=
  isWordX 5 1 (evaluate (exactState localsWordX) shapeMismatchProgram)

private def primDestinationNoneGuard : Bool :=
  isStructX 5 (evaluate (exactState localsStructX) destinationNoneProgram)

private def primArgumentsNoneGuard : Bool :=
  isStructX 5 (evaluate (exactState localsStructX) argumentsNoneProgram)

private def primErrorGuard : Bool :=
  primWrongArityGuard && primShapeMismatchGuard &&
    primDestinationNoneGuard && primArgumentsNoneGuard

#guard primErrorGuard

def runChecks : IO Bool := do
  if primWrongArityGuard then
    IO.println "PASS exact-state Primitive pan_primop failure keeps state and clock"
  else
    IO.println "FAIL exact-state Primitive pan_primop failure"
  if primShapeMismatchGuard then
    IO.println "PASS exact-state Primitive destination shape mismatch keeps state and clock"
  else
    IO.println "FAIL exact-state Primitive destination shape mismatch"
  if primDestinationNoneGuard then
    IO.println "PASS exact-state Primitive unbound destination keeps state and clock"
  else
    IO.println "FAIL exact-state Primitive unbound destination"
  if primArgumentsNoneGuard then
    IO.println "PASS exact-state Primitive failing arguments keeps state and clock"
  else
    IO.println "FAIL exact-state Primitive failing arguments"
  pure primErrorGuard

end Flapjack.Test.PanSemPrimitiveErrorExactParity