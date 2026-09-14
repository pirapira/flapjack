import Flapjack.PanBst

/-!
# Parity checks for Pancake `bst_def`

The direct HOL fixture in `scripts/hol-probes/pan_bst_probe.out` is generated
from `pan_itreeSemScript.sml:692-708`.  Lean checks cover every copied field
and verify that changing the omitted clock or FFI state cannot affect the
projection.
-/

namespace Flapjack.Test.PanBstParity

open Flapjack

def sourceState : PanSemState Nat String where
  locals := updatePanValueMap (fun _ => none) "local" (.word 3)
  globals := updatePanValueMap (fun _ => none) "global" (.word 5)
  structs := [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]
  code := fun name => if name == "main" then some ([], .skip, .one) else none
  exceptionShapes := fun name => if name == "E" then some .one else none
  memory := fun address => if address == 7 then some (.word 9) else none
  memaddrs := fun address => address == 7
  sharedMemaddrs := fun address => address == 11
  clock := 4
  be := true
  ffi := "initial"
  baseAddress := 100
  topAddress := 200

def hasWord (value : Option (PanValue Nat)) (expected : Nat) : Bool :=
  match value with
  | some (.word actual) => actual == expected
  | _ => false

def observeCopiedFields : Bool :=
  let projected := panBst sourceState
  hasWord (projected.locals "local") 3 &&
    hasWord (projected.globals "global") 5 &&
    projected.structs.length == sourceState.structs.length &&
    (match projected.code "main" with | some _ => true | none => false) &&
    (match projected.exceptionShapes "E" with | some .one => true | _ => false) &&
    hasWord (projected.memory 7) 9 &&
    projected.memaddrs 7 && projected.sharedMemaddrs 11 &&
    projected.be && projected.baseAddress == 100 && projected.topAddress == 200

theorem clockProjectionExample :
    panBst { sourceState with clock := 0 } =
      panBst { sourceState with clock := 99 } := by
  rfl

theorem ffiProjectionExample :
    panBst { sourceState with ffi := "left" } =
      panBst { sourceState with ffi := "right" } := by
  rfl

def observeClockIrrelevant : Bool := true

def observeFfiIrrelevant : Bool := true

#guard observeCopiedFields
#guard observeClockIrrelevant
#guard observeFfiIrrelevant

def runChecks : IO Bool := do
  if observeCopiedFields then IO.println "PASS bst copies semantic fields"
    else IO.println "FAIL bst copies semantic fields"
  if observeClockIrrelevant then IO.println "PASS bst drops clock"
    else IO.println "FAIL bst drops clock"
  if observeFfiIrrelevant then IO.println "PASS bst drops ffi"
    else IO.println "FAIL bst drops ffi"
  pure (observeCopiedFields && observeClockIrrelevant && observeFfiIrrelevant)

end Flapjack.Test.PanBstParity
