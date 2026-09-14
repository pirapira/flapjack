import Flapjack.PanBState

/-!
# Parity checks for Pancake `bst_def`

The direct HOL fixture in `scripts/hol-probes/pan_bst_probe.out` evaluates the
same projection from `pan_itreeSemScript.sml:692-705`.  These checks exercise
all projected fields and separately confirm that clock and FFI are omitted.
-/

namespace Flapjack.Test.PanBStateParity

open Flapjack

def testFfi : FfiState Unit :=
  { oracle := fun _ state _ _ => .returned state []
    state := ()
    ioEvents := [] }

def testState : PanState Nat Unit :=
  { locals := fun name => if name == "local" then some (.word 1) else none
    globals := fun name => if name == "global" then some (.word 2) else none
    structs := [("pair", { fields := [("left", .one), ("right", .one)], size := 2 })]
    code := [("main", ([("x", .one)], .return (.const 0), .one))]
    eshapes := [("exn", .one)]
    memory := fun address => .word (address + 10)
    memaddrs := fun address => address < 100
    shMemaddrs := fun address => address < 20
    clock := 17
    be := false
    ffi := testFfi
    baseAddress := 1000
    topAddress := 2000 }

def isWord (value : Option (PanValue Nat)) (expected : Nat) : Bool :=
  match value with
  | some (.word actual) => actual == expected
  | _ => false

def isMemoryWord (value : PanWordLab Nat) (expected : Nat) : Bool :=
  match value with
  | .word actual => actual == expected

def observeFields : Bool :=
  isWord ((panBst testState).locals "local") 1 &&
  isWord ((panBst testState).globals "global") 2 &&
  (panBst testState).structs.length == 1 &&
  (panBst testState).code.length == 1 &&
  (panBst testState).eshapes.length == 1 &&
  isMemoryWord ((panBst testState).memory 3) 13 &&
  (panBst testState).memaddrs 99 &&
  !(panBst testState).memaddrs 100 &&
  (panBst testState).shMemaddrs 19 &&
  !(panBst testState).shMemaddrs 20 &&
  !(panBst testState).be &&
  (panBst testState).baseAddress == 1000 &&
  (panBst testState).topAddress == 2000

def observeClockAndFfiDropped : Bool :=
  testState.clock == 17 && testState.ffi.state == ()

#guard observeFields
#guard observeClockAndFfiDropped

def runChecks : IO Bool := do
  if observeFields then IO.println "PASS bst projected fields"
  else IO.println "FAIL bst projected fields"
  if observeClockAndFfiDropped then IO.println "PASS bst clock and FFI omission"
  else IO.println "FAIL bst clock and FFI omission"
  pure (observeFields && observeClockAndFfiDropped)

end Flapjack.Test.PanBStateParity
