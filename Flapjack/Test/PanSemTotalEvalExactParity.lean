import Flapjack.Pancake.Semantics.PanSem.TotalEvalExact
import Flapjack.Test.PanSemExtCallExactParity

/-! Direct original-HOL rows for the exact-state PanSem dispatcher fragment.
    Call/DecCall cases correspond to `call_code_map_7`,
    `recursive_call_code_map_7`, `deccall_code_map_7`,
    `nested_deccall_code_map_7`, and recursive timeout rows in
    `scripts/hol-probes/pan_sem_e2e_probe.out`; matching exception handling
    corresponds to `call_handles_exception_7`. -/

namespace Flapjack.Test.PanSemTotalEvalExactParity

open Flapjack
open Flapjack.Pancake.PanLang (ExpHOL ProgHOL)
open Flapjack.Test.PanSemExtCallExactParity

abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

abbrev W := RiscV.Word 64

private def baseState : PanSemStateExact 64 Unit :=
  { locals := fun name => if name = ml "x" then some (.val (.word 7)) else none
    globals := fun name => if name = ml "g" then some (.val (.word 1)) else none
    structs := []
    code := fun _ => none
    eshapes := fun name => if name = ml "E" then some .one else none
    memory := fun _ => .word 0
    memaddrs := fun address => address = 0
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

private instance : DecidablePred baseState.memaddrs := fun address =>
  if h : address = 0 then isTrue h else isFalse h

private instance : DecidablePred baseState.shMemaddrs := fun _ => isFalse id

private def idCodeState (clock : Nat) : PanSemStateExact 64 Unit :=
  { baseState with
    code := fun name =>
      if name = ml "id" then
        some ([(ml "x", .one)], .return (.var .local (ml "x")), .one)
      else if name = ml "raiseE" then
        some ([], .raise (ml "E") (.const 7), .one)
      else none
    locals := fun name =>
      if name = ml "ev" then some (.val (.word 0)) else baseState.locals name
    clock := clock }

private instance (clock : Nat) : DecidablePred (idCodeState clock).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (idCodeState clock).shMemaddrs := by
  intro address
  change Decidable (baseState.shMemaddrs address)
  infer_instance

private def nestedCallCodeState (clock : Nat) : PanSemStateExact 64 Unit :=
  { baseState with
    code := fun name =>
      if name = ml "f" then
        some ([], .decCall (ml "nested") .one (ml "g") []
          (.return (.var .local (ml "nested"))), .one)
      else if name = ml "g" then
        some ([], .return (.const 7), .one)
      else none
    clock := clock }

private instance (clock : Nat) : DecidablePred (nestedCallCodeState clock).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (nestedCallCodeState clock).shMemaddrs := by
  intro address
  change Decidable (baseState.shMemaddrs address)
  infer_instance

private def nestedDecCallCodeState (clock : Nat) : PanSemStateExact 64 Unit :=
  { baseState with
    code := fun name =>
      if name = ml "f" then
        some ([], .decCall (ml "nested") .one (ml "g") []
          (.return (.var .local (ml "nested"))), .one)
      else if name = ml "g" then
        some ([], .return (.const 7), .one)
      else none
    clock := clock }

private instance (clock : Nat) : DecidablePred (nestedDecCallCodeState clock).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (nestedDecCallCodeState clock).shMemaddrs := by
  intro address
  change Decidable (baseState.shMemaddrs address)
  infer_instance

private def recursiveCallCodeState (clock : Nat) : PanSemStateExact 64 Unit :=
  { baseState with
    code := fun name =>
      if name = ml "loop" then some ([], .call none (ml "loop") [], .one)
      else none
    clock := clock }

private instance (clock : Nat) : DecidablePred (recursiveCallCodeState clock).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (recursiveCallCodeState clock).shMemaddrs := by
  intro address
  change Decidable (baseState.shMemaddrs address)
  infer_instance

private def recursiveDecCallCodeState (clock : Nat) : PanSemStateExact 64 Unit :=
  { baseState with
    code := fun name =>
      if name = ml "loop" then
        some ([], .decCall (ml "nested") .one (ml "loop") [] .skip, .one)
      else none
    clock := clock }

private instance (clock : Nat) : DecidablePred (recursiveDecCallCodeState clock).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (recursiveDecCallCodeState clock).shMemaddrs := by
  intro address
  change Decidable (baseState.shMemaddrs address)
  infer_instance

private def recursiveExact
    (program : ProgHOL 64) (state : PanSemStateExact 64 Unit)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs] :=
  evalPanSemRecursiveCallHOLExact program state

private def primitiveState : PanSemStateExact 64 Unit :=
  { baseState with
    locals := fun name =>
      if name = ml "x" then some (.rStruct [.val (.word 0), .val (.word 0)])
      else none }

private instance : DecidablePred primitiveState.memaddrs := fun address =>
  if h : address = 0 then isTrue h else isFalse h

private instance : DecidablePred primitiveState.shMemaddrs := fun _ => isFalse id

private def exactDispatch (program : ProgHOL 64) (state : PanSemStateExact 64 Unit)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs] :
    Option (Option (PanSemResultExact 64) × PanSemStateExact 64 Unit) :=
  evalPanSemNonrecursiveHOLExact program state

private def resultIsError
    (result : Option (PanSemResultExact 64)) : Bool :=
  match result with
  | some .error => true
  | _ => false

private def localWord (state : PanSemStateExact 64 Unit) (name : String) : Option Nat :=
  match state.locals (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

private def memoryWord (state : PanSemStateExact 64 Unit) (address : W) : Option Nat :=
  match state.memory address with
  | .word value => some value.toNat

private def badReadState : PanSemStateExact 8 Unit :=
  PanSemExtCallExactParity.baseState returningFfi memory8 (fun _ => False)

private instance : DecidablePred badReadState.memaddrs := fun _ => isFalse id

private instance : DecidablePred badReadState.shMemaddrs := fun _ => isFalse id

def skipBreakTickRows : Bool :=
  let skipOk := match exactDispatch .skip baseState with
    | some (none, state) => state.clock == 5 && localWord state "x" == some 7
    | _ => false
  let breakOk := match exactDispatch .break baseState with
    | some (some .break, state) => state.clock == 5 && localWord state "x" == some 7
    | _ => false
  let continueOk := match exactDispatch .continue baseState with
    | some (some .continue, state) => state.clock == 5 && localWord state "x" == some 7
    | _ => false
  let tickZero := match exactDispatch .tick { baseState with clock := 0 } with
    | some (some .timeOut, state) => state.clock == 0 && (state.locals (ml "x")).isNone
    | _ => false
  let tickPositive := match exactDispatch .tick baseState with
    | some (none, state) => state.clock == 4 && localWord state "x" == some 7
    | _ => false
  skipOk && breakOk && continueOk && tickZero && tickPositive

def assignPrimitiveRows : Bool :=
  let assignOk := match exactDispatch (.assign .local (ml "x") (.const 9)) baseState with
    | some (none, state) => localWord state "x" == some 9
    | _ => false
  let primitiveOk := match exactDispatch
      (.primitive (ml "x") .addCarry [.const 40, .const 50, .const 0]) primitiveState with
    | some (none, state) =>
        match state.locals (ml "x") with
        | some (.rStruct [.val (.word sum), .val (.word carry)]) =>
            sum.toNat == 90 && carry.toNat == 0
        | _ => false
    | _ => false
  assignOk && primitiveOk

def storeRows : Bool :=
  let storeOk := match exactDispatch (.store (.const 0) (.const 7)) baseState with
    | some (none, state) => memoryWord state 0 == some 7
    | _ => false
  let store32Ok := match exactDispatch (.store32 (.const 0) (.const 0x11223344)) baseState with
    | some (none, state) => memoryWord state 0 == some 0x11223344
    | _ => false
  let storeByteOk := match exactDispatch (.storeByte (.const 0) (.const 0xAB)) baseState with
    | some (none, state) => memoryWord state 0 == some 0xAB
    | _ => false
  let outside := { baseState with memaddrs := fun _ => False }
  let storeErr := match exactDispatch (.store (.const 0) (.const 7)) outside with
    | some (result, state) => resultIsError result && memoryWord state 0 == some 0
    | _ => false
  storeOk && store32Ok && storeByteOk && storeErr

def returnRaiseRows : Bool :=
  let returnOk := match exactDispatch (.return (.const 41)) baseState with
    | some (some (.returned (.val (.word value))), state) =>
        value.toNat == 41 && (state.locals (ml "x")).isNone
    | _ => false
  let raiseOk := match exactDispatch (.raise (ml "E") (.const 5)) baseState with
    | some (some (.exception name (.val (.word value))), state) =>
        name == ml "E" && value.toNat == 5 && (state.locals (ml "x")).isNone
    | _ => false
  let raiseMissing := match exactDispatch (.raise (ml "missing") (.const 5)) baseState with
    | some (result, state) => resultIsError result && localWord state "x" == some 7
    | _ => false
  returnOk && raiseOk && raiseMissing

def sharedMemoryRows : Bool :=
  let loadOutOfDomain := match exactDispatch
      (.shMemLoad .opW .local (ml "x") (.const 8)) baseState with
    | some (result, state) => resultIsError result && localWord state "x" == some 7
    | _ => false
  let storeOutOfDomain := match exactDispatch
      (.shMemStore .opW (.const 8) (.const 0xAB)) baseState with
    | some (result, state) => resultIsError result && state.ffi.ioEvents == []
    | _ => false
  loadOutOfDomain && storeOutOfDomain

def extCallRows : Bool :=
  let result := evalPanSemNonrecursiveHOLExact
      (.extCall (ml "x") (.const 0) (.const 2) (.const 0) (.const 2)) badReadState
  match result with
  | some (outcome, state) =>
      (match outcome with
      | some .error => true
      | _ => false) &&
        (match state.memory 0 with
        | .word byte => byte.toNat == 0xAB)
  | none => false

def stateOwnedCallRows : Bool :=
  let direct := recursiveExact (.call none (ml "id") [.const 7]) (idCodeState 10)
  let nested := recursiveExact (.call none (ml "f") []) (nestedCallCodeState 10)
  let handlerInfo := some (none,
    some (ml "E", ml "ev", .return (.var .local (ml "ev"))))
  let handled := recursiveExact (.call handlerInfo (ml "raiseE") []) (idCodeState 10)
  let directOk := match direct with
    | some (some (.returned (.val (.word value))), post) =>
        value.toNat == 7 && post.clock == 9 && (post.locals (ml "x")).isNone
    | _ => false
  let nestedOk := match nested with
    | some (some (.returned (.val (.word value))), post) =>
        value.toNat == 7 && post.clock == 8
    | _ => false
  let handlerOk := match handled with
    | some (some (.returned (.val (.word value))), post) =>
        value.toNat == 7 && post.clock == 9
    | _ => false
  directOk && nestedOk && handlerOk

def stateOwnedDecCallRows : Bool :=
  let direct := recursiveExact
    (.decCall (ml "answer") .one (ml "id") [.const 7]
      (.return (.var .local (ml "answer")))) (idCodeState 10)
  let nested := recursiveExact
    (.decCall (ml "answer") .one (ml "f") []
      (.return (.var .local (ml "answer")))) (nestedDecCallCodeState 10)
  let directOk := match direct with
    | some (some (.returned (.val (.word value))), post) =>
        value.toNat == 7 && post.clock == 9
    | _ => false
  let nestedOk := match nested with
    | some (some (.returned (.val (.word value))), post) =>
        value.toNat == 7 && post.clock == 8
    | _ => false
  directOk && nestedOk

def stateOwnedTimeoutRows : Bool :=
  let call := recursiveExact (.call none (ml "loop") [])
    (recursiveCallCodeState 2)
  let decCall := recursiveExact
    (.decCall (ml "answer") .one (ml "loop") [] .skip)
    (recursiveDecCallCodeState 2)
  let callTimeout := match call with
    | some (some .timeOut, post) => post.clock == 0 && (post.locals (ml "x")).isNone
    | _ => false
  let decCallTimeout := match decCall with
    | some (some .timeOut, post) => post.clock == 0 && (post.locals (ml "x")).isNone
    | _ => false
  callTimeout && decCallTimeout

/-! The outer `none` is the documented fragment gap, not HOL `SOME Error`. -/
def recursiveGapRows : Bool :=
  let seqOpen := evalPanSemRecursiveCallHOLExact (.seq .skip .skip) baseState
  let ifOpen := evalPanSemRecursiveCallHOLExact (.ite (.const 1) .skip .skip) baseState
  let decOpen := evalPanSemRecursiveCallHOLExact
    (.dec (ml "y") .one (.const 1) .skip) baseState
  let assignOpen := evalPanSemRecursiveCallHOLExact
    (.assign .local (ml "x") (.const 2)) baseState
  let whileOpen := evalPanSemRecursiveCallHOLExact (.while (.const 1) .skip) baseState
  seqOpen.isNone && ifOpen.isNone && decOpen.isNone && assignOpen.isNone && whileOpen.isNone

#guard skipBreakTickRows
#guard assignPrimitiveRows
#guard storeRows
#guard returnRaiseRows
#guard sharedMemoryRows
#guard extCallRows
#guard stateOwnedCallRows
#guard stateOwnedDecCallRows
#guard stateOwnedTimeoutRows
#guard recursiveGapRows

def runChecks : IO Bool := do
  if skipBreakTickRows then
    IO.println "PASS exact-state dispatcher Skip/Break/Continue/Tick rows match HOL"
  else IO.println "FAIL exact-state dispatcher Skip/Break/Continue/Tick rows match HOL"
  if assignPrimitiveRows then
    IO.println "PASS exact-state dispatcher Assign/Primitive rows match HOL"
  else IO.println "FAIL exact-state dispatcher Assign/Primitive rows match HOL"
  if storeRows then
    IO.println "PASS exact-state dispatcher Store/Store32/StoreByte rows match HOL"
  else IO.println "FAIL exact-state dispatcher Store/Store32/StoreByte rows match HOL"
  if returnRaiseRows then
    IO.println "PASS exact-state dispatcher Return/Raise rows match HOL"
  else IO.println "FAIL exact-state dispatcher Return/Raise rows match HOL"
  if sharedMemoryRows then
    IO.println "PASS exact-state dispatcher ShMem out-of-domain rows match HOL"
  else IO.println "FAIL exact-state dispatcher ShMem out-of-domain rows match HOL"
  if extCallRows then
    IO.println "PASS exact-state dispatcher ExtCall bad-read row matches HOL"
  else IO.println "FAIL exact-state dispatcher ExtCall bad-read row matches HOL"
  if stateOwnedCallRows then
    IO.println "PASS exact-state recursive Call/nested Call/DecCall/handler rows match original HOL"
  else IO.println "FAIL exact-state recursive Call/nested Call/DecCall/handler rows match original HOL"
  if stateOwnedDecCallRows then
    IO.println "PASS exact-state recursive DecCall and nested DecCall match original HOL"
  else IO.println "FAIL exact-state recursive DecCall and nested DecCall match original HOL"
  if stateOwnedTimeoutRows then
    IO.println "PASS exact-state recursive Call/DecCall timeout clocks match original HOL"
  else IO.println "FAIL exact-state recursive Call/DecCall timeout clocks match original HOL"
  if recursiveGapRows then
    IO.println "PASS exact-state dispatcher keeps unassembled constructors explicitly open"
  else IO.println "FAIL exact-state dispatcher keeps unassembled constructors explicitly open"
  pure (skipBreakTickRows && assignPrimitiveRows && storeRows && returnRaiseRows &&
    sharedMemoryRows && extCallRows && stateOwnedCallRows && stateOwnedDecCallRows &&
    stateOwnedTimeoutRows && recursiveGapRows)

end Flapjack.Test.PanSemTotalEvalExactParity
