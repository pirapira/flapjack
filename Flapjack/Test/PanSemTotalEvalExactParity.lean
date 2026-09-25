import Flapjack.Pancake.Semantics.PanSem.TotalEvalExact
import Flapjack.Test.PanSemExtCallExactParity

/-! Direct original-HOL rows for the exact-state PanSem dispatcher fragment.
    Call/DecCall cases correspond to `call_code_map_7`,
    `recursive_call_code_map_7`, `deccall_code_map_7`,
    `nested_deccall_code_map_7`, `recursive_call_bad_return_shape`,
    `recursive_deccall_bad_declared_shape`, `recursive_call_callee_skip`,
    `recursive_call_callee_break`, `recursive_call_nonmatching_exception_handler`,
    `recursive_call_invalid_exception_target`,
    `recursive_deccall_exception_propagates`,
    `while_cond_zero`, `while_timeout`, `while_break`, `while_skip_timeout`,
    `while_continue_timeout`, `while_return_propagates`,
    `recursive_seq_call_normal_continue`, `recursive_seq_call_terminal_error`,
    and recursive timeout rows in
    `scripts/hol-probes/pan_sem_e2e_probe.out`; matching exception handling
    corresponds to `call_handles_exception_7`. If rows correspond to
    `exact_if_nonzero_*`, `exact_if_zero_*`, `exact_if_nonword_*`, and
    `exact_if_failed_*` in `pan_sem_ite_e2e_probe.out`. Dec success, shape
    mismatch, missing old binding, and Break restoration correspond to the
    `dec_*` rows in `pan_sem_e2e_probe.out`. -/

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

private def whileClockState (clock : Nat) : PanSemStateExact 64 Unit :=
  { baseState with clock := clock }

private instance (clock : Nat) : DecidablePred (whileClockState clock).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (whileClockState clock).shMemaddrs := by
  intro address
  change Decidable (baseState.shMemaddrs address)
  infer_instance

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

private def callControlState (clock : Nat) : PanSemStateExact 64 Unit :=
  { idCodeState clock with
    code := fun name =>
      if name = ml "skip" then some ([], .skip, .one)
      else if name = ml "break" then some ([], .break, .one)
      else if name = ml "continue" then some ([], .continue, .one)
      else if name = ml "raiseF" then
        some ([], .raise (ml "F") (.const 7), .one)
      else if name = ml "raiseE" then
        some ([], .raise (ml "E") (.const 7), .one)
      else none
    eshapes := fun name =>
      if name = ml "E" || name = ml "F" then some .one else none }

private def existingLocalDecCallState (clock : Nat) : PanSemStateExact 64 Unit :=
  { idCodeState clock with
    locals := fun name =>
      if name = ml "answer" then some (.val (.word 3))
      else (idCodeState clock).locals name }

private instance (clock : Nat) : DecidablePred (idCodeState clock).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (idCodeState clock).shMemaddrs := by
  intro address
  change Decidable (baseState.shMemaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (callControlState clock).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (callControlState clock).shMemaddrs := by
  intro address
  change Decidable (baseState.shMemaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (existingLocalDecCallState clock).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) : DecidablePred (existingLocalDecCallState clock).shMemaddrs := by
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

private def badReturnCodeState (clock : Nat) (returnShape : Flapjack.Pancake.PanLang.ShapeHOL) :
    PanSemStateExact 64 Unit :=
  { baseState with
    locals := fun name => if name = ml "keep" then some (.val (.word 42)) else none
    code := fun name =>
      if name = ml "bad" then
        some ([], .return (.const 7), returnShape)
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

private instance (clock : Nat) (returnShape : Flapjack.Pancake.PanLang.ShapeHOL) :
    DecidablePred (badReturnCodeState clock returnShape).memaddrs := by
  intro address
  change Decidable (baseState.memaddrs address)
  infer_instance

private instance (clock : Nat) (returnShape : Flapjack.Pancake.PanLang.ShapeHOL) :
    DecidablePred (badReturnCodeState clock returnShape).shMemaddrs := by
  intro address
  change Decidable (baseState.shMemaddrs address)
  infer_instance

private def recursiveExact
    (program : ProgHOL 64) (state : PanSemStateExact 64 Unit)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs] :=
  evalPanSemRecursiveCallHOLExact program state

private def recursiveExact8
    (program : ProgHOL 8) (state : PanSemStateExact 8 Unit)
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

private def returnedExtCallState : PanSemStateExact 8 Unit :=
  PanSemExtCallExactParity.baseState returningFfi memory8 domain8

private instance : DecidablePred returnedExtCallState.memaddrs := by
  intro address
  dsimp [returnedExtCallState, PanSemExtCallExactParity.baseState, domain8]
  infer_instance

private instance : DecidablePred returnedExtCallState.shMemaddrs := by
  intro address
  dsimp [returnedExtCallState, PanSemExtCallExactParity.baseState]
  infer_instance

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
  let recursiveAssignOk := match recursiveExact
      (.assign .local (ml "x") (.const 9)) baseState with
    | some (none, state) => localWord state "x" == some 9
    | _ => false
  let recursiveAssignError := match recursiveExact
      (.assign .local (ml "x") (.var .local (ml "missing"))) baseState with
    | some (some .error, state) => localWord state "x" == some 7 && state.clock == 5
    | _ => false
  assignOk && primitiveOk && recursiveAssignOk && recursiveAssignError

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

/-! Direct recursive-dispatch checks for the HOL `store_clause_hit` and
`store_clause_out_of_domain` rows in `pan_sem_e2e_probe.out`. -/
def recursiveStoreRows : Bool :=
  let storeOk := match recursiveExact (.store (.const 0) (.const 7)) baseState with
    | some (none, state) => memoryWord state 0 == some 7
    | _ => false
  let outside := { baseState with memaddrs := fun _ => False }
  let storeErr := match recursiveExact (.store (.const 0) (.const 7)) outside with
    | some (some .error, state) => memoryWord state 0 == some 0
    | _ => false
  storeOk && storeErr

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

/-! The recursive dispatcher must return the exact ExtCall clause result and
thread its post-state through the context. These guards reuse the original
HOL `extcall_clause_returned` and `extcall_clause_bad_read` rows. -/
def recursiveExtCallRows : Bool :=
  let program : ProgHOL 8 :=
    .extCall (ml "x") (.const 0) (.const 2) (.const 0) (.const 2)
  let returned := recursiveExact8 program returnedExtCallState
  let badRead := recursiveExact8 program badReadState
  let returnedOk := match returned with
    | some (none, state) =>
        match state.memory 0 with
        | .word byte => byte.toNat == 0x42
    | _ => false
  let badReadOk := match badRead with
    | some (some .error, state) =>
        match state.memory 0 with
        | .word byte => byte.toNat == 0xAB
    | _ => false
  returnedOk && badReadOk

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

def stateOwnedCallNegativeRows : Bool :=
  let mismatchedReturn := recursiveExact (.call none (ml "bad") [])
    (badReturnCodeState 10 (.comb []))
  match mismatchedReturn with
  | some (some .error, post) => post.clock == 9 && (post.locals (ml "keep")).isNone
  | _ => false

def stateOwnedCallDestinationRows : Bool :=
  let assigned := recursiveExact
    (.call (some (some (.local, ml "answer"), none)) (ml "id") [.const 7])
    (existingLocalDecCallState 10)
  let rejected := recursiveExact
    (.call (some (some (.local, ml "answer"), none)) (ml "id") [.const 7])
    { existingLocalDecCallState 10 with
      locals := fun name =>
        if name == ml "answer" then some (.rStruct [])
        else (existingLocalDecCallState 10).locals name }
  let assignedOk := match assigned with
    | some (none, post) => post.clock == 9 && localWord post "answer" == some 7
    | _ => false
  let rejectedOk := match rejected with
    | some (some .error, post) => post.clock == 9 && (post.locals (ml "answer")).isNone
    | _ => false
  assignedOk && rejectedOk

def stateOwnedCallControlNegativeRows : Bool :=
  let skip := recursiveExact (.call none (ml "skip") []) (callControlState 10)
  let breakCase := recursiveExact (.call none (ml "break") []) (callControlState 10)
  let continueCase := recursiveExact (.call none (ml "continue") []) (callControlState 10)
  let skipOk := match skip with
    | some (some .error, post) => post.clock == 9 && (post.locals (ml "x")).isNone
    | _ => false
  let breakOk := match breakCase with
    | some (some .error, post) => post.clock == 9 && (post.locals (ml "x")).isNone
    | _ => false
  let continueOk := match continueCase with
    | some (some .error, post) => post.clock == 9 && (post.locals (ml "x")).isNone
    | _ => false
  skipOk && breakOk && continueOk

def stateOwnedCallExceptionNegativeRows : Bool :=
  let nonmatching := recursiveExact
    (.call (some (none, some (ml "E", ml "ev", .skip))) (ml "raiseF") [])
    (callControlState 10)
  let invalidTargetState := { callControlState 10 with
    locals := fun name =>
      if name = ml "ev" then some (.rStruct []) else (callControlState 10).locals name }
  let invalidTarget := recursiveExact
    (.call (some (none, some (ml "E", ml "ev", .skip))) (ml "raiseE") [])
    invalidTargetState
  let nonmatchingOk := match nonmatching with
    | some (some (.exception name (.val (.word value))), post) =>
        name == ml "F" && value.toNat == 7 && post.clock == 9 &&
          (post.locals (ml "ev")).isNone
    | _ => false
  let invalidTargetOk := match invalidTarget with
    | some (some .error, post) => post.clock == 9 && (post.locals (ml "ev")).isNone
    | _ => false
  nonmatchingOk && invalidTargetOk

def stateOwnedSeqCallRows : Bool :=
  let normal := recursiveExact
    (.seq
      (.call (some (none, none)) (ml "id") [.const 7])
      (.return (.const 9))) (idCodeState 10)
  let terminal := recursiveExact
    (.seq
      (.call (some (none, none)) (ml "skip") [])
      (.return (.const 9))) (callControlState 10)
  let normalOk := match normal with
    | some (some (.returned (.val (.word value))), post) =>
        value.toNat == 9 && post.clock == 9 && (post.locals (ml "x")).isNone
    | _ => false
  let terminalOk := match terminal with
    | some (some .error, post) => post.clock == 9 && (post.locals (ml "x")).isNone
    | _ => false
  normalOk && terminalOk

def stateOwnedDecCallExceptionRows : Bool :=
  let propagated := recursiveExact
    (.decCall (ml "answer") .one (ml "raiseE") [] .skip) (callControlState 10)
  match propagated with
  | some (some (.exception name (.val (.word value))), post) =>
      name == ml "E" && value.toNat == 7 && post.clock == 9 &&
        (post.locals (ml "x")).isNone
  | _ => false

def stateOwnedDecCallControlNegativeRows : Bool :=
  let skipCase := recursiveExact
    (.decCall (ml "answer") .one (ml "skip") [] .skip) (callControlState 10)
  let breakCase := recursiveExact
    (.decCall (ml "answer") .one (ml "break") [] .skip) (callControlState 10)
  let continueCase := recursiveExact
    (.decCall (ml "answer") .one (ml "continue") [] .skip) (callControlState 10)
  let isErrorWithCalleeState result :=
    match result with
    | some (some .error, post) => post.clock == 9 && (post.locals (ml "x")).isNone
    | _ => false
  isErrorWithCalleeState skipCase && isErrorWithCalleeState breakCase &&
    isErrorWithCalleeState continueCase

def stateOwnedLookupErrorRows : Bool :=
  let missingCall := recursiveExact (.call none (ml "missing") []) baseState
  let missingDecCall := recursiveExact
    (.decCall (ml "answer") .one (ml "missing") [] .skip) baseState
  let callOk := match missingCall with
    | some (some .error, post) => post.clock == 5 && localWord post "x" == some 7
    | _ => false
  let decCallOk := match missingDecCall with
    | some (some .error, post) => post.clock == 5 && localWord post "x" == some 7
    | _ => false
  let badCallArgument := recursiveExact
    (.call none (ml "id") [.var .local (ml "absent")]) (idCodeState 10)
  let badDecCallArgument := recursiveExact
    (.decCall (ml "answer") .one (ml "id") [.var .local (ml "absent")] .skip)
    (idCodeState 10)
  let callArgumentOk := match badCallArgument with
    | some (some .error, post) => post.clock == 10 && localWord post "x" == some 7
    | _ => false
  let decCallArgumentOk := match badDecCallArgument with
    | some (some .error, post) => post.clock == 10 && localWord post "x" == some 7
    | _ => false
  callOk && decCallOk && callArgumentOk && decCallArgumentOk

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
  let restoresExistingLocal := recursiveExact
    (.decCall (ml "answer") .one (ml "id") [.const 7]
      (.return (.var .local (ml "answer")))) (existingLocalDecCallState 10)
  let restoreOk := match restoresExistingLocal with
    | some (some (.returned (.val (.word value))), post) =>
        value.toNat == 7 && post.clock == 9 && localWord post "answer" == some 3
    | _ => false
  directOk && nestedOk && restoreOk

def stateOwnedDecCallNegativeRows : Bool :=
  let mismatchedDeclaredShape := recursiveExact
    (.decCall (ml "answer") (.comb []) (ml "bad") [] .skip)
    (badReturnCodeState 10 .one)
  match mismatchedDeclaredShape with
  | some (some .error, post) => post.clock == 9 && (post.locals (ml "keep")).isNone
  | _ => false

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

/-- The recursive dispatcher routes Primitive through the reviewed HOL clause.
    The successful `primitive_success` and invalid-arity `primitive_wrong_args`
    cases are direct rows from `pan_sem_e2e_probe.out`. -/
def recursivePrimitiveRows : Bool :=
  let success := evalPanSemRecursiveCallHOLExact
    (.primitive (ml "x") .addCarry [.const 40, .const 50, .const 0]) primitiveState
  let wrongArity := evalPanSemRecursiveCallHOLExact
    (.primitive (ml "x") .addCarry [.const 1, .const 2]) primitiveState
  let successOk := match success with
    | some (none, post) =>
        match post.locals (ml "x") with
        | some (.rStruct [.val (.word sum), .val (.word carry)]) =>
            sum.toNat == 90 && carry.toNat == 0
        | _ => false
    | _ => false
  let wrongArityOk := match wrongArity with
    | some (some .error, post) =>
        match post.locals (ml "x") with
        | some (.rStruct [.val (.word first), .val (.word second)]) =>
            first.toNat == 0 && second.toNat == 0 && post.clock == 5
        | _ => false
    | _ => false
  successOk && wrongArityOk

/-- Direct original-HOL While equations for false/true conditions, recursive
    normal and Continue iterations to timeout, Break exit, terminal Return, and
    failed condition evaluation. -/
def recursiveWhileRows : Bool :=
  let falseCondition := recursiveExact (.while (.const 0) .skip) baseState
  let timeout := recursiveExact (.while (.const 1) .skip) (whileClockState 0)
  let breakExit := recursiveExact (.while (.const 1) .break) baseState
  let normalRecursion := recursiveExact (.while (.const 1) .skip) (whileClockState 1)
  let continueRecursion := recursiveExact (.while (.const 1) .continue) (whileClockState 1)
  let returnPropagation := recursiveExact
    (.while (.const 1) (.return (.const 9))) baseState
  let conditionFailure := recursiveExact
    (.while (.var .local (ml "missing")) .skip) baseState
  let falseOk := match falseCondition with
    | some (none, post) => post.clock == 5 && localWord post "x" == some 7
    | _ => false
  let timeoutOk := match timeout with
    | some (some .timeOut, post) => post.clock == 0 && localWord post "x" == none
    | _ => false
  let breakOk := match breakExit with
    | some (none, post) => post.clock == 4 && localWord post "x" == some 7
    | _ => false
  let normalOk := match normalRecursion with
    | some (some .timeOut, post) => post.clock == 0 && localWord post "x" == none
    | _ => false
  let continueOk := match continueRecursion with
    | some (some .timeOut, post) => post.clock == 0 && localWord post "x" == none
    | _ => false
  let returnOk := match returnPropagation with
    | some (some (.returned (.val (.word value))), post) =>
        value.toNat == 9 && post.clock == 4 && localWord post "x" == none
    | _ => false
  let failureOk := match conditionFailure with
    | some (some .error, post) => post.clock == 5 && localWord post "x" == some 7
    | _ => false
  falseOk && timeoutOk && breakOk && normalOk && continueOk && returnOk && failureOk

/-- The direct HOL rows `exact_if_nonzero_*`, `exact_if_zero_*`,
    `exact_if_nonword_*`, and `exact_if_failed_*` exercise selected branches
    and the state-preserving Error case in the exact recursive dispatcher. -/
def recursiveIfRows : Bool :=
  let nonzero := recursiveExact
    (.ite (.const 1) .tick .skip) baseState
  let zero := recursiveExact
    (.ite (.const 0) .tick .skip) baseState
  let nonword := recursiveExact
    (.ite (.rstruct []) .tick .skip) baseState
  let failed := recursiveExact
    (.ite (.var .local (ml "missing")) .tick .skip)
    baseState
  let nonzeroOk := match nonzero with
    | some (none, post) => post.clock == 4 && localWord post "x" == some 7
    | _ => false
  let zeroOk := match zero with
    | some (none, post) => post.clock == 5 && localWord post "x" == some 7
    | _ => false
  let nonwordOk := match nonword with
    | some (some .error, post) => post.clock == 5 && localWord post "x" == some 7
    | _ => false
  let failedOk := match failed with
    | some (some .error, post) => post.clock == 5 && localWord post "x" == some 7
    | _ => false
  nonzeroOk && zeroOk && nonwordOk && failedOk

/-- Exact recursive `Dec` checks against original HOL's successful local
    restoration and shape-mismatch rows. -/
def recursiveDecRows : Bool :=
  let success := recursiveExact
    (.dec (ml "x") .one (.const 9)
      (.return (.var .local (ml "x")))) baseState
  let missingOld := recursiveExact
    (.dec (ml "fresh") .one (.const 9) .skip) baseState
  let breakBody := recursiveExact
    (.dec (ml "x") .one (.const 9) .break) baseState
  let mismatch := recursiveExact
    (.dec (ml "x") (.comb []) (.const 9) .skip) baseState
  let initializerFailure := recursiveExact
    (.dec (ml "x") .one (.var .local (ml "missing")) .skip) baseState
  let successOk := match success with
    | some (some (.returned (.val (.word value))), post) =>
        value.toNat == 9 && localWord post "x" == some 7
    | _ => false
  let missingOldOk := match missingOld with
    | some (none, post) => localWord post "fresh" == none && localWord post "x" == some 7
    | _ => false
  let breakBodyOk := match breakBody with
    | some (some .break, post) => localWord post "x" == some 7
    | _ => false
  let mismatchOk := match mismatch with
    | some (some .error, post) => post.clock == 5 && localWord post "x" == some 7
    | _ => false
  let initializerFailureOk := match initializerFailure with
    | some (some .error, post) => post.clock == 5 && localWord post "x" == some 7
    | _ => false
  successOk && missingOldOk && breakBodyOk && mismatchOk && initializerFailureOk

#guard skipBreakTickRows
#guard assignPrimitiveRows
#guard storeRows
#guard recursiveStoreRows
#guard returnRaiseRows
#guard sharedMemoryRows
#guard extCallRows
#guard recursiveExtCallRows
#guard stateOwnedCallRows
#guard stateOwnedCallNegativeRows
#guard stateOwnedCallDestinationRows
#guard stateOwnedCallControlNegativeRows
#guard stateOwnedCallExceptionNegativeRows
#guard stateOwnedSeqCallRows
#guard stateOwnedLookupErrorRows
#guard stateOwnedDecCallRows
#guard stateOwnedDecCallNegativeRows
#guard stateOwnedDecCallExceptionRows
#guard stateOwnedDecCallControlNegativeRows
#guard stateOwnedTimeoutRows
#guard recursiveIfRows
#guard recursiveWhileRows
#guard recursiveDecRows
#guard recursivePrimitiveRows

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
  if recursiveStoreRows then
    IO.println "PASS exact-state recursive Store hit/out-of-domain rows match HOL"
  else IO.println "FAIL exact-state recursive Store hit/out-of-domain rows match HOL"
  if returnRaiseRows then
    IO.println "PASS exact-state dispatcher Return/Raise rows match HOL"
  else IO.println "FAIL exact-state dispatcher Return/Raise rows match HOL"
  if sharedMemoryRows then
    IO.println "PASS exact-state dispatcher ShMem out-of-domain rows match HOL"
  else IO.println "FAIL exact-state dispatcher ShMem out-of-domain rows match HOL"
  if extCallRows then
    IO.println "PASS exact-state dispatcher ExtCall bad-read row matches HOL"
  else IO.println "FAIL exact-state dispatcher ExtCall bad-read row matches HOL"
  if recursiveExtCallRows then
    IO.println "PASS exact-state recursive ExtCall returned/bad-read rows match HOL"
  else IO.println "FAIL exact-state recursive ExtCall returned/bad-read rows match HOL"
  if stateOwnedCallRows then
    IO.println "PASS exact-state recursive Call/nested Call/DecCall/handler rows match original HOL"
  else IO.println "FAIL exact-state recursive Call/nested Call/DecCall/handler rows match original HOL"
  if stateOwnedCallNegativeRows then
    IO.println "PASS exact-state recursive Call rejects a callee return-shape mismatch with the callee state"
  else IO.println "FAIL exact-state recursive Call rejects a callee return-shape mismatch with the callee state"
  if stateOwnedCallDestinationRows then
    IO.println "PASS exact-state recursive Call assigns valid destinations and rejects shape mismatches"
  else IO.println "FAIL exact-state recursive Call assigns valid destinations and rejects shape mismatches"
  if stateOwnedCallControlNegativeRows then
    IO.println "PASS exact-state recursive Call maps callee Skip/Break/Continue to Error with callee state"
  else IO.println "FAIL exact-state recursive Call maps callee Skip/Break/Continue to Error with callee state"
  if stateOwnedCallExceptionNegativeRows then
    IO.println "PASS exact-state recursive Call preserves unmatched exceptions and rejects invalid handler targets"
  else IO.println "FAIL exact-state recursive Call preserves unmatched exceptions and rejects invalid handler targets"
  if stateOwnedSeqCallRows then
    IO.println "PASS exact-state Seq clamps the Call state, continues on NONE, and propagates terminal errors"
  else IO.println "FAIL exact-state Seq clamps the Call state, continues on NONE, and propagates terminal errors"
  if stateOwnedLookupErrorRows then
    IO.println "PASS exact-state recursive Call/DecCall missing-code errors preserve the caller state"
  else IO.println "FAIL exact-state recursive Call/DecCall missing-code errors preserve the caller state"
  if stateOwnedDecCallRows then
    IO.println "PASS exact-state recursive DecCall and nested DecCall match original HOL"
  else IO.println "FAIL exact-state recursive DecCall and nested DecCall match original HOL"
  if stateOwnedDecCallNegativeRows then
    IO.println "PASS exact-state recursive DecCall rejects a declared return-shape mismatch with the callee state"
  else IO.println "FAIL exact-state recursive DecCall rejects a declared return-shape mismatch with the callee state"
  if stateOwnedDecCallExceptionRows then
    IO.println "PASS exact-state recursive DecCall propagates callee exceptions and clears locals"
  else IO.println "FAIL exact-state recursive DecCall propagates callee exceptions and clears locals"
  if stateOwnedDecCallControlNegativeRows then
    IO.println "PASS exact-state recursive DecCall maps callee Skip/Break/Continue to Error with callee state"
  else IO.println "FAIL exact-state recursive DecCall maps callee Skip/Break/Continue to Error with callee state"
  if stateOwnedTimeoutRows then
    IO.println "PASS exact-state recursive Call/DecCall timeout clocks match original HOL"
  else IO.println "FAIL exact-state recursive Call/DecCall timeout clocks match original HOL"
  if recursiveIfRows then
    IO.println "PASS exact-state recursive If selects nonzero/zero branches and preserves state on Error"
  else IO.println "FAIL exact-state recursive If selects nonzero/zero branches and preserves state on Error"
  if recursiveWhileRows then
    IO.println "PASS exact-state recursive While matches HOL clock, body, Break, Continue, and terminal-result clauses"
  else IO.println "FAIL exact-state recursive While matches HOL clock, body, Break, Continue, and terminal-result clauses"
  if recursiveDecRows then
    IO.println "PASS exact-state recursive Dec matches HOL initializer, body, shape, control, and local restoration rows"
  else IO.println "FAIL exact-state recursive Dec matches HOL initializer, body, shape, control, and local restoration rows"
  if recursivePrimitiveRows then
    IO.println "PASS exact recursive dispatcher Primitive rows match HOL"
  else IO.println "FAIL exact recursive dispatcher Primitive rows match HOL"
  pure (skipBreakTickRows && assignPrimitiveRows && storeRows && returnRaiseRows &&
    sharedMemoryRows && extCallRows && recursiveStoreRows && stateOwnedCallRows && stateOwnedCallNegativeRows &&
    stateOwnedCallDestinationRows &&
    stateOwnedCallControlNegativeRows && stateOwnedCallExceptionNegativeRows &&
    stateOwnedSeqCallRows && stateOwnedLookupErrorRows &&
    stateOwnedDecCallRows && stateOwnedDecCallNegativeRows &&
    stateOwnedDecCallExceptionRows && stateOwnedDecCallControlNegativeRows &&
    stateOwnedTimeoutRows && recursiveIfRows && recursiveWhileRows && recursiveDecRows &&
    recursivePrimitiveRows)

end Flapjack.Test.PanSemTotalEvalExactParity
