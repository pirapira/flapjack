/-
  Parity for the exact HOL `panSem$evaluate` Call clause step
  (`callStepHOLClause.HOL`).  The guards replay the direct original-HOL rows in
  `scripts/hol-probes/pan_sem_e2e_probe.out`
  (`call_clause_ok_none`, `call_clause_ok_nodest`, `call_clause_ok_dest`,
  `call_clause_bad_shape`, `call_clause_handler`, `call_clause_missing_function`,
  `call_clause_clock_zero`).
-/
import Flapjack.Pancake.Semantics.PanSem.CallExact
import Flapjack.Test.PanValueFfiSemantics

namespace Flapjack.Test.PanSemCallExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := RiscV.Word 8

abbrev callCodeMap : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  fun name =>
    if name = ml "f" then
      some ([(ml "a", .one)], .return (.var .local (ml "a")), .one)
    else if name = ml "g" then
      some ([(ml "a", .one)], .raise (ml "E") (.var .local (ml "a")), .one)
    else none

abbrev badShapeCodeMap : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  fun _ => some ([(ml "a", .one)], .return (.rstruct ([] : List (ExpHOL 8))), .one)

abbrev nullCodeMap : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  fun _ => none

abbrev callState (clock : Nat) : PanSemStateExact 8 Unit where
  locals := fun name =>
    if name = ml "r" then some (.val (.word 0))
    else if name = ml "ev" then some (.val (.word 0))
    else none
  globals := fun _ => none
  structs := []
  code := callCodeMap
  eshapes := fun name => if name = ml "E" then some .one else none
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := clock
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

abbrev missingFunctionState : PanSemStateExact 8 Unit where
  locals := fun name => if name = ml "r" then some (.val (.word 0)) else none
  globals := fun _ => none
  structs := []
  code := nullCodeMap
  eshapes := fun _ => none
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

abbrev badShapeState : PanSemStateExact 8 Unit where
  locals := fun _ => none
  globals := fun _ => none
  structs := []
  code := badShapeCodeMap
  eshapes := fun _ => none
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

abbrev CallInfo := Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 8))

def evalArguments (_state : PanSemStateExact 8 Unit) :
    List (ExpHOL 8) → Option (List (ValueHOL 8))
  | [] => some []
  | expression :: rest =>
      match expression with
      | .const value =>
          match evalArguments _state rest with
          | some values => some (.val (.word value) :: values)
          | none => none
      | _ => none

def evaluateStub :
    ProgHOL 8 → PanSemStateExact 8 Unit →
      Option (PanSemResultExact 8) × PanSemStateExact 8 Unit
  | .return (.var .local name), state =>
      (some (.returned ((state.locals name).getD (.val (.word 0)))), state)
  | .return (.rstruct ([] : List (ExpHOL 8))), state =>
      (some (.returned (.rStruct [])), state)
  | .raise exceptionId (.var .local name), state =>
      (some (.exception exceptionId ((state.locals name).getD (.val (.word 0)))), state)
  | .skip, state => (none, state)
  | _, state => (some .error, state)

def isErrorResult (result : Option (PanSemResultExact 8)) : Bool :=
  match result with
  | some .error => true
  | _ => false

def isTimeOutResult (result : Option (PanSemResultExact 8)) : Bool :=
  match result with
  | some .timeOut => true
  | _ => false

def isNoneResult (result : Option (PanSemResultExact 8)) : Bool :=
  match result with
  | none => true
  | _ => false

def returnedWord (result : Option (PanSemResultExact 8)) : Option Nat :=
  match result with
  | some (.returned (.val (.word value))) => some value.toNat
  | _ => none

def localsWordOf (locals : MlS → Option (ValueHOL 8)) (name : MlS) : Option Nat :=
  match locals name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def callOkNoneGuard : Bool :=
  (returnedWord (callStepHOLExact (callState 5) none (ml "f") [.const 3]
      evalArguments evaluateStub).1 == some 3) &&
    ((localsWordOf (callStepHOLExact (callState 5) none (ml "f") [.const 3]
      evalArguments evaluateStub).2.locals (ml "a")).isNone) &&
    ((localsWordOf (callStepHOLExact (callState 5) none (ml "f") [.const 3]
      evalArguments evaluateStub).2.locals (ml "r")).isNone)

def callOkNoDestGuard : Bool :=
  isNoneResult (callStepHOLExact (callState 5)
    (some (none, none) : CallInfo) (ml "f") [.const 3] evalArguments evaluateStub).1 &&
    localsWordOf (callStepHOLExact (callState 5)
      (some (none, none) : CallInfo) (ml "f") [.const 3]
      evalArguments evaluateStub).2.locals (ml "r") == some 0

def callOkDestGuard : Bool :=
  isNoneResult (callStepHOLExact (callState 5)
    (some (some (.local, ml "r"), none) : CallInfo) (ml "f") [.const 3]
    evalArguments evaluateStub).1 &&
    localsWordOf (callStepHOLExact (callState 5)
      (some (some (.local, ml "r"), none) : CallInfo) (ml "f") [.const 3]
      evalArguments evaluateStub).2.locals (ml "r") == some 3

def callBadShapeGuard : Bool :=
  isErrorResult (callStepHOLExact badShapeState none (ml "f") [.const 3]
    evalArguments evaluateStub).1

def callHandlerGuard : Bool :=
  isNoneResult (callStepHOLExact (callState 5)
    (some (none, some (ml "E", ml "ev", .skip)) : CallInfo) (ml "g") [.const 3]
    evalArguments evaluateStub).1 &&
    localsWordOf (callStepHOLExact (callState 5)
      (some (none, some (ml "E", ml "ev", .skip)) : CallInfo) (ml "g") [.const 3]
      evalArguments evaluateStub).2.locals (ml "ev") == some 3

def callMissingFunctionGuard : Bool :=
  isErrorResult (callStepHOLExact missingFunctionState none (ml "h") [.const 3]
    evalArguments evaluateStub).1 &&
    localsWordOf (callStepHOLExact missingFunctionState none (ml "h") [.const 3]
      evalArguments evaluateStub).2.locals (ml "r") == some 0

def callClockZeroGuard : Bool :=
  isTimeOutResult (callStepHOLExact (callState 0) none (ml "f") [.const 3]
    evalArguments evaluateStub).1 &&
    (localsWordOf (callStepHOLExact (callState 0) none (ml "f") [.const 3]
      evalArguments evaluateStub).2.locals (ml "a")).isNone

def callExactGuard : Bool :=
  callOkNoneGuard && callOkNoDestGuard && callOkDestGuard && callBadShapeGuard &&
    callHandlerGuard && callMissingFunctionGuard && callClockZeroGuard

#eval callOkNoneGuard
#eval callOkNoDestGuard
#eval callOkDestGuard
#eval callBadShapeGuard
#eval callHandlerGuard
#eval callMissingFunctionGuard
#eval callClockZeroGuard
#eval callExactGuard
#guard callExactGuard

def runChecks : IO Bool := do
  if callExactGuard then
    IO.println "PASS exact panSem Call clause step (7 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem Call clause step (7 HOL rows)"
    pure false

end Flapjack.Test.PanSemCallExactParity
