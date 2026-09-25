/-
  Direct parity for the exact `panSem$lookup_code` port and the exact `evaluate`
  DecCall clause step over the exact `mlstring`-keyed source state.

  The rows replay `scripts/hol-probes/pan_sem_e2e_probe.out` (`lookup_code_ok`,
  `lookup_code_bad_arg`, `lookup_code_dup_param`, `deccall_clause_ok`,
  `deccall_clause_clock_zero`, `deccall_clause_bad_shape`,
  `deccall_clause_missing_function`).
-/
import Flapjack.Pancake.Semantics.PanSem.DecCallExact

namespace Flapjack.Test.PanSemDecCallExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

/-- The code map used by the rows: function `f` taking one `One` parameter `a`
    and returning it. -/
def codeMap : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  fun name =>
    if name = ml "f" then
      some ([(ml "a", ShapeHOL.one)], ProgHOL.return (.var .local (ml "a")), ShapeHOL.one)
    else none

/-- Duplicate-formal variant used by the `lookup_code_dup_param` row. -/
def duplicateCodeMap : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  fun name =>
    if name = ml "f" then
      some ([(ml "a", ShapeHOL.one), (ml "a", ShapeHOL.one)], ProgHOL.skip, ShapeHOL.one)
    else none

abbrev baseState (clock : Nat) : PanSemStateExact 8 Unit :=
  { locals := fun name => if name = ml "r" then some (.val (.word 0)) else none
    globals := fun _ => none
    structs := []
    code := codeMap
    eshapes := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := clock
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

abbrev missingFunctionState : PanSemStateExact 8 Unit :=
  { baseState 5 with code := fun _ => none }

/-- Evaluate the argument expressions with the exact expression evaluator. -/
def evalArguments (_state : PanSemStateExact 8 Unit) : List (ExpHOL 8) → Option (List (ValueHOL 8))
  | [] => some []
  | .const value :: rest =>
      (evalArguments _state rest).map (fun values => .val (.word value) :: values)
  | _ => none

/-- Body/continuation stub: a `return (var local)` returns the bound value. -/
def evaluateStub (body : ProgHOL 8) (state : PanSemStateExact 8 Unit) :
    Option (PanSemResultExact 8) × PanSemStateExact 8 Unit :=
  match body with
  | .return (.var .local name) => (some (.returned ((state.locals name).getD (.val (.word 0)))), state)
  | _ => (some .error, state)

def isErrorResult (result : Option (PanSemResultExact 8)) : Bool :=
  match result with
  | some .error => true
  | _ => false

def isTimeOutResult (result : Option (PanSemResultExact 8)) : Bool :=
  match result with
  | some .timeOut => true
  | _ => false

def returnedWord (result : Option (PanSemResultExact 8)) : Option Nat :=
  match result with
  | some (.returned (.val (.word value))) => some value.toNat
  | _ => none

def localsWordOf (map : MlS → Option (ValueHOL 8)) (name : MlS) : Option Nat :=
  match map name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def localsWord (state : PanSemStateExact 8 Unit) (name : MlS) : Option Nat :=
  localsWordOf state.locals name

/-- `lookup_code_ok=(T,SOME (ValWord 3w))`. -/
def lookupOkGuard : Bool :=
  match lookupCodeHOLExact codeMap (ml "f") [.val (.word 3)] with
  | some (_, locals, _) => localsWordOf locals (ml "a") == some 3
  | none => false

/-- `lookup_code_bad_arg=(F,NONE)`. -/
def lookupBadArgGuard : Bool := (lookupCodeHOLExact codeMap (ml "f") [.rStruct []]).isNone

/-- `lookup_code_dup_param=(F,NONE)`. -/
def lookupDupParamGuard : Bool :=
  (lookupCodeHOLExact duplicateCodeMap (ml "f") [.val (.word 3)]).isNone

/-- `deccall_clause_ok=(SOME (Return (ValWord 3w)),SOME (ValWord 0w),NONE)`. -/
def decCallOkGuard : Bool :=
  let result := decCallStepHOLExact (baseState 5) (ml "r") ShapeHOL.one (ml "f")
    [.const 3] (ProgHOL.return (.var .local (ml "r"))) evalArguments evaluateStub
  returnedWord result.1 == some 3 && localsWord result.2 (ml "r") == some 0 &&
    (result.2.locals (ml "a")).isNone

/-- `deccall_clause_clock_zero=(SOME TimeOut,NONE,0)`. -/
def decCallClockZeroGuard : Bool :=
  let result := decCallStepHOLExact (baseState 0) (ml "r") ShapeHOL.one (ml "f")
    [.const 3] (ProgHOL.return (.var .local (ml "r"))) evalArguments evaluateStub
  isTimeOutResult result.1 && (result.2.locals (ml "r")).isNone && result.2.clock == 0

/-- `deccall_clause_bad_shape=(SOME Error,NONE)` (the error state keeps the
    callee's locals, so the caller's `r` binding is gone). -/
def decCallBadShapeGuard : Bool :=
  let result := decCallStepHOLExact (baseState 5) (ml "r") (ShapeHOL.comb []) (ml "f")
    [.const 3] (ProgHOL.return (.var .local (ml "r"))) evalArguments evaluateStub
  isErrorResult result.1 && (result.2.locals (ml "r")).isNone

/-- `deccall_clause_missing_function=(SOME Error,SOME (ValWord 0w))`. -/
def decCallMissingFunctionGuard : Bool :=
  let result := decCallStepHOLExact missingFunctionState
    (ml "r") ShapeHOL.one (ml "g") [.const 3] (ProgHOL.return (.var .local (ml "r")))
    evalArguments evaluateStub
  isErrorResult result.1 && localsWord result.2 (ml "r") == some 0

def decCallExactGuard : Bool :=
  lookupOkGuard && lookupBadArgGuard && lookupDupParamGuard && decCallOkGuard &&
    decCallClockZeroGuard && decCallBadShapeGuard && decCallMissingFunctionGuard

-- `lookupCodeHOLExact_of_code_none`: a code map missing the function returns none.
example : lookupCodeHOLExact (width := 8) (fun _ => none) (ml "g")
      [.val (.word (3 : BitVec 8))] = none :=
  lookupCodeHOLExact_of_code_none _ _ _ rfl

#guard lookupOkGuard
#guard lookupBadArgGuard
#guard lookupDupParamGuard
#guard decCallOkGuard
#guard decCallClockZeroGuard
#guard decCallBadShapeGuard
#guard decCallMissingFunctionGuard
#guard decCallExactGuard

def runChecks : IO Bool := do
  if decCallExactGuard then
    IO.println "PASS exact panSem lookup_code/DecCall clause step (7 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem lookup_code/DecCall clause step"
    pure false

end Flapjack.Test.PanSemDecCallExactParity
