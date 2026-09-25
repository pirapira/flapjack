/-
  Parity for the exact HOL `panSem$Dec`-with-initializer clause over the exact
  MlString-keyed state (`Flapjack/Pancake/Semantics/PanSem/DecExact.lean`).

  Rows reproduced from the committed direct original-HOL probe
  `scripts/hol-probes/pan_sem_e2e_probe.out`:

  * `dec_restores_locals` =
    `(SOME (Return (ValWord 9w)), SOME (ValWord 7w))` for
    `evaluate (Dec "x" One (Const 9w) (Return (Var Local "x")), s)` with
    `s.locals = |+ ("x", ValWord 7w)`;
  * `dec_shape_mismatch` = `SOME Error` for
    `evaluate (Dec "x" One (RStruct []) Skip, s)`.

  The clause is callback-parameterised, so the fixtures below supply the
  initializer evaluation and the body evaluation directly.
-/
import Flapjack.Pancake.Semantics.PanSem.DecExact

namespace Flapjack.Test.PanSemDecExactParity

open Flapjack
open Flapjack.Pancake.PanLang (ExpHOL ProgHOL)

abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

/-- Base state mirroring the HOL probe: local `x` bound to the word `7`. -/
def baseState : PanSemStateExact 64 Unit where
  locals := fun name => if name = ml "x" then some (.val (.word 7)) else none
  globals := fun _ => none
  structs := []
  code := fun _ => none
  eshapes := fun _ => none
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

/-- Initializer evaluator for the fixture: evaluates `Const` (as `ValWord`) and
    `RStruct []` (as an empty record), and fails otherwise. -/
def evalInitializerFixture (_state : PanSemStateExact 64 Unit) (e : ExpHOL 64) :
    Option (ValueHOL 64) :=
  match e with
  | .const value => some (.val (.word value))
  | .rstruct [] => some (.rStruct [])
  | _ => none

/-- Body evaluator for the fixture: `Return (Var Local name)` returns the current
    binding of `name`; anything else errors. -/
def evaluateBodyFixture (_body : ProgHOL 64)
    (state : PanSemStateExact 64 Unit) :
    Option (PanSemResultExact 64) × PanSemStateExact 64 Unit :=
  match _body with
  | .return (.var .local name) => (some (.returned ((state.locals name).getD (.val (.word 0)))), state)
  | _ => (some .error, state)

/-- Project a returned word out of an exact result. -/
def returnedWord (result : Option (PanSemResultExact 64)) : Option Nat :=
  match result with
  | some (.returned (.val (.word value))) => some value.toNat
  | _ => none

def isErrorResult (result : Option (PanSemResultExact 64)) : Bool :=
  match result with
  | some .error => true
  | _ => false

def localsWord (state : PanSemStateExact 64 Unit) (name : String) : Option Nat :=
  match state.locals (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

/-- `dec_restores_locals`: the body sees the new binding (`9`) and afterwards the
    previous binding (`7`) is restored. -/
def decRestoresLocalsGuard : Bool :=
  let result := decStepHOLExact baseState (ml "x") .one (.const 9)
    (.return (.var .local (ml "x"))) evalInitializerFixture evaluateBodyFixture
  returnedWord result.1 == some 9 && localsWord result.2 "x" == some 7

/-- `dec_shape_mismatch`: a well-formed record against the `One` shape errors. -/
def decShapeMismatchGuard : Bool :=
  let result := decStepHOLExact baseState (ml "x") .one (.rstruct [])
    .skip evalInitializerFixture evaluateBodyFixture
  isErrorResult result.1

/-- An initializer-evaluation failure errors. -/
def decInitializerErrorGuard : Bool :=
  let result := decStepHOLExact baseState (ml "x") .one .baseAddr
    .skip evalInitializerFixture evaluateBodyFixture
  isErrorResult result.1

def decExactGuard : Bool :=
  decRestoresLocalsGuard && decShapeMismatchGuard && decInitializerErrorGuard

#guard decExactGuard

def runChecks : IO Bool := do
  if decExactGuard then
    IO.println "PASS exact panSem Dec-with-initializer clause (2 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem Dec-with-initializer clause (2 HOL rows)"
    pure false

end Flapjack.Test.PanSemDecExactParity
