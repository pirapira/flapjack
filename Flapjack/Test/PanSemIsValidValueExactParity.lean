/-
  Parity for the exact HOL `panSem$is_valid_value` port over the exact
  MlString-keyed state (`Flapjack/Pancake/Semantics/PanSem/IsValidValueExact.lean`).

  Rows reproduced from the committed direct original-HOL probe
  `scripts/hol-probes/pan_sem_is_valid_value_probe.out`
  (`is_valid_value_local_shape=T`, `is_valid_value_global_shape=T`,
  `is_valid_value_mismatch=F`, `is_valid_value_missing=F`), with the base state
  `locals = |+ ("x", ValWord 5w)`, `globals = |+ ("g", ValWord 7w)`.
-/
import Flapjack.Pancake.Semantics.PanSem.IsValidValueExact

namespace Flapjack.Test.PanSemIsValidValueExactParity

open Flapjack

abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

/-- Base state mirroring the HOL probe: `x` local bound to a word, `g` global
bound to a word. -/
def baseState : PanSemStateExact 64 Unit where
  locals := fun name => if name = ml "x" then some (.val (.word 5)) else none
  globals := fun name => if name = ml "g" then some (.val (.word 7)) else none
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

def localShapeGuard : Bool :=
  isValidValueHOLExact baseState .local (ml "x") (.val (.word 9))

def globalShapeGuard : Bool :=
  isValidValueHOLExact baseState .global (ml "g") (.val (.word 9))

def mismatchGuard : Bool :=
  !isValidValueHOLExact baseState .local (ml "x") (.rStruct [])

def missingGuard : Bool :=
  !isValidValueHOLExact baseState .local (ml "missing") (.val (.word 9))

def isValidValueGuard : Bool :=
  localShapeGuard && globalShapeGuard && mismatchGuard && missingGuard

#guard isValidValueGuard

def runChecks : IO Bool := do
  if isValidValueGuard then
    IO.println "PASS exact panSem is_valid_value (4 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem is_valid_value (4 HOL rows)"
    pure false

end Flapjack.Test.PanSemIsValidValueExactParity
