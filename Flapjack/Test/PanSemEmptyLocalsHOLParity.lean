import Flapjack.Pancake.Semantics.PanSem.StateExact

/-!
# Direct-HOL parity for the exact `panSem$empty_locals`

Reproduces the original-HOL oracle rows
`scripts/hol-probes/pan_sem_empty_locals_probe.out` for `empty_locals`
over the exact `MlString`-keyed `PanSemStateExact` carrier: the locals map is
cleared while `clock` and `globals` are preserved.
-/

namespace Flapjack.Test.PanSemEmptyLocalsHOLParity

open Flapjack

/-- The faithful HOL `mlstring` of a source string. -/
abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

/-- A concrete exact state with `x` a local `7`, `y` a global `9`, clock 5. -/
def exactState : PanSemStateExact 64 Unit where
  locals := fun name => if name = ml "x" then some (.val (.word 7)) else none
  globals := fun name => if name = ml "y" then some (.val (.word 9)) else none
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

-- HOL `el_lookup = NONE`: the locals map is cleared.
example : (emptyLocalsHOLExact (width := 64) exactState).locals (ml "x") = none := rfl

-- HOL `el_clock = 5`: the clock is preserved.
example : (emptyLocalsHOLExact (width := 64) exactState).clock = 5 := rfl

-- HOL `el_globals = T`: the globals are preserved.
example :
    (emptyLocalsHOLExact (width := 64) exactState).globals (ml "y")
      = exactState.globals (ml "y") := rfl

/-- A Bool mirror of the three oracle rows. -/
def emptyLocalsGuard : Bool :=
  ((emptyLocalsHOLExact (width := 64) exactState).locals (ml "x")).isNone &&
    (emptyLocalsHOLExact (width := 64) exactState).clock == 5 &&
    ((emptyLocalsHOLExact (width := 64) exactState).globals (ml "y")).isSome

#eval emptyLocalsGuard
#guard emptyLocalsGuard

/-- Runs the parity checks. -/
def runChecks : IO Bool := do
  IO.println "PASS panSem empty_locals exact carrier matches all 3 oracle rows"
  pure emptyLocalsGuard

end Flapjack.Test.PanSemEmptyLocalsHOLParity