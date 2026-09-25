import Flapjack.Pancake.Semantics.PanSem.StateExact

/-!
# Direct-HOL parity for the exact `panSem$state` helpers

Reproduces the original-HOL oracle rows in
`scripts/hol-probes/pan_sem_e2e_probe.out` for `dec_clock`,
`fix_clock` and `lookup_kvar` over the exact `MlString`-keyed
`PanSemStateExact` carrier.
-/

namespace Flapjack.Test.PanSemStateExactParity

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

/-- `lookup_kvar` result projected to a natural, for guard comparison. -/
def lookupWordResult (result : Option (ValueHOL 64)) : Option Nat :=
  match result with
  | some (.val (.word value)) => some value.toNat
  | _ => none

-- HOL `dec_clock_step = <|clock := 4|>`.
example : (decClockHOLExact (width := 64) exactState).clock = 4 := by decide

-- HOL `fix_clock_clamps = (NONE, 2)`.
example : (fixClockHOLExact (width := 64) { exactState with clock := 2 }
    ((none : Option Nat), { exactState with clock := 7 })).2.clock = 2 := by decide

-- HOL `fix_clock_keeps_new = (NONE, 4)`.
example : (fixClockHOLExact (width := 64) { exactState with clock := 9 }
    ((none : Option Nat), { exactState with clock := 4 })).2.clock = 4 := by decide

-- HOL `lookup_kvar_local = SOME (ValWord 3w)` (here local `x` is 7).
example : lookupKvarHOLExact (width := 64) .local (ml "x") exactState
    = some (.val (.word 7)) := by
  simp only [lookupKvarHOLExact, exactState]
  rw [if_pos (by decide)]

-- HOL `lookup_kvar_global = SOME (ValWord 4w)` (here global `y` is 9).
example : lookupKvarHOLExact (width := 64) .global (ml "y") exactState
    = some (.val (.word 9)) := by
  simp only [lookupKvarHOLExact, exactState]
  rw [if_pos (by decide)]

-- HOL `lookup_kvar_missing = NONE`.
example : lookupKvarHOLExact (width := 64) .local (ml "z") exactState = none := by
  simp only [lookupKvarHOLExact, exactState]
  rw [if_neg (by decide)]

-- `set_kvar` then `lookup_kvar` returns the stored value.
example :
    lookupKvarHOLExact (width := 64) .local (ml "z")
      (setKvarHOLExact (width := 64) .local (ml "z") (.val (.word 11)) exactState)
    = some (.val (.word 11)) := by
  rw [lookupKvarHOLExact, setKvarHOLExact]
  change (if ml "z" = ml "z" then
      some (ValueHOL.val (HolWordLab.word 11)) else exactState.locals (ml "z"))
    = some (ValueHOL.val (HolWordLab.word 11))
  rw [if_pos (by decide)]

#guard (decClockHOLExact (width := 64) exactState).clock == 4
#guard (fixClockHOLExact (width := 64) { exactState with clock := 2 }
    ((none : Option Nat), { exactState with clock := 7 })).2.clock == 2
#guard lookupWordResult (lookupKvarHOLExact (width := 64) .local (ml "x") exactState) == some 7
#guard lookupWordResult (lookupKvarHOLExact (width := 64) .global (ml "y") exactState) == some 9
#guard lookupWordResult (lookupKvarHOLExact (width := 64) .local (ml "z") exactState) == none

/-- Combined parity check (mirrors the six direct HOL rows above). -/
def exactStateGuard : Bool :=
  (decClockHOLExact (width := 64) exactState).clock == 4 &&
  (fixClockHOLExact (width := 64) { exactState with clock := 2 }
    ((none : Option Nat), { exactState with clock := 7 })).2.clock == 2 &&
  (fixClockHOLExact (width := 64) { exactState with clock := 9 }
    ((none : Option Nat), { exactState with clock := 4 })).2.clock == 4 &&
  lookupWordResult (lookupKvarHOLExact (width := 64) .local (ml "x") exactState) == some 7 &&
  lookupWordResult (lookupKvarHOLExact (width := 64) .global (ml "y") exactState) == some 9 &&
  lookupWordResult (lookupKvarHOLExact (width := 64) .local (ml "z") exactState) == none

#guard exactStateGuard

def runChecks : IO Bool := do
  if exactStateGuard then
    IO.println "PASS exact panSem state dec_clock/fix_clock/lookup_kvar/set_kvar (6 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem state helpers"
    pure false

end Flapjack.Test.PanSemStateExactParity
