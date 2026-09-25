import Flapjack.Pancake.Semantics.PanSem.LocalUpdatesExact

/-!
# Direct-HOL parity for the exact `panSem` local/global update helpers

Reproduces the original-HOL oracle rows in
`scripts/hol-probes/pan_sem_set_var_probe.out` (`set_var_*`, `set_global_*`,
`upd_locals_*`) and `scripts/hol-probes/pan_res_var_probe.out`
(`delete_hit`, `delete_other`, `update_hit`) over the exact `MlString`-keyed
`PanSemStateExact` carrier.
-/

namespace Flapjack.Test.PanSemLocalUpdatesExactParity

open Flapjack

/-- The faithful HOL `mlstring` of a source string. -/
abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

/-- Concrete exact state: locals `x = 5`, `y = 7`, global `g = 1`, clock 5. -/
def baseState : PanSemStateExact 64 Unit where
  locals := fun name =>
    if name = ml "x" then some (.val (.word 5))
    else if name = ml "y" then some (.val (.word 7)) else none
  globals := fun name => if name = ml "g" then some (.val (.word 1)) else none
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

/-- A `ValueHOL` result projected to a natural, for guard comparison. -/
def wordOf (result : Option (ValueHOL 64)) : Option Nat :=
  match result with
  | some (.val (.word value)) => some value.toNat
  | _ => none

-- HOL `set_var_new = SOME 9`.
def setVarNew : Bool :=
  wordOf ((setVarHOLExact (width := 64) (ml "z") (.val (.word 9)) baseState).locals (ml "z"))
    == some 9

-- HOL `set_var_overwrite = SOME 9`.
def setVarOverwrite : Bool :=
  wordOf ((setVarHOLExact (width := 64) (ml "x") (.val (.word 9)) baseState).locals (ml "x"))
    == some 9

-- HOL `set_var_other = SOME 7` (unrelated local `y` untouched).
def setVarOther : Bool :=
  wordOf ((setVarHOLExact (width := 64) (ml "x") (.val (.word 9)) baseState).locals (ml "y"))
    == some 7

-- HOL `set_var_globals = SOME 1` (`set_var` does not touch globals).
def setVarGlobals : Bool :=
  wordOf ((setVarHOLExact (width := 64) (ml "x") (.val (.word 9)) baseState).globals (ml "g"))
    == some 1

-- HOL `set_var_clock = s.clock` (the clock is preserved).
def setVarClock : Bool :=
  (setVarHOLExact (width := 64) (ml "x") (.val (.word 9)) baseState).clock == 5

-- HOL `set_global_new = SOME 9`.
def setGlobalNew : Bool :=
  wordOf ((setGlobalHOLExact (width := 64) (ml "h") (.val (.word 9)) baseState).globals (ml "h"))
    == some 9

-- HOL `set_global_locals = SOME 5` (`set_global` does not touch locals).
def setGlobalLocals : Bool :=
  wordOf ((setGlobalHOLExact (width := 64) (ml "h") (.val (.word 9)) baseState).locals (ml "x"))
    == some 5

-- HOL `upd_locals_x = SOME 9`.
def updLocalsX : Bool :=
  wordOf ((updLocalsHOLExact (width := 64) [(ml "x", .val (.word 9))] baseState).locals (ml "x"))
    == some 9

-- HOL `upd_locals_other = NONE` (`upd_locals` starts from `FEMPTY`).
def updLocalsOther : Bool :=
  wordOf ((updLocalsHOLExact (width := 64) [(ml "x", .val (.word 9))] baseState).locals (ml "y"))
    == none

-- HOL `upd_locals_dup = SOME 11` (later duplicate wins).
def updLocalsDup : Bool :=
  wordOf ((updLocalsHOLExact (width := 64)
      [(ml "x", .val (.word 9)), (ml "x", .val (.word 11))] baseState).locals (ml "x"))
    == some 11

-- HOL `delete_hit = NONE`.
def resVarDeleteHit : Bool :=
  wordOf (resVarHOLExact (width := 64) baseState.locals (ml "x", none) (ml "x")) == none

-- HOL `delete_other = SOME (ValWord 3w)` (here local `x` is 5).
def resVarDeleteOther : Bool :=
  wordOf (resVarHOLExact (width := 64) baseState.locals (ml "y", none) (ml "x")) == some 5

-- HOL `update_hit = SOME (ValWord 7w)`.
def resVarUpdateHit : Bool :=
  wordOf (resVarHOLExact (width := 64) baseState.locals (ml "x", some (.val (.word 7))) (ml "x"))
    == some 7

/-- Combined parity check: all 13 direct HOL rows above. -/
def localUpdatesGuard : Bool :=
  setVarNew && setVarOverwrite && setVarOther && setVarGlobals && setVarClock &&
  setGlobalNew && setGlobalLocals &&
  updLocalsX && updLocalsOther && updLocalsDup &&
  resVarDeleteHit && resVarDeleteOther && resVarUpdateHit

#guard localUpdatesGuard

def runChecks : IO Bool := do
  if localUpdatesGuard then
    IO.println
      "PASS exact panSem set_var/set_global/upd_locals/res_var (13 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem local update helpers"
    pure false

end Flapjack.Test.PanSemLocalUpdatesExactParity
