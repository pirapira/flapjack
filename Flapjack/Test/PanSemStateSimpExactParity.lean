import Flapjack.Pancake.Semantics.PanSem.StateSimpExact

/-!
# Parity for the exact `panSem` state-accessor simplification lemmas

Reproduces the direct HOL rows `kvar_simps_set_local`, `kvar_simps_lookup_local`,
`is_valid_value_clock_update`, `is_valid_value_memory_update` from
`scripts/hol-probes/pan_sem_e2e_probe.out` (produced by `panSem$EVAL` in
`scripts/hol-probes/pan_sem_e2e_probeScript.sml`), and builds the three tagged
exact theorems `kvar_simps`, `is_valid_value_simps`, `is_valid_value_simps2`
(`StateSimpExact.lean`).
-/

namespace Flapjack.Test.PanSemStateSimpExactParity

open Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := RiscV.Word 8

abbrev stateA : PanSemStateExact 8 Unit where
  locals := fun name => if name = ml "x" then some (.val (.word 7)) else none
  globals := fun name => if name = ml "g" then some (.val (.word 9)) else none
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

abbrev stateClock : PanSemStateExact 8 Unit := { stateA with clock := 9 }

abbrev stateMemory : PanSemStateExact 8 Unit := { stateA with memory := fun address => .word address }

/-- Word projection of an exact local/global lookup (the carrier `ValueHOL`
    derives only `Repr`, so guards compare projected `Nat`s). -/
def wordOfLocal (state : PanSemStateExact 8 Unit) (name : MlS) : Option Nat :=
  match state.locals name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def kvarSetLocalGuard : Bool :=
  wordOfLocal (setKvarHOLExact .local (ml "x") (.val (.word 3)) stateA) (ml "x") == some 3

def kvarLookupLocalGuard : Bool :=
  wordOfLocal stateA (ml "x") == some 7

def is_valid_value_clock_updateGuard : Bool :=
  (isValidValueHOLExact stateClock .local (ml "x") (.val (.word 7)) == true)
    && (isValidValueHOLExact stateA .local (ml "x") (.val (.word 7)) == true)

def is_valid_value_memory_updateGuard : Bool :=
  (isValidValueHOLExact stateMemory .local (ml "x") (.val (.word 7)) == true)
    && (isValidValueHOLExact stateA .local (ml "x") (.val (.word 7)) == true)

def stateSimpGuard : Bool :=
  kvarSetLocalGuard
    && (kvarLookupLocalGuard
      && (is_valid_value_clock_updateGuard && is_valid_value_memory_updateGuard))

example : setKvarHOLExact .local (ml "x") (.val (.word 3)) stateA
    = setVarHOLExact (ml "x") (.val (.word 3)) stateA :=
  (kvar_simps (width := 8) (ml "x") (.val (.word 3)) stateA).1

example : lookupKvarHOLExact .local (ml "x") stateA = stateA.locals (ml "x") :=
  (kvar_simps (width := 8) (ml "x") (.val (.word 3)) stateA).2.2.1

example : isValidValueHOLExact stateA .local (ml "x") (.val (.word 7))
    = (match stateA.locals (ml "x") with
        | some existing => shapeEqHOL (shapeOfHOLExact (width := 8) (.val (.word 7))) (shapeOfHOLExact existing)
        | none => false) :=
  (is_valid_value_simps (width := 8) stateA (ml "x") (.val (.word 7))).1

example : lookupKvarHOLExact .global (ml "g") { stateA with memory := fun address => .word address }
    = lookupKvarHOLExact .global (ml "g") stateA :=
  (is_valid_value_simps2 (width := 8) stateA .global (ml "g") (.val (.word 7)) 5
      stateA.ffi stateA.code (fun address => .word address)).2.2.2.2.2.2.2

#guard kvarSetLocalGuard
#guard kvarLookupLocalGuard
#guard is_valid_value_clock_updateGuard
#guard is_valid_value_memory_updateGuard
#guard stateSimpGuard

def runChecks : IO Bool := do
  if stateSimpGuard then
    IO.println "PASS exact panSem kvar_simps/is_valid_value_simps/is_valid_value_simps2 (4 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem kvar_simps/is_valid_value_simps/is_valid_value_simps2"
    pure false

end Flapjack.Test.PanSemStateSimpExactParity
