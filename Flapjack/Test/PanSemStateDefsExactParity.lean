import Flapjack.Pancake.Semantics.PanSem.StateDefsExact

/-!
# Parity for the exact `kvar_defs` state-accessor bundle

Replays the direct original-HOL rows in
`scripts/hol-probes/pan_sem_e2e_probe.out`
(`kvar_defs_set_kvar_local`, `kvar_defs_set_global_update`,
`kvar_defs_lookup_global`, `kvar_defs_is_valid_value`) against the exact
`PanSemStateExact` carrier, and exercises each conjunct of the tagged
`kvar_defs` theorem.
-/

namespace Flapjack.Test.PanSemStateDefsExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS)

private abbrev Word8 := RiscV.Word 8

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

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

def wordOfLocal (state : PanSemStateExact 8 Unit) (name : MlS) : Option Nat :=
  match state.locals name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def wordOfGlobal (state : PanSemStateExact 8 Unit) (name : MlS) : Option Nat :=
  match state.globals name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

/-- Conjunct `set_var_def`: `set_var v value s = s with locals := s.locals |+ (v,value)`. -/
example (name : MlS) (value : ValueHOL 8) (state : PanSemStateExact 8 Unit) :
    setVarHOLExact name value state =
      { state with locals := fun current =>
          if current = name then some value else state.locals current } :=
  (kvar_defs (width := 8) (σ := Unit)).1 name value state

/-- Conjunct `set_global_def`: the `globals` counterpart. -/
example (name : MlS) (value : ValueHOL 8) (state : PanSemStateExact 8 Unit) :
    setGlobalHOLExact name value state =
      { state with globals := fun current =>
          if current = name then some value else state.globals current } :=
  (kvar_defs (width := 8) (σ := Unit)).2.1 name value state

/-- Conjunct `set_kvar_def`: the `Local`/`Global` dispatch. -/
example (kind : VarKind) (name : MlS) (value : ValueHOL 8)
    (state : PanSemStateExact 8 Unit) :
    setKvarHOLExact kind name value state =
      match kind with
      | .local => setVarHOLExact name value state
      | .global => setGlobalHOLExact name value state :=
  (kvar_defs (width := 8) (σ := Unit)).2.2.1 kind name value state

/-- Conjunct `lookup_kvar_def`: the `Local`/`Global` dispatch of the lookup. -/
example (kind : VarKind) (name : MlS) (state : PanSemStateExact 8 Unit) :
    lookupKvarHOLExact kind name state =
      match kind with
      | .local => state.locals name
      | .global => state.globals name :=
  (kvar_defs (width := 8) (σ := Unit)).2.2.2.2 kind name state

/-- HOL `kvar_defs_set_kvar_local`: `set_kvar Local v value s = set_var v value s`. -/
example : wordOfLocal (setKvarHOLExact .local (ml "x") (.val (.word 3)) stateA)
    (ml "x") = some 3 := by
  rw [show setKvarHOLExact .local (ml "x") (.val (.word 3)) stateA
        = setVarHOLExact (ml "x") (.val (.word 3)) stateA from
      (kvar_defs (width := 8) (σ := Unit)).2.2.1 .local (ml "x") (.val (.word 3)) stateA]
  simp [setVarHOLExact, wordOfLocal]

/-- HOL `kvar_defs_set_global_update`: `set_global` updates `globals` only. -/
example :
    wordOfGlobal (setGlobalHOLExact (ml "g") (.val (.word 3)) stateA) (ml "g") = some 3
      ∧ wordOfLocal (setGlobalHOLExact (ml "g") (.val (.word 3)) stateA) (ml "x")
        = some 7 := by
  rw [show setGlobalHOLExact (ml "g") (.val (.word 3)) stateA
        = { stateA with globals := fun current =>
            if current = ml "g" then some (.val (.word 3)) else stateA.globals current } from
      (kvar_defs (width := 8) (σ := Unit)).2.1 (ml "g") (.val (.word 3)) stateA]
  refine ⟨?_, ?_⟩ <;> simp [wordOfGlobal, wordOfLocal]

/-- HOL `kvar_defs_lookup_global`: `lookup_kvar Global v s = FLOOKUP s.globals v`. -/
example : lookupKvarHOLExact .global (ml "g") stateA = some (.val (.word 9)) := by
  rw [show lookupKvarHOLExact .global (ml "g") stateA = stateA.globals (ml "g") from
      (kvar_defs (width := 8) (σ := Unit)).2.2.2.2 .global (ml "g") stateA]
  simp

/-- HOL `kvar_defs_is_valid_value`: the bound value matches its own shape. -/
example : isValidValueHOLExact stateA .local (ml "x") (.val (.word 7)) = true := by
  rw [show isValidValueHOLExact stateA .local (ml "x") (.val (.word 7))
        = (match lookupKvarHOLExact .local (ml "x") stateA with
            | some existing =>
                shapeEqHOL (shapeOfHOLExact (.val (.word 7))) (shapeOfHOLExact existing)
            | none => false) from
      (kvar_defs (width := 8) (σ := Unit)).2.2.2.1 stateA .local (ml "x") (.val (.word 7))]
  simp [lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL.eq_def]

def stateDefsGuard : Bool :=
  (wordOfLocal (setVarHOLExact (ml "x") (.val (.word 3)) stateA) (ml "x") == some 3) &&
  (wordOfGlobal (setGlobalHOLExact (ml "g") (.val (.word 3)) stateA) (ml "g") == some 3) &&
  (wordOfLocal (setKvarHOLExact .local (ml "x") (.val (.word 3)) stateA) (ml "x")
      == some 3) &&
  (isValidValueHOLExact stateA .local (ml "x") (.val (.word 7))) &&
  (match lookupKvarHOLExact .global (ml "g") stateA with
    | some (.val (.word v)) => some v.toNat
    | _ => none) == some 9

#eval stateDefsGuard
#guard stateDefsGuard

def runChecks : IO Bool := do
  if stateDefsGuard then
    IO.println "PASS exact panSem kvar_defs state-accessor bundle (4 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem kvar_defs state-accessor bundle"
    pure false

end Flapjack.Test.PanSemStateDefsExactParity
