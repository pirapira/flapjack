import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.Test.CrepInlineRelParity

open Flapjack

/-! Executable regression for the exact `crep_inlineProofScript.sml` state
    relations (`state_rel`, `locals_rel`, `locals_strong_rel`) and the
    `locals_rel_dec_clock` preservation theorem ported in
    `Flapjack.Pancake.Proofs.CrepInline`. -/

/-- A concrete 11-field state: locals `0 := 7`, `1 := 9`; empty globals and
    code; constant zero memory; both addresses in the memory domain. -/
def baseState : CrepHolState Nat Unit :=
  { locals := fun n => match n with
      | 0 => some (.word 7)
      | 1 => some (.word 9)
      | _ => none
    globals := fun _ => none
    code := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => true
    shMemaddrs := fun _ => false
    clock := 5
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 100 }

/-- A strict superset of `baseState`'s locals. -/
def weakState : CrepHolState Nat Unit :=
  { baseState with
    locals := fun n => match n with
      | 0 => some (.word 7)
      | 1 => some (.word 9)
      | 2 => some (.word 11)
      | _ => none }

/-- A strict subset of `baseState`'s locals. -/
def subsetState : CrepHolState Nat Unit :=
  { baseState with
    locals := fun n => match n with
      | 0 => some (.word 7)
      | _ => none }

theorem baseState_submap_weak : crepInlineLocalsRel baseState weakState := by
  rintro (_ | _ | _ | n) v h <;> simp_all [baseState, weakState]

theorem subsetState_submap_base : crepInlineLocalsRel subsetState baseState := by
  rintro (_ | _ | n) v h <;> simp_all [baseState, subsetState]

theorem not_baseState_submap_subset : ¬ crepInlineLocalsRel baseState subsetState := by
  intro h
  have hlookup := h 1 (.word 9) (by simp [baseState])
  simp [subsetState] at hlookup

theorem baseState_strong_rel : crepInlineLocalsStrongRel baseState baseState := rfl

theorem not_baseState_strong_weak : ¬ crepInlineLocalsStrongRel baseState weakState := by
  intro h
  have hpoint := congrFun h 2
  simp [baseState, weakState] at hpoint

theorem baseState_state_rel : crepInlineStateRel baseState baseState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem not_baseState_state_rel_other_clock :
    ¬ crepInlineStateRel baseState { baseState with clock := 4 } := by
  intro h
  have hcl := h.2.2.2.2.2.1
  simp [baseState] at hcl

theorem decClock_preserves :
    crepInlineLocalsRel (decCrepHolClock baseState) (decCrepHolClock weakState) ∧
    crepInlineStateRel (decCrepHolClock baseState) (decCrepHolClock weakState) :=
  crepInlineLocalsRel_decClock baseState weakState baseState_submap_weak
    (by
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
      simp [baseState, weakState])

def baseStateGuard : Bool :=
  (decCrepHolClock baseState).clock == 4 &&
    (decCrepHolClock weakState).clock == 4

#guard baseStateGuard

/-- A state differing from `baseState` only in `code`. -/
def codeState : CrepHolState Nat Unit :=
  { baseState with code := fun _ => some ([1], CrepProg.skip) }

theorem baseState_state_rel_code : crepInlineStateRelCode baseState baseState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem state_rel_code_ignores_code : crepInlineStateRelCode baseState codeState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem not_state_rel_code_other_clock :
    ¬ crepInlineStateRelCode baseState { baseState with clock := 4 } := by
  intro h
  have hcl := h.2.2.2.2.1
  simp [baseState] at hcl

theorem localsExtRel_self_holds :
    crepInlineLocalsExtRel baseState weakState baseState weakState :=
  crepInlineLocalsExtRel_self baseState weakState

/-- A run whose states have locals `{0 ↦ 7}` then `{0 ↦ 7, 1 ↦ 9}`. -/
def extA : CrepHolState Nat Unit :=
  { baseState with locals := fun n => match n with
      | 0 => some (.word 7)
      | _ => none }

def extA' : CrepHolState Nat Unit :=
  { extA with locals := fun n => match n with
      | 0 => some (.word 7)
      | 1 => some (.word 9)
      | _ => none }

/-- A run whose locals start differently but add the same `1 ↦ 9`. -/
def extB : CrepHolState Nat Unit :=
  { baseState with locals := fun n => match n with
      | 2 => some (.word 5)
      | _ => none }

def extB' : CrepHolState Nat Unit :=
  { extB with locals := fun n => match n with
      | 1 => some (.word 9)
      | 2 => some (.word 5)
      | _ => none }

/-- A run that adds `1 ↦ 11` instead of `1 ↦ 9`. -/
def extBbad' : CrepHolState Nat Unit :=
  { extB with locals := fun n => match n with
      | 1 => some (.word 11)
      | 2 => some (.word 5)
      | _ => none }

theorem localsExtRel_agree : crepInlineLocalsExtRel extA extB extA' extB' := by
  simp only [crepInlineLocalsExtRel]
  funext n
  cases n with
  | zero => simp [crepHolFdiff, crepHolFdom, extA, extB, extB']
  | succ n =>
      cases n with
      | zero => simp [crepHolFdiff, crepHolFdom, extA, extA', extB, extB']
      | succ n =>
          cases n with
          | zero => simp [crepHolFdiff, crepHolFdom, extA, extA', extB]
          | succ n => simp [crepHolFdiff, crepHolFdom, extA, extA', extB, extB']

theorem not_localsExtRel_disagree : ¬ crepInlineLocalsExtRel extA extB extA' extBbad' := by
  intro h
  have hpoint := congrFun h 1
  simp [crepHolFdiff, crepHolFdom, extA, extA', extB, extBbad'] at hpoint

def runChecks : IO Bool := do
  let relOk ←
    if baseStateGuard then
      IO.println "PASS crep_inline state_rel/locals_rel/locals_strong_rel definitions"
      pure true
    else
      IO.println "FAIL crep_inline state_rel/locals_rel/locals_strong_rel definitions"
      pure false
  IO.println "PASS crep_inline locals_rel_dec_clock preservation"
  IO.println "PASS crep_inline locals_ext_rel/state_rel_code definitions"
  pure relOk

end Flapjack.Test.CrepInlineRelParity
