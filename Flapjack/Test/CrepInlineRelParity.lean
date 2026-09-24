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

/-- A finite inline map with one callee `f` whose body is `Skip`. -/
def codeInlFmap : CrepInlineFmap Nat :=
  CrepInlineFmap.insert "f" ([7], CrepProg.skip) CrepInlineFmap.empty

def codeInlSource : CrepHolState Nat Unit :=
  { baseState with code := fun _ => some ([7], CrepProg.skip) }

def codeInlTarget : CrepHolState Nat Unit :=
  { baseState with
    code := fun _ => some ([7], crepInlineProgFmap codeInlFmap CrepProg.skip) }

def codeInlEmptyTarget : CrepHolState Nat Unit :=
  { baseState with code := fun _ => none }

theorem codeInlRel_positive :
    crepInlineCodeInlRel codeInlFmap codeInlSource codeInlTarget := by
  apply crepInlineCodeInlRel_of_code
  intro fname args prog hcode
  simp [codeInlSource] at hcode
  obtain ⟨rfl, rfl⟩ := hcode
  simp [codeInlTarget]

theorem codeInlRel_negative :
    ¬ crepInlineCodeInlRel codeInlFmap codeInlSource codeInlEmptyTarget :=
  not_crepInlineCodeInlRel_of_target_none codeInlFmap codeInlSource
    codeInlEmptyTarget "f" [7] CrepProg.skip
    (by simp [codeInlSource]) (by simp [codeInlEmptyTarget])

def codeInlGuard : Bool :=
  (codeInlSource.code "f").isSome && (codeInlTarget.code "f").isSome &&
    (codeInlEmptyTarget.code "f").isNone

/-! ## Expression-evaluation invariance (`eval_code_inl`) over the canonical word -/

/-- A concrete 11-field state over `RiscV.Word 64` with locals `0 := 7`. -/
def evalBase : CrepHolState (RiscV.Word 64) Unit :=
  { locals := fun n => if n == 0 then some (.word 7) else none
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

/-- The empty inline finite map. -/
def evalInlineFmap : CrepInlineFmap (RiscV.Word 64) := CrepInlineFmap.empty

theorem evalCodeInl_hcode :
    crepInlineCodeInlRel evalInlineFmap evalBase evalBase := by
  apply crepInlineCodeInlRel_of_code
  intro fname args prog hcode
  simp [evalBase] at hcode

example : crepHolFdom evalBase.code = crepHolFdom evalBase.code := rfl

example (n : FunName) (hn : crepHolFdom evalBase.code n = true) :
    crepHolFdom evalBase.code n = true :=
  crepInlineCodeInlRel_fdom_subset evalInlineFmap evalBase evalBase
    evalCodeInl_hcode n hn

example :
    (∀ n, crepHolFdom (fun _ : Nat => (none : Option Nat)) n = true →
      crepHolFdom (fun _ : Nat => (none : Option Nat)) n = true) ↔
    (∀ n p, (fun _ : Nat => (none : Option Nat)) n = some p →
      ∃ q, (fun _ : Nat => (none : Option Nat)) n = some q) :=
  crepHolFdom_subset_flookup _ _

/-- `eval_code_inl`: a constant evaluates identically in the inlined code. -/
example : evalCrepHolExp evalBase (.const (7 : RiscV.Word 64)) =
    some (7 : RiscV.Word 64) :=
  crepInlineEvalCodeInl evalBase evalBase (.const (7 : RiscV.Word 64))
    (7 : RiscV.Word 64) evalInlineFmap (by simp only [evalCrepHolExp])
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl evalCodeInl_hcode

/-- `eval_code_inl` transfers a variable lookup through equal locals. -/
example : evalCrepHolExp evalBase (.var 0) = some (7 : RiscV.Word 64) := by
  simp only [evalCrepHolExp, evalBase]
  decide

def evalInvarianceGuard : Bool :=
  (evalCrepHolExp evalBase (.const (7 : RiscV.Word 64))).isSome &&
    (evalCrepHolExp evalBase (.var 0)).isSome

#guard evalInvarianceGuard

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
  let codeInlOk ←
    if codeInlGuard then
      IO.println "PASS crep_inline finite-map code_inl_rel relation"
      pure true
    else
      IO.println "FAIL crep_inline finite-map code_inl_rel relation"
      pure false
  let evalOk ←
    if evalInvarianceGuard then
      IO.println "PASS crep_inline eval_code_inl expression invariance"
      pure true
    else
      IO.println "FAIL crep_inline eval_code_inl expression invariance"
      pure false
  pure (relOk && codeInlOk && evalOk)

end Flapjack.Test.CrepInlineRelParity
