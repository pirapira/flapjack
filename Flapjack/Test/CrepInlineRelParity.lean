import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Test.CrepGlobalShapeParity

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

/-! ## Nontrivial distinct code maps related by `inline_prog` -/

/-- The inlineable callee `inc` with body `Skip`. -/
def inlineCalleeFmap : CrepInlineFmap (RiscV.Word 64) :=
  CrepInlineFmap.insert "inc" ([8], CrepProg.skip) CrepInlineFmap.empty

/-- Source `main` body: a call to the inlineable `inc`. -/
def inlineSrcMainBody : CrepProg (RiscV.Word 64) := .call none "inc" []

/-- Source code with two nonempty entries. -/
def inlineSrcCode : FunName → Option (List Nat × CrepProg (RiscV.Word 64)) :=
  fun n =>
    if n == "main" then some ([7], inlineSrcMainBody)
    else if n == "inc" then some ([8], CrepProg.skip)
    else none

/-- Target code: each source body replaced by its `inline_prog` image. -/
def inlineTgtCode : FunName → Option (List Nat × CrepProg (RiscV.Word 64)) :=
  fun n =>
    if n == "main" then
      some ([7], crepInlineProgFmap inlineCalleeFmap inlineSrcMainBody)
    else if n == "inc" then
      some ([8], crepInlineProgFmap inlineCalleeFmap CrepProg.skip)
    else none

/-- Source state: locals `0 := 7`, nonempty source code. -/
def inlineSrcState : CrepHolState (RiscV.Word 64) Unit :=
  { evalBase with code := inlineSrcCode }

/-- Target state: same locals and `state_rel_code` fields, different code. -/
def inlineTgtState : CrepHolState (RiscV.Word 64) Unit :=
  { evalBase with code := inlineTgtCode }

theorem inlineStates_state_rel_code :
    crepInlineStateRelCode inlineSrcState inlineTgtState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem inlineStates_locals_strong :
    crepInlineLocalsStrongRel inlineSrcState inlineTgtState := rfl

theorem inlineCodeInlRel :
    crepInlineCodeInlRel inlineCalleeFmap inlineSrcState inlineTgtState := by
  apply crepInlineCodeInlRel_of_code
  intro fname args prog hcode
  cases hmain : fname == "main" with
  | true =>
      simp [beq_iff_eq] at hmain
      subst hmain
      simp [inlineSrcState, inlineSrcCode] at hcode
      obtain ⟨rfl, rfl⟩ := hcode
      simp [inlineTgtState, inlineTgtCode]
  | false =>
      cases hinc : fname == "inc" with
      | true =>
          simp [beq_iff_eq] at hinc
          subst hinc
          simp [inlineSrcState, inlineSrcCode, hmain] at hcode
          obtain ⟨rfl, rfl⟩ := hcode
          simp [inlineTgtState, inlineTgtCode, hmain]
      | false =>
          simp [inlineSrcState, inlineSrcCode, hmain, hinc] at hcode

theorem inlineSrcVarEval :
    evalCrepHolExp inlineSrcState (.var 0) = some (7 : RiscV.Word 64) := by
  simp only [evalCrepHolExp, inlineSrcState, evalBase]
  decide

/-- `eval_code_inl` on a distinct nonempty code pair: the target still returns 7. -/
example : evalCrepHolExp inlineTgtState (.var 0) = some (7 : RiscV.Word 64) :=
  crepInlineEvalCodeInl inlineSrcState inlineTgtState (.var 0)
    (7 : RiscV.Word 64) inlineCalleeFmap inlineSrcVarEval
    inlineStates_state_rel_code inlineStates_locals_strong inlineCodeInlRel

def inlineEvalTransferGuard : Bool :=
  (inlineSrcState.code "main").isSome && (inlineTgtState.code "main").isSome &&
    (evalCrepHolExp inlineTgtState (.var 0) == some (7 : RiscV.Word 64))

#guard inlineEvalTransferGuard

/-- Nonempty heterogeneous expression list: a constant and a variable. -/
def inlineHeteroExps : List (CrepExp (RiscV.Word 64)) :=
  [.const (5 : RiscV.Word 64), .var 0]

theorem inlineSrcMmapEval :
    inlineHeteroExps.mapM (evalCrepHolExp inlineSrcState) =
      some [(5 : RiscV.Word 64), 7] := by
  simp only [inlineHeteroExps, List.mapM_cons, List.mapM_nil]
  simp only [evalCrepHolExp, inlineSrcState, evalBase]
  decide

/-- `opt_mmap_eval_code_inl` transfers the whole heterogeneous list: the
    distinct-code target evaluates it to the same values. -/
example :
    inlineHeteroExps.mapM (evalCrepHolExp inlineTgtState) =
      some [(5 : RiscV.Word 64), 7] :=
  crepInlineOptMmapEvalCodeInl inlineSrcState inlineTgtState inlineHeteroExps
    [(5 : RiscV.Word 64), 7] inlineCalleeFmap inlineSrcMmapEval
    inlineStates_state_rel_code inlineStates_locals_strong inlineCodeInlRel

def inlineMmapTransferGuard : Bool :=
  (inlineHeteroExps.mapM (evalCrepHolExp inlineTgtState) ==
    some [(5 : RiscV.Word 64), 7])

#guard inlineMmapTransferGuard

/-! ## `inline_prog_correct` Skip constructor case

The HOL `inline_prog_correct` Skip case: a source run of `Skip` ends in the same
state, `inline_prog` maps `Skip` to `Skip`, and the target run exists and
preserves the input relations.  We exercise it over the production fuel-bounded
evaluator `evalCrepRuntimeResult`; the theorem is untagged because that
evaluator is fuel-cutoff based rather than HOL's clock-based `evaluate`. -/

/-- The empty inline map relates the (vacuous) code of `globalState` to itself. -/
theorem skipCodeInlRel :
    crepInlineRuntimeCodeInlRel CrepInlineFmap.empty
      Flapjack.Test.CrepGlobalShapeParity.globalState
      Flapjack.Test.CrepGlobalShapeParity.globalState := by
  apply crepInlineCodeInlRel_of_code
  intro fname args prog hcode
  simp [CrepRuntimeState.toHolState, Flapjack.Test.CrepGlobalShapeParity.globalState,
    FEMPTY] at hcode

/-- The Skip fixture is `state_rel_code` to itself. -/
theorem skipStateRel :
    crepInlineRuntimeStateRelCode Flapjack.Test.CrepGlobalShapeParity.globalState
      Flapjack.Test.CrepGlobalShapeParity.globalState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The Skip fixture is `locals_strong_rel` to itself. -/
theorem skipLocalsStrong :
    crepInlineRuntimeLocalsStrongRel Flapjack.Test.CrepGlobalShapeParity.globalState
      Flapjack.Test.CrepGlobalShapeParity.globalState := rfl

/-- Skip-case transfer: the target run is *derived* (existential) and preserves
    all postrelations, rather than being assumed. -/
example :
    ∃ t',
      evalCrepRuntimeResult Flapjack.Test.CrepGlobalShapeParity.runtimeHandler
          Flapjack.Test.CrepGlobalShapeParity.noPrimitive 1
          Flapjack.Test.CrepGlobalShapeParity.globalState
          (crepInlineProgFmap CrepInlineFmap.empty CrepProg.skip) =
        some (CrepRuntimeResult.normal, t') ∧
      crepInlineRuntimeStateRelCode Flapjack.Test.CrepGlobalShapeParity.globalState
        t' ∧
      crepInlineRuntimeLocalsStrongRel Flapjack.Test.CrepGlobalShapeParity.globalState
        t' ∧
      crepInlineRuntimeCodeInlRel CrepInlineFmap.empty
        Flapjack.Test.CrepGlobalShapeParity.globalState t' :=
  crepInlineRuntimeSkip Flapjack.Test.CrepGlobalShapeParity.runtimeHandler
    Flapjack.Test.CrepGlobalShapeParity.noPrimitive 0
    Flapjack.Test.CrepGlobalShapeParity.globalState
    Flapjack.Test.CrepGlobalShapeParity.globalState
    Flapjack.Test.CrepGlobalShapeParity.globalState CrepInlineFmap.empty
    (evalCrepRuntimeResult_skip Flapjack.Test.CrepGlobalShapeParity.runtimeHandler
      Flapjack.Test.CrepGlobalShapeParity.noPrimitive 0
      Flapjack.Test.CrepGlobalShapeParity.globalState)
    skipStateRel skipLocalsStrong skipCodeInlRel

/-- The inline transform leaves `Skip` unchanged. -/
example : crepInlineProgFmap CrepInlineFmap.empty CrepProg.skip = CrepProg.skip :=
  crepInlineProgFmap_skip CrepInlineFmap.empty

def inlineSkipGuard : Bool :=
  (evalCrepRuntimeResult Flapjack.Test.CrepGlobalShapeParity.runtimeHandler
    Flapjack.Test.CrepGlobalShapeParity.noPrimitive 1
    Flapjack.Test.CrepGlobalShapeParity.globalState CrepProg.skip).isSome

#guard inlineSkipGuard

/-- Handler and primitive used by the clocked `CrepHolState` evaluator. -/
def evalHandler64 : CrepRuntimeFfiHandler (RiscV.Word 64) Unit Unit :=
  fun _ state => CrepRuntimeFfiResponse.returned state []

def evalPrimitive64 : CrepPrimitiveHandler (RiscV.Word 64) := fun _ _ => none

/-- Clocked evaluator `Skip` equation over the 11-field `CrepHolState`,
    matching HOL `crepSem$evaluate (Skip,s) = (NONE,s)`. -/
example :
    evalCrepHolProg (evalBase.clock + 1) evalHandler64 evalPrimitive64 evalBase
        CrepProg.skip =
      some (CrepRuntimeResult.normal, evalBase) :=
  evalCrepHolProg_skip evalHandler64 evalPrimitive64 evalBase

def holSkipEvalGuard : Bool :=
  (evalCrepHolProg (evalBase.clock + 1) evalHandler64 evalPrimitive64 evalBase
    CrepProg.skip).isSome

#guard holSkipEvalGuard

/-- Clocked evaluator `Break` equation over the 11-field `CrepHolState`,
    matching HOL `crepSem$evaluate (Break n,s) = (SOME (Break n),s)`. -/
example :
    evalCrepHolProg (evalBase.clock + 1) evalHandler64 evalPrimitive64 evalBase
        (CrepProg.break 1) =
      some (CrepRuntimeResult.broke 1, evalBase) :=
  evalCrepHolProg_break evalHandler64 evalPrimitive64 evalBase 1

/-- Clocked evaluator `Continue` equation over the 11-field `CrepHolState`,
    matching HOL `crepSem$evaluate (Continue n,s) = (SOME (Continue n),s)`. -/
example :
    evalCrepHolProg (evalBase.clock + 1) evalHandler64 evalPrimitive64 evalBase
        (CrepProg.continue 2) =
      some (CrepRuntimeResult.continued 2, evalBase) :=
  evalCrepHolProg_continue evalHandler64 evalPrimitive64 evalBase 2

def holBreakEvalGuard : Bool :=
  (evalCrepHolProg (evalBase.clock + 1) evalHandler64 evalPrimitive64 evalBase
    (CrepProg.break 1)).isSome

def holContinueEvalGuard : Bool :=
  (evalCrepHolProg (evalBase.clock + 1) evalHandler64 evalPrimitive64 evalBase
    (CrepProg.continue 2)).isSome

#guard holBreakEvalGuard
#guard holContinueEvalGuard

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
  let inlineEvalOk ←
    if inlineEvalTransferGuard then
      IO.println "PASS crep_inline eval_code_inl nontrivial distinct-code transfer"
      pure true
    else
      IO.println "FAIL crep_inline eval_code_inl nontrivial distinct-code transfer"
      pure false
  let inlineMmapOk ←
    if inlineMmapTransferGuard then
      IO.println "PASS crep_inline opt_mmap_eval_code_inl heterogeneous list transfer"
      pure true
    else
      IO.println "FAIL crep_inline opt_mmap_eval_code_inl heterogeneous list transfer"
      pure false
  let inlineSkipOk ←
    if inlineSkipGuard then
      IO.println "PASS crep_inline inline_prog_correct Skip case"
      pure true
    else
      IO.println "FAIL crep_inline inline_prog_correct Skip case"
      pure false
  let holSkipEvalOk ←
    if holSkipEvalGuard then
      IO.println "PASS crepSem clocked evaluate Skip constructor over CrepHolState"
      pure true
    else
      IO.println "FAIL crepSem clocked evaluate Skip constructor over CrepHolState"
      pure false
  let holBreakEvalOk ←
    if holBreakEvalGuard && holContinueEvalGuard then
      IO.println "PASS crepSem clocked evaluate Break/Continue constructors over CrepHolState"
      pure true
    else
      IO.println "FAIL crepSem clocked evaluate Break/Continue constructors over CrepHolState"
      pure false
  pure (relOk && codeInlOk && evalOk && inlineEvalOk && inlineMmapOk && inlineSkipOk && holSkipEvalOk && holBreakEvalOk)

end Flapjack.Test.CrepInlineRelParity
