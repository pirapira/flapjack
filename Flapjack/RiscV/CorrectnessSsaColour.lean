import Flapjack.RiscV.CorrectnessColour

/-!
# SSA-renaming to colouring boundary

CakeML's SSA pass gives each assignment a fresh destination, while the
colouring pass applies one fixed name map to a whole program.  These are the
same transformation for a straight-line assignment when its RHS does not
read the destination.  This module records that equation and immediately
feeds it into the executable colouring simulation.
-/

namespace Flapjack.RiscV

def ssaAssignmentColour (ssa : WordSsaState) (name : Nat) : Nat → Nat :=
  fun current => if current = name then (wordSsaFresh ssa name).2
    else wordSsaRead ssa current

/-! Before an SSA assignment, the destination's old value need not satisfy the
    eventual colouring relation: the generated code overwrites it. -/

structure WordColourStateRelationExcept (colour : Nat → Nat) (excluded : Nat)
    [NeZero width] (source target : State width) : Prop where
  pc : source.pc = target.pc
  memory : source.memory = target.memory
  privilege : source.privilege = target.privilege
  mode : source.mode = target.mode
  register : ∀ (current : Nat) (hcurrent : current < 32)
      (_hnot : current ≠ excluded) (hcolour : colour current < 32),
    readRegister source ⟨current, hcurrent⟩ =
      readRegister target ⟨colour current, hcolour⟩

theorem wordColourStateRelationExcept_nextPc
    (colour : Nat → Nat) (excluded : Nat)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelationExcept colour excluded source target) :
    WordColourStateRelationExcept colour excluded
      {source with pc := nextPc source} {target with pc := nextPc target} := by
  constructor
  · simp [nextPc, hrelation.pc]
  · exact hrelation.memory
  · exact hrelation.privilege
  · exact hrelation.mode
  · intro current hcurrent hnot hcolour
    exact hrelation.register current hcurrent hnot hcolour

theorem wordColourStateRelationExcept_writeRegister
    (colour : Nat → Nat) (excluded : Nat)
    (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelationExcept colour excluded source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : excluded < 32) (value targetValue : Word width)
    (hvalue : value = targetValue) :
    WordColourStateRelation colour
      (writeRegister source ⟨excluded, hname⟩ value)
      (writeRegister target ⟨colour excluded, valid excluded hname⟩ targetValue) := by
  by_cases hzero : excluded = 0
  · have hcolourZero : colour excluded = 0 := by simpa [hzero] using colourZero
    subst excluded
    constructor
    · simpa [writeRegister, colourZero] using hrelation.pc
    · simpa [writeRegister, colourZero] using hrelation.memory
    · simpa [writeRegister, colourZero] using hrelation.privilege
    · simpa [writeRegister, colourZero] using hrelation.mode
    · intro current hcurrent hcolour
      by_cases hcurrentZero : current = 0
      · subst current
        simpa [ZeroRegister, readRegister, writeRegister, colourZero] using
          hzeroSource.trans hzeroTarget.symm
      · simpa [writeRegister, readRegister, colourZero, hcurrentZero] using
          hrelation.register current hcurrent hcurrentZero hcolour
  · have hsourceNonzero : (⟨excluded, hname⟩ : Fin 32) ≠ 0 := by
      intro h
      exact hzero (congrArg Fin.val h)
    have hcolourNonzero : colour excluded ≠ 0 := by
      intro h
      apply hzero
      apply injective
      simpa [colourZero] using h
    have htargetNonzero :
        (⟨colour excluded, valid excluded hname⟩ : Fin 32) ≠ 0 := by
      intro h
      exact hcolourNonzero (congrArg Fin.val h)
    constructor
    · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
      exact hrelation.pc
    · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
      exact hrelation.memory
    · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
      exact hrelation.privilege
    · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
      exact hrelation.mode
    · intro current hcurrent hcolour
      by_cases hsame : current = excluded
      · subst current
        have hsourceEq :
            (⟨excluded, hcurrent⟩ : Fin 32) = ⟨excluded, hname⟩ := by
          apply Fin.ext
          rfl
        have htargetEq :
            (⟨colour excluded, hcolour⟩ : Fin 32) =
              ⟨colour excluded, valid excluded hname⟩ := by
          apply Fin.ext
          rfl
        simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false,
          readRegister]
        simp only [if_true]
        exact hvalue
      · have htargetSame :
            (⟨colour current, hcolour⟩ : Fin 32) ≠
              (⟨colour excluded, valid excluded hname⟩ : Fin 32) := by
          intro h
          apply hsame
          apply injective
          exact congrArg Fin.val h
        have hsourceCurrent :
            (⟨current, hcurrent⟩ : Fin 32) ≠ ⟨excluded, hname⟩ := by
          intro h
          apply hsame
          exact congrArg Fin.val h
        simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false,
          readRegister]
        rw [if_neg hsourceCurrent, if_neg htargetSame]
        exact hrelation.register current hcurrent hsame hcolour

theorem wordColourStateRelationExcept_executeConst
    [NeZero width]
    (colour : Nat → Nat) (excluded : Nat)
    (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept colour excluded source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : excluded < 32) (hvalue : Word width) :
    WordColourStateRelation colour
      (execute source (.addi ⟨excluded, hname⟩ 0 hvalue))
      (execute target
        (.addi ⟨colour excluded, valid excluded hname⟩ 0 hvalue)) := by
  have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
  have hread :
      readRegister source 0 + hvalue = readRegister target 0 + hvalue := by
    simpa [ZeroRegister] using congrArg (fun value => value + hvalue)
      (hzeroSource.trans hzeroTarget.symm)
  have hstate := wordColourStateRelationExcept_writeRegister colour excluded
    valid injective colourZero {source with pc := nextPc source}
    {target with pc := nextPc target} hnext
    (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
    (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
    hname (readRegister source 0 + hvalue)
    (readRegister target 0 + hvalue) hread
  simpa [execute] using hstate

theorem ssaRenameAssign_eq_applyColour
    [NeZero width] (ssa : WordSsaState) (name : Nat)
    (value : WordExp (Word width))
    (hprogram : WordVarStraightLine width (.assign name value))
    (hnot : name ∉ wordExpReadVars value) :
    (wordSsaRenameProgram ssa (.assign name value)).2 =
      wordApplyColour (ssaAssignmentColour ssa name)
        (.assign name value) := by
  cases hprogram with
  | assign name source hname hsource =>
      have hne : name ≠ source := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hne' : source ≠ name := Ne.symm hne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hne']
  | assignConst name value hname =>
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp]
  | assignBinary operator name left right hname hleft hright =>
      have hleft_ne : name ≠ left := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hright_ne : name ≠ right := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hleft_ne' : left ≠ name := Ne.symm hleft_ne
      have hright_ne' : right ≠ name := Ne.symm hright_ne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hleft_ne', hright_ne']
  | assignImmediate operator name source value hname hsource =>
      have hne : name ≠ source := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hne' : source ≠ name := Ne.symm hne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hne']
  | assignShift operator name left right hoperator hname hleft hright =>
      have hleft_ne : name ≠ left := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hright_ne : name ≠ right := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hleft_ne' : left ≠ name := Ne.symm hleft_ne
      have hright_ne' : right ≠ name := Ne.symm hright_ne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hleft_ne', hright_ne']
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      have hne : name ≠ left := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hne' : left ≠ name := Ne.symm hne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hne']

/-! The first SSA assignment simulation permits an arbitrary old value in the
    fresh target register.  This is the overwrite property needed before
    composing multiple SSA writes. -/

theorem evalWordFunction_ssaRenameAssignConst_applyColourExcept
    [NeZero width]
    (ssa : WordSsaState) (name : Nat) (value : Word width)
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept
      (ssaAssignmentColour ssa name) name source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : name < 32) :
    ∃ source' target',
      evalWordFunction source (.assign name (.const value)) =
        some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa (.assign name (.const value))).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  let colour := ssaAssignmentColour ssa name
  have hprogram : WordVarStraightLine width
      (.assign name (.const value)) :=
    .assignConst name value hname
  have hnot : name ∉ wordExpReadVars (.const value) := by
    simp [wordExpReadVars]
  have hrename := ssaRenameAssign_eq_applyColour ssa name (.const value)
    hprogram hnot
  have hsourceEval :
      evalWordFunction source (.assign name (.const value)) =
        some (execute source (.addi ⟨name, hname⟩ 0 value), []) := by
    simp [evalWordFunction, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, hname, executeInstructions]
  have htargetEval :
      evalWordFunction target
          (wordSsaRenameProgram ssa (.assign name (.const value))).2 =
        some (execute target
          (.addi ⟨colour name, valid name hname⟩ 0 value), []) := by
    rw [hrename]
    simp [colour, evalWordFunction, wordApplyColour,
      wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, valid name hname, executeInstructions]
  have hrelation' := wordColourStateRelationExcept_executeConst
    colour name valid injective colourZero source target hrelation
    hzeroSource hzeroTarget hname value
  exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩

theorem evalWordFunction_ssaRenameAssign_applyColour
    [NeZero width]
    (ssa : WordSsaState) (name : Nat) (value : WordExp (Word width))
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (colourNoScratch : ∀ current, current < 31 →
      ssaAssignmentColour ssa name current ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation
      (ssaAssignmentColour ssa name) source target)
    (hprogram : WordVarStraightLine width (.assign name value))
    (hnot : name ∉ wordExpReadVars value) :
    ∃ source' target',
      evalWordFunction source (.assign name value) = some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa (.assign name value)).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  rcases evalWordFunction_wordVarStraightLine_applyColour
    (ssaAssignmentColour ssa name) valid injective colourZero colourNoScratch
    source target hrelation (.assign name value) hprogram with
    ⟨source', target', hsource, htarget, hrelation'⟩
  have hrename := ssaRenameAssign_eq_applyColour ssa name value hprogram hnot
  refine ⟨source', target', hsource, ?_, hrelation'⟩
  simpa [hrename] using htarget

end Flapjack.RiscV
