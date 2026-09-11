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
