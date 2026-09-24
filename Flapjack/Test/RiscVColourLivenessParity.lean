import Flapjack.RiscV.CorrectnessColour

/-! Regression for the live-set assignment case of CakeML's
    `evaluate_apply_colour`: a source and destination may share one colour
    when the source is read before the write and no other live value clashes. -/

namespace Flapjack.Test.RiscVColourLivenessParity

open Flapjack.RiscV

private def aliasColour (name : Nat) : Nat := if name = 0 then 0 else 1

example :
    ∃ source' target',
      evalWordProg (zeroState 64) (.assign 2 (.var 1)) = some source' ∧
      evalWordProg (zeroState 64)
        (wordApplyColour aliasColour (.assign 2 (.var 1))) = some target' ∧
      WordColourStateRelationOn aliasColour [] source' target' := by
  have hvalid : wordColourValid aliasColour := by
    intro name hname
    by_cases hzero : name = 0
    · simp [aliasColour, hzero]
    · simp [aliasColour, hzero]
  have hcolourZero : aliasColour 0 = 0 := by simp [aliasColour]
  have hrelation : WordColourStateRelationOn aliasColour [1]
      (zeroState 64) (zeroState 64) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro name hmem hname hcolour
    rfl
  exact evalWordProg_assignVar_applyColour_live aliasColour hvalid hcolourZero
    (zeroState 64) (zeroState 64) [] 2 1 (by omega) (by omega) hrelation
    (by intro _; simp [aliasColour])
    (by simp)

private def liveAliasColour (name : Nat) : Nat :=
  if name = 0 then 0 else if name = 3 then 2 else 1

example :
    ∃ source' target',
      evalWordProg (zeroState 64) (.assign 2 (.var 1)) = some source' ∧
      evalWordProg (zeroState 64)
        (wordApplyColour liveAliasColour (.assign 2 (.var 1))) = some target' ∧
      WordColourStateRelationOn liveAliasColour [3] source' target' := by
  have hvalid : wordColourValid liveAliasColour := by
    intro name hname
    by_cases hzero : name = 0
    · simp [liveAliasColour, hzero]
    · by_cases hlive : name = 3
      · simp [liveAliasColour, hlive]
      · simp [liveAliasColour, hzero, hlive]
  have hcolourZero : liveAliasColour 0 = 0 := by simp [liveAliasColour]
  have hrelation : WordColourStateRelationOn liveAliasColour [1, 3]
      (zeroState 64) (zeroState 64) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro name hmem hname hcolour
    rfl
  exact evalWordProg_assignVar_applyColour_live liveAliasColour hvalid hcolourZero
    (zeroState 64) (zeroState 64) [3] 2 1 (by omega) (by omega) hrelation
    (by intro hzero; simp [liveAliasColour, hzero])
    (by
      intro current hcurrent hdifferent
      have : current = 3 := by simpa using hcurrent
      subst current
      simp [liveAliasColour])

example :
    liveAliasColour 3 ≠ liveAliasColour 2 := by
  apply wordColouringRespectsClashes_singleWrite_map_noAlias
    2 [3] liveAliasColour [(2, 1), (3, 2)]
  · decide
  · intro name hname
    rcases hname with rfl | hname
    · simp [lookupNatInfo, liveAliasColour]
    · have : name = 3 := by simpa using hname
      subst name
      simp [lookupNatInfo, liveAliasColour]
  · simp
  · simp

end Flapjack.Test.RiscVColourLivenessParity
