import Flapjack.RiscV.CorrectnessColour

/-! Regression for live-scoped assignment cases related to CakeML's
    `evaluate_apply_colour`. The paired direct HOL observation for the binary
    case is `apply_colour_alias_add` in `scripts/hol-probes/apply_colour_probe.out`.
    These are finite RISC-V support cases, not the full HOL theorem. -/

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

private def binaryLiveColour (name : Nat) : Nat :=
  if name = 0 then 0 else if name = 1 then 1 else if name = 2 then 1
  else if name = 3 then 2 else 3

example :
    ∃ source' target',
      evalWordProg (zeroState 64)
        (.assign 2 (.op .add [.var 1, .var 3])) = some source' ∧
      evalWordProg (zeroState 64)
        (wordApplyColour binaryLiveColour
          (.assign 2 (.op .add [.var 1, .var 3]))) = some target' ∧
      WordColourStateRelationOn binaryLiveColour [4] source' target' := by
  have hvalid : wordColourValid binaryLiveColour := by
    intro name hname
    by_cases hzero : name = 0
    · simp [binaryLiveColour, hzero]
    · by_cases hone : name = 1
      · simp [binaryLiveColour, hone]
      · by_cases htwo : name = 2
        · simp [binaryLiveColour, htwo]
        · by_cases hthree : name = 3
          · simp [binaryLiveColour, hthree]
          · simp [binaryLiveColour, hzero, hone, htwo, hthree]
  have hrelation : WordColourStateRelationOn binaryLiveColour [1, 3, 4]
      (zeroState 64) (zeroState 64) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro name hmem hname hcolour
    rfl
  exact evalWordProg_assignBinaryVarVar_applyColour_live binaryLiveColour
    hvalid (by simp [binaryLiveColour]) (zeroState 64) (zeroState 64) [4]
    .add 2 1 3 (by omega) (by omega) (by omega) hrelation
    (by intro hzero; simp [binaryLiveColour, hzero])
    (by
      intro current hcurrent hdifferent
      have : current = 4 := by simpa using hcurrent
      subst current
      simp [binaryLiveColour])

example :
    wordApplyColour binaryLiveColour
      ((.assign 2 (.op .add [.var 1, .var 3])) : WordProg Nat) =
        ((.assign 1 (.op .add [.var 1, .var 2])) : WordProg Nat) := by
  simp [wordApplyColour, wordApplyColourExp, binaryLiveColour]

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

example :
    ∃ source' target',
      evalWordProg (zeroState 64) (.assign 2 (.const (BitVec.ofNat 64 5))) =
        some source' ∧
      evalWordProg (zeroState 64)
        (wordApplyColour liveAliasColour
          (.assign 2 (.const (BitVec.ofNat 64 5)))) = some target' ∧
      WordColourStateRelationOn liveAliasColour [3] source' target' := by
  have hvalid : wordColourValid liveAliasColour := by
    intro name hname
    by_cases hzero : name = 0
    · simp [liveAliasColour, hzero]
    · by_cases hlive : name = 3
      · simp [liveAliasColour, hlive]
      · simp [liveAliasColour, hzero, hlive]
  have hrelation : WordColourStateRelationOn liveAliasColour [3]
      (zeroState 64) (zeroState 64) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro name hmem hname hcolour
    rfl
  exact evalWordProg_assignConst_applyColour_live liveAliasColour hvalid
    (by simp [liveAliasColour]) (zeroState 64) (zeroState 64) [3] hrelation rfl
    2 (BitVec.ofNat 64 5) (by omega)
    (by intro hzero; simp [liveAliasColour, hzero])
    (by
      intro current hcurrent hdifferent
      have : current = 3 := by simpa using hcurrent
      subst current
      simp [liveAliasColour])

example :
    wordApplyColour liveAliasColour
      (.assign 2 (.const (BitVec.ofNat 64 5))) =
      .assign 1 (.const (BitVec.ofNat 64 5)) := by
  simp [wordApplyColour, wordApplyColourExp, liveAliasColour]

end Flapjack.Test.RiscVColourLivenessParity
