import Flapjack.RiscV.CorrectnessSsa

namespace Flapjack.RiscV

/-! Regression coverage for the first SSA-renaming semantic boundary. -/

example :
    (evalWordProg (zeroState 32)
      (.inst (.mem .store 1 2))).map (fun state => state.memory) =
      (evalWordProg (zeroState 32)
        (.inst (wordSsaRenameInst
          ({ current := [], next := 0 } : WordSsaState)
          (.mem .store 1 2)).2)).map (fun state => state.memory) := by
  apply evalWordProg_ssaRename_store
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32) (.inst (.mem .load 1 2)) = some source' ∧
      evalWordProg (zeroState 32)
          (.inst (wordSsaRenameInst
            ({ current := [], next := 4 } : WordSsaState)
            (.mem .load 1 2)).2) = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_load_destination
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    (evalWordProg (zeroState 32)
      (.inst (.mem .store32 1 2))).map (fun state => state.memory) =
      (evalWordProg (zeroState 32)
        (.inst (wordSsaRenameInst
          ({ current := [], next := 4 } : WordSsaState)
          (.mem .store32 1 2)).2)).map (fun state => state.memory) := by
  apply evalWordProg_ssaRename_store_family
  · intro name
    rfl
  · rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32) (.inst (.arith (.div 1 2 3))) = some source' ∧
      evalWordProg (zeroState 32)
          (.inst (wordSsaRenameInst
            ({ current := [], next := 4 } : WordSsaState)
            (.arith (.div 1 2 3) : WordInst)).2) = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_div_destination
  · intro name
    rfl
  · rfl
  all_goals decide

end Flapjack.RiscV
