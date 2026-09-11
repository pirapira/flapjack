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

end Flapjack.RiscV
