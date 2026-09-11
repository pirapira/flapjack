import Flapjack.RiscV.CorrectnessSsaColour

namespace Flapjack.Test.CorrectnessSsaColour

open Flapjack Flapjack.RiscV

example [NeZero width] (ssa : WordSsaState) (value : Word width) :
    (wordSsaRenameProgram ssa
      (.assign 3 (.const value) : WordProg (Word width))).2 =
      wordApplyColour (ssaAssignmentColour ssa 3)
        (.assign 3 (.const value)) := by
  apply ssaRenameAssign_eq_applyColour ssa 3 (.const value)
  · exact .assignConst 3 value (by omega)
  · simp [wordExpReadVars]

end Flapjack.Test.CorrectnessSsaColour
