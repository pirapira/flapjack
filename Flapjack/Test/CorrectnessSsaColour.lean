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

example [NeZero width] (ssa : WordSsaState) :
    (wordSsaRenameProgram ssa
      (.assign 3 (.var 2) : WordProg (Word width))).2 =
      wordApplyColour (ssaAssignmentColour ssa 3)
        (.assign 3 (.var 2)) := by
  apply ssaRenameAssign_eq_applyColour ssa 3 (.var 2)
  · exact .assign 3 2 (by omega) (by omega)
  · simp [wordExpReadVars]

example [NeZero width] (ssa : WordSsaState) :
    (wordSsaRenameProgram ssa
      (.assign 3 (.op .add [.var 1, .var 2]) : WordProg (Word width))).2 =
      wordApplyColour (ssaAssignmentColour ssa 3)
        (.assign 3 (.op .add [.var 1, .var 2])) := by
  apply ssaRenameAssign_eq_applyColour ssa 3
    (.op .add [.var 1, .var 2])
  · exact .assignBinary .add 3 1 2 (by omega) (by omega) (by omega)
  · simp [wordExpReadVars]

end Flapjack.Test.CorrectnessSsaColour
