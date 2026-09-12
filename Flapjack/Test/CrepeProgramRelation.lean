import Flapjack.CrepeProgramRelation

/-! Regression coverage for the base cases of the source-to-Crep program
relation.  Keeping these applications concrete makes sure the generic leaf
theorems elaborate with the ordinary arithmetic instances used by tests. -/

namespace Flapjack

example : PanValueCrepProgramCorrect (.skip : Prog Nat) :=
  panValueCrepProgramCorrect_skip

example : PanValueCrepProgramCorrect (.tick : Prog Nat) :=
  panValueCrepProgramCorrect_tick

example : PanValueCrepProgramCorrect (.annot "test" "leaf" : Prog Nat) :=
  panValueCrepProgramCorrect_annot "test" "leaf"

example : PanValueCrepProgramCorrect (.break : Prog Nat) :=
  panValueCrepProgramCorrect_break

example : PanValueCrepProgramCorrect (.continue : Prog Nat) :=
  panValueCrepProgramCorrect_continue

end Flapjack
