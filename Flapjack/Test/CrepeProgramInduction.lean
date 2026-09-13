import Flapjack.CrepeProgramInduction

/-!
Regression coverage for the assembled stateful source-to-Crep induction.
The example has nested sequencing and a return boundary, so it exercises both
the recursive proof and the explicit source/compiled state relation.
-/

namespace Flapjack.Test.CrepeProgramInduction

open Flapjack

def compactExample : Prog Nat :=
  .seq (.return (.const 7))
    (.seq .tick (.annot "regression" "stateful"))

example : StatefulCompactProg Nat compactExample := by
  exact .seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful"))

example : PanValueCrepProgramStateCorrect compactExample := by
  exact panValueCrepProgramStateCorrect_statefulCompact compactExample
    (.seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful")))

end Flapjack.Test.CrepeProgramInduction
