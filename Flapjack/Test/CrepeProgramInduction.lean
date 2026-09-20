import Flapjack.PanToCrepCorrectnessBoundary

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

def arbitraryRaise : Prog Nat :=
  .raise "E" (.rStruct [.const 3, .const 5, .const 8])

example : StatefulCompactProg Nat compactExample := by
  exact .seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful"))

example : PanValueCrepProgramStateCorrect compactExample := by
  exact panValueCrepProgramStateCorrect_statefulCompact compactExample
    (.seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful")))

example : PanValueCrepProgramCorrect compactExample := by
  exact panValueCrepProgramCorrect_statefulCompact compactExample
    (.seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful")))

example (hraiseState : PanValueCrepProgramStateCorrect arbitraryRaise)
    (hraisePlain : PanValueCrepProgramCorrect arbitraryRaise) :
    StatefulCompactProg Nat arbitraryRaise := by
  exact .raiseWithEvidence "E" (.rStruct [.const 3, .const 5, .const 8])
    hraiseState hraisePlain

example (hraiseState : PanValueCrepProgramStateCorrect arbitraryRaise)
    (hraisePlain : PanValueCrepProgramCorrect arbitraryRaise) :
    PanValueCrepProgramStateCorrect arbitraryRaise := by
  exact panValueCrepProgramStateCorrect_statefulCompact arbitraryRaise
    (.raiseWithEvidence "E" (.rStruct [.const 3, .const 5, .const 8])
      hraiseState hraisePlain)

example (hraiseState : PanValueCrepProgramStateCorrect arbitraryRaise)
    (hraisePlain : PanValueCrepProgramCorrect arbitraryRaise) :
    PanValueCrepProgramCorrect arbitraryRaise := by
  exact panValueCrepProgramCorrect_statefulCompact arbitraryRaise
    (.raiseWithEvidence "E" (.rStruct [.const 3, .const 5, .const 8])
      hraiseState hraisePlain)

example : PanValueCrepProgramStateControlSafe compactExample := by
  exact panValueCrepProgramStateControlSafe_statefulCompact compactExample
    (.seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful")))

example : PanValueCrepProgramStateCorrect compactExample ∧
    PanValueCrepProgramStateControlSafe compactExample := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_statefulCompact
    compactExample
    (.seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful")))

/-! The composed return theorem is exercised independently of the inductive
fragment, with a continuation that would change control if it were run. -/
example : PanValueCrepProgramStateCorrect
    (.seq (.return (.const (11 : Nat))) (.tick : Prog Nat)) := by
  exact panValueCrepProgramStateCorrect_seq_return_const 11 .tick
    panValueCrepProgramStateCorrect_tick

end Flapjack.Test.CrepeProgramInduction
