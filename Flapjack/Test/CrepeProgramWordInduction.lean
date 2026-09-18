import Flapjack.CrepeProgramWordInduction

/-!
Regression coverage for the source-word stateful induction assembly.  The
lookup premise is intentionally quantified exactly as it is in the
Cake-faithful word constructor theorem; this test checks that the new
induction preserves that premise rather than hiding it in a compatibility
evaluator.
-/

namespace Flapjack.Test.CrepeProgramWordInduction

open Flapjack

def wordReturn : Prog Nat := .return (.const 7)

def wordReturnThenTick : Prog Nat :=
  .seq wordReturn (.seq .tick (.annot "word" "induction"))

example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    StatefulWordProg Nat wordReturnThenTick := by
  exact .seq
    (.returnWord (.const 7) (by simp [wordExp]) hbytesInWord hlookup)
    (.seq .tick (.annot "word" "induction"))

example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect wordReturnThenTick := by
  apply panValueCrepProgramStateCorrect_statefulWord wordReturnThenTick
  exact .seq
    (.returnWord (.const 7) (by simp [wordExp]) hbytesInWord hlookup)
    (.seq .tick (.annot "word" "induction"))

end Flapjack.Test.CrepeProgramWordInduction
