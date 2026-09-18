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

def wordRecordReturn : Prog Nat :=
  .return (.rStruct [.const 7, .const 8])

def wordRecordFieldReturn : Prog Nat :=
  .return (.rField 1 (.rStruct [.const 7, .const 8]))

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

example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect wordRecordReturn := by
  apply panValueCrepProgramStateCorrect_statefulWord wordRecordReturn
  exact .returnWordRecord [.const 7, .const 8] hbytesInWord hlookup (by decide)

example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect wordRecordFieldReturn := by
  apply panValueCrepProgramStateCorrect_statefulWord wordRecordFieldReturn
  exact .returnWordRecordField [.const 7, .const 8] 1 hbytesInWord hlookup

end Flapjack.Test.CrepeProgramWordInduction
