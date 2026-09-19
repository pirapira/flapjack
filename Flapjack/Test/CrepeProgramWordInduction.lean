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

def wordRecordRaise : Prog Nat :=
  .raise "E" (.rStruct [.const 3, .const 4, .const 5, .const 6, .const 7])

def nestedWordRecordRaise : Prog Nat :=
  .raise "E" (.rStruct [.rStruct [.const 3]])

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

example
    (hlookupException : ∀ (context : CompileContext Nat),
      ∃ exceptionCode, lookupInfo "E" context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext Nat) (state : CrepState Nat)
      (name : Nat), name ∈ freshNames context 5 1 →
      state.locals name = none)
    (hexception : ∀ (context : CompileContext Nat)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (exceptionCode : Nat),
      lookupInfo "E" context.exceptions = some exceptionCode →
      exceptionRel "E" (.rStruct
        [.word 3, .word 4, .word 5, .word 6, .word 7]) exceptionCode) :
    PanValueCrepProgramStateCorrect wordRecordRaise := by
  apply panValueCrepProgramStateCorrect_statefulWord wordRecordRaise
  exact .raiseWordRecord "E" [3, 4, 5, 6, 7]
    hlookupException hfresh hexception

example
    (hlookupException : ∀ (context : CompileContext Nat),
      ∃ exceptionCode, lookupInfo "E" context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext Nat) (state : CrepState Nat),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext Nat)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (exceptionCode : Nat),
      lookupInfo "E" context.exceptions = some exceptionCode →
      exceptionRel "E" (.rStruct [.rStruct [.word 3]]) exceptionCode) :
    PanValueCrepProgramStateCorrect nestedWordRecordRaise := by
  apply panValueCrepProgramStateCorrect_statefulWord nestedWordRecordRaise
  exact .raiseNestedWordRecord "E" 3 hlookupException hfresh hexception

end Flapjack.Test.CrepeProgramWordInduction
