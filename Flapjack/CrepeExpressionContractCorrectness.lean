import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeSourceWordRecordCorrectness

/-!
Expression-contract instances for the scalar source fragment.

This is the expression-side companion to the program-level return constructor:
the structural expression simulation supplies the compilation witness, while
the state relation supplies the values of local slots.
-/

namespace Flapjack

theorem panValueCrepExpressionCorrect_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionCorrect expression.toExp := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  obtain ⟨value, hword⟩ := evalPanValueExp_sourceWord_inv
    structs sourceLocals sourceGlobals sourceMemory
    baseAddress topAddress bytesInWord context hrel.2.1
    (fun name value hvalue =>
      hlookup context sourceLocals name value hvalue)
    expression sourceValue hsource
  cases hword
  have hsourceValue :
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression.toExp =
        some (.word value) := by
    exact hsource
  obtain ⟨compiled, hcompile, hcompiled⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      (hbytesInWord context bytesInWord) hrel.2.1
      (fun name value hvalue =>
        hlookup context sourceLocals name value hvalue)
      expression value hsourceValue
  refine ⟨by simp, [compiled], ?_, ?_⟩
  · simpa [panValueShape] using hcompile
  · simp [evalCrepFullExps, hcompiled, panValueFlatWords,
      panValueFlatWordsFuel]

theorem panValueCrepExpressionCorrect_two_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (left right : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionCorrect
      (.rStruct [left.toExp, right.toExp]) := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left.toExp with
  | none =>
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hleft] at hsource
  | some leftValue' =>
      obtain ⟨leftValue, hleftWord⟩ := evalPanValueExp_sourceWord_inv
        structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord context hrel.2.1
        (fun name value hvalue =>
          hlookup context sourceLocals name value hvalue)
        left leftValue' hleft
      have hleftSource :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord left.toExp =
            some (.word leftValue) := by
        rw [hleft, hleftWord]
      cases hright : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord right.toExp with
      | none =>
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleft, hright] at hsource
      | some rightValue' =>
          obtain ⟨rightValue, hrightWord⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun name value hvalue =>
              hlookup context sourceLocals name value hvalue)
            right rightValue' hright
          have hrightSource :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord right.toExp =
                some (.word rightValue) := by
            rw [hright, hrightWord]
          have hsourceValue :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord
                (.rStruct [left.toExp, right.toExp]) =
                some (.rStruct [.word leftValue, .word rightValue]) := by
            simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
              hleftSource, hrightSource]
          have hvalueEq : sourceValue =
              (.rStruct [.word leftValue, .word rightValue] : PanValue α) := by
            exact Option.some.inj (hsource.symm.trans hsourceValue)
          cases hvalueEq
          obtain ⟨compiled, hcompile, hcompiled⟩ :=
            compileSourceWordRecordExp_relation context structs sourceLocals
              sourceGlobals sourceMemory state.locals state.memory
              baseAddress topAddress bytesInWord
              (hbytesInWord context bytesInWord) hrel.2.1
              (fun name value hvalue =>
                hlookup context sourceLocals name value hvalue)
              [left, right] [leftValue, rightValue]
              (by simpa [evalPanValueExp, evalPanValueExps, Function.comp_def]
                using hsourceValue)
          refine ⟨by simp, compiled, ?_, ?_⟩
          · simpa [panValueShape] using hcompile
          · have hflat :
                panValueFlatWords
                    (.rStruct [.word leftValue, .word rightValue]) =
                  [leftValue, rightValue] := by
              simp [panValueFlatWords, panValueFlatWordsFuel,
                panValueFlatValueFuel,
                panValueFlatWordsFuel.panValueFlatWordsListFuel,
                panValueFlatValueFuel.panValueFlatValueListFuel]
            simpa [hflat] using hcompiled

end Flapjack
