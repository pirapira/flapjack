import Flapjack.CrepeExpCorrectness
import Flapjack.CrepeExpressionRelation

/-!
Expression-contract correctness for a scalar field projection from a record of
constant words.  The existing compiler lemma identifies the selected Crep
constant; this contract packages it for the compositional program theorem.
-/

namespace Flapjack

theorem panValueCrepExpressionCorrect_rField_const_words
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (values : List α) (index : Nat) (value : α)
    (hfield : values[index]? = some value) :
    PanValueCrepExpressionCorrect
      (.rField index (.rStruct (values.map (fun value => .const value)))) := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  obtain ⟨hcompile, hsourceExpected, hcrep⟩ :=
    compileExp_rField_const_words_correct context structs sourceLocals
      sourceGlobals sourceMemory state.locals state.memory baseAddress topAddress
      bytesInWord values index value hfield
  have hsourceValue : sourceValue = .word value := by
    apply Option.some.inj
    exact hsource.symm.trans hsourceExpected
  subst sourceValue
  refine ⟨panValuePayloadWithinLimit_word structs value, [.const value], ?_, ?_⟩
  · simpa [panValueShape] using hcompile
  · simp [evalCrepFullExps, hcrep, panValueFlatWords,
      panValueFlatWordsFuel]

theorem panValueCrepExpressionStateCorrect_rField_const_words
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (values : List α) (index : Nat) (value : α)
    (hfield : values[index]? = some value) :
    PanValueCrepExpressionStateCorrect
      (.rField index (.rStruct (values.map (fun value => .const value)))) := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  obtain ⟨hcompile, hsourceExpected, hcrep⟩ :=
    compileExp_rField_const_words_correct context structs sourceLocals
      sourceGlobals sourceMemory state.locals state.memory baseAddress topAddress
      bytesInWord values index value hfield
  have hsourceValue : sourceValue = .word value := by
    apply Option.some.inj
    exact hsource.symm.trans hsourceExpected
  subst sourceValue
  refine ⟨panValuePayloadWithinLimit_word structs value, [.const value], ?_, ?_⟩
  · simpa [panValueShape] using hcompile
  · simp [evalCrepFullExpsState, evalCrepFullExpState,
      panValueFlatWords, panValueFlatWordsFuel]

end Flapjack
