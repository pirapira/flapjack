import Flapjack.CrepeExpressionRelation

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

end Flapjack
