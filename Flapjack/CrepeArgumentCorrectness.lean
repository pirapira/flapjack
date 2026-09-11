import Flapjack.CrepeExpressionContractCorrectness

/-!
List-level argument correctness.

The expression contract supplies one compiled Crep expression list per source
expression.  This theorem lifts those witnesses through `compileArgs` and the
target list evaluator, producing exactly the flattened source argument list.
-/

namespace Flapjack

theorem compileArgs_evalCrepFullExps_of_expression_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expressionCorrect : ∀ expression : Exp α,
      PanValueCrepExpressionCorrect expression)
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α)) (values : List (PanValue α))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expressions = some values) :
    ∃ compiled,
      compileArgs context expressions = compiled ∧
      evalCrepFullExps state.locals state.memory
        baseAddress topAddress compiled =
        some (values.flatMap panValueFlatWords) := by
  have evalAppend : ∀ (left right : List (CrepExp α))
      (leftValues rightValues : List α),
      evalCrepFullExps state.locals state.memory baseAddress topAddress left =
        some leftValues →
      evalCrepFullExps state.locals state.memory baseAddress topAddress right =
        some rightValues →
      evalCrepFullExps state.locals state.memory baseAddress topAddress
          (left ++ right) = some (leftValues ++ rightValues) := by
    intro left
    induction left with
    | nil =>
        intro right leftValues rightValues hleft hright
        have hleft' : leftValues = [] := by
          simpa [evalCrepFullExps] using hleft
        subst leftValues
        simpa [evalCrepFullExps] using hright
    | cons head tail ih =>
        intro right leftValues rightValues hleft hright
        cases hhead : evalCrepFullExp state.locals state.memory
            baseAddress topAddress head with
        | none =>
            simp [evalCrepFullExps, hhead] at hleft
        | some headValue =>
            cases htail : evalCrepFullExps state.locals state.memory
                baseAddress topAddress tail with
            | none =>
                simp [evalCrepFullExps, hhead, htail] at hleft
            | some tailValues =>
                have hleftValues : leftValues = headValue :: tailValues := by
                  have hsome : some (headValue :: tailValues) = some leftValues := by
                    simpa [evalCrepFullExps, hhead, htail] using hleft
                  exact (Option.some.inj hsome).symm
                subst leftValues
                have htailAppend := ih right tailValues rightValues htail hright
                simp only [List.cons_append, evalCrepFullExps, hhead]
                rw [htailAppend]
                simp
  induction expressions generalizing values with
  | nil =>
      have hvalues : values = [] := by
        have hsome : some [] = some values := by
          simpa [evalPanValueExps, evalPanValueExp.evalPanValueExps] using hsource
        exact (Option.some.inj hsome).symm
      subst values
      exact ⟨[], by simp [compileArgs], by simp [evalCrepFullExps]⟩
  | cons expression expressions ih =>
      change evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
        sourceMemory baseAddress topAddress bytesInWord
        (expression :: expressions) = some values at hsource
      cases hhead : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord expression with
      | none =>
          simp [evalPanValueExp.evalPanValueExps, hhead] at hsource
      | some value =>
          cases htail : evalPanValueExps structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord expressions with
          | none =>
              have htail' :
                  evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                    sourceMemory baseAddress topAddress bytesInWord expressions = none := by
                simpa [evalPanValueExps] using htail
              simp [evalPanValueExp.evalPanValueExps, hhead, htail'] at hsource
          | some tailValues =>
              have htail' :
                  evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                    sourceMemory baseAddress topAddress bytesInWord expressions =
                    some tailValues := by
                simpa [evalPanValueExps] using htail
              have hvalues : values = value :: tailValues := by
                have hsome : some (value :: tailValues) = some values := by
                  simpa [evalPanValueExp.evalPanValueExps, hhead, htail'] using hsource
                exact (Option.some.inj hsome).symm
              subst values
              obtain ⟨_, compiledHead, hcompileHead, hcompiledHead⟩ :=
                expressionCorrect expression context structs sourceLocals
                  sourceGlobals sourceMemory state baseAddress topAddress
                  bytesInWord value hrel hhead
              obtain ⟨compiledTail, hcompileTail, hcompiledTail⟩ :=
                ih tailValues htail
              refine ⟨compiledHead ++ compiledTail, ?_, ?_⟩
              · simp [compileArgs, hcompileHead, hcompileTail]
              · exact evalAppend compiledHead compiledTail
                  (panValueFlatWords value)
                  (tailValues.flatMap panValueFlatWords)
                  hcompiledHead hcompiledTail

end Flapjack
