import Flapjack.CrepeProgramBasicRelation

/-!
The scalar constant-return case for the compositional Pancake program
relation.  This is the first value-producing base case: Pancake clears source
locals at a return boundary, while Crep returns with its current flattened
locals, so the proof explicitly switches to the empty-source-local relation.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_return_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (value : α) :
    PanValueCrepProgramCorrect (.return (.const value)) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          have hlimit : panValuePayloadWithinLimit structs (.word value) = true :=
            panValuePayloadWithinLimit_word structs value
          have hsourceResult :
              PanValueControlResult.returned (fun _ => none) sourceGlobals
                sourceMemory [.word value] = sourceResult := by
            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
              evalPanValueExp, hlimit] using hsource
          have hcrepResult :
              CrepControlResult.returned state [value] = crepResult := by
            simpa [compileProg, compileExp, evalCrepFullProg,
              evalCrepFullExps, evalCrepFullExp] using hcrep
          cases hsourceResult
          cases hcrepResult
          have hstateRel :
              panValueCrepStateRel structs context
                (fun _ => none) sourceGlobals sourceMemory state := by
            exact ⟨hrel.1, panValueCrepLocalsRel_empty structs context
              state.locals, hrel.2.2⟩
          exact ⟨hstateRel, panValueCrepValuesRel_singleton (.word value)⟩

end Flapjack
