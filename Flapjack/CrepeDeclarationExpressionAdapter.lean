import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramAssignmentCorrectness

/-!
Adapter from the universal expression-correctness contract to the witness
shape consumed by the generic declaration constructor.  The declaration
proof fixes the compiled shape in advance, whereas the expression contract
returns the source value's shape; successful compilation identifies the two.
-/

namespace Flapjack

theorem panValueCrepExpressionCorrect_compiled_list
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : Exp α) (hvalue : PanValueCrepExpressionCorrect expression)
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (baseAddress topAddress bytesInWord : α)
    (compiledValues : List (CrepExp α)) (shape : Shape)
    (sourceValue : PanValue α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hcompile : compileExp context expression = (compiledValues, shape))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue) :
    ∃ values,
      evalCrepFullExps state.locals state.memory baseAddress topAddress
        compiledValues = some values ∧
      compiledValues.length = values.length ∧
      panValueFlatWords sourceValue = values := by
  obtain ⟨_hlimit, compiled, hcompiledShape, hcompiled⟩ :=
    hvalue context structs sourceLocals sourceGlobals sourceMemory state
      baseAddress topAddress bytesInWord sourceValue hrel hsource
  have hpair : (compiled, panValueShape structs sourceValue) =
      (compiledValues, shape) := hcompiledShape.symm.trans hcompile
  cases hpair
  let values := panValueFlatWords sourceValue
  refine ⟨values, ?_, ?_, rfl⟩
  · simpa [values] using hcompiled
  · exact evalCrepFullExps_length state.locals state.memory baseAddress topAddress
      compiledValues values (by simpa [values] using hcompiled)

end Flapjack
