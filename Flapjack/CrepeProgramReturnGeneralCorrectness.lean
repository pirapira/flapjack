import Flapjack.CrepeProgramReturnFuelRelation
import Flapjack.CrepeProgramRelation

/-!
Program-level correctness for an arbitrary source return expression.  The
expression proof is supplied as a compilation/evaluation witness; this
constructor handles the source and Crep return boundaries and their fuel
polymorphism.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_return_of_expression_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : Exp α)
    (hvalue : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
      (baseAddress topAddress bytesInWord : α) (sourceValue : PanValue α),
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression = some sourceValue →
      panValuePayloadWithinLimit structs sourceValue = true ∧
      ∃ compiled,
        compileExp context expression =
          (compiled, panValueShape structs sourceValue) ∧
        evalCrepFullExps state.locals state.memory
          baseAddress topAddress compiled =
          some (panValueFlatWords sourceValue)) :
    PanValueCrepProgramCorrect (.return expression) := by
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
          cases hsourceValue : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord expression with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceValue] at hsource
          | some sourceValue =>
              obtain ⟨hvalid, compiled, hcompile, hcompiled⟩ := hvalue
                context structs sourceLocals sourceGlobals sourceMemory state
                baseAddress topAddress bytesInWord sourceValue hsourceValue
              have hresult := compile_full_pan_value_return_relation_fuel
                context structs sourceFunctions functions sourceLocals sourceGlobals
                sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                baseAddress topAddress bytesInWord sourceFuel targetFuel expression
                sourceValue compiled exceptionRel hsourceValue hvalid hcompile
                hcompiled hrel
              have hsourceEq := Option.some.inj (hresult.1.symm.trans hsource)
              have hcrepEq := Option.some.inj (hresult.2.1.symm.trans hcrep)
              cases hsourceEq
              cases hcrepEq
              exact hresult.2.2

end Flapjack
