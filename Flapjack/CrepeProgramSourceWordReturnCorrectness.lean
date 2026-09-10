import Flapjack.CrepeProgramSourceWordReturnRelation
import Flapjack.CrepeProgramRelation

/-!
Program-level source-word return correctness.

The expression relation supplies the single lowered Crep expression, while
the fuel-polymorphic return boundary supplies the source/target control
results.  This is the reusable return constructor for the compositional
Pancake correctness induction.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_return_source_word
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
    PanValueCrepProgramCorrect (.return expression.toExp) := by
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
          cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord expression.toExp with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
          | some sourceValue =>
              obtain ⟨value, hword⟩ := evalPanValueExp_sourceWord_inv
                structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord context hrel.2.1
                (fun name value hvalue =>
                  hlookup context sourceLocals name value hvalue)
                expression sourceValue hvalue
              have hsourceValue :
                  evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                    baseAddress topAddress bytesInWord expression.toExp =
                    some (.word value) := by
                rw [hvalue, hword]
              have hresult := compile_full_pan_value_return_source_word_relation_fuel
                context structs sourceFunctions functions sourceLocals sourceGlobals
                sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                baseAddress topAddress bytesInWord sourceFuel targetFuel expression value
                exceptionRel (hbytesInWord context bytesInWord)
                (hlookup context sourceLocals) hrel hsourceValue
              rcases hresult with
                ⟨compiled, hcompile, hcompiled, hsourceResult, hcrepResult,
                  hrelation⟩
              have hsourceEq := Option.some.inj (hsourceResult.symm.trans hsource)
              have hcrepEq := Option.some.inj (hcrepResult.symm.trans hcrep)
              cases hsourceEq
              cases hcrepEq
              exact hrelation

end Flapjack
