import Flapjack.CrepeWordExpressionContract
import Flapjack.CrepeProgramExtCallSourceWordStateCorrectness

/-!
Lift the scalar external-call correctness constructor to original Pancake
expressions.  FFI correspondence and temporary freshness remain explicit
because they describe the handler boundary and sequential temporary bindings.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_extCall_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (hconfiguration : wordExp configuration)
    (hconfigurationLength : wordExp configurationLength)
    (harray : wordExp array)
    (harrayLength : wordExp arrayLength)
    (hffi : ∀ (sourceHandler : PanValueFfiHandler α)
      (ffi : CrepFfiHandler α), panValueCrepExtCallCorrect sourceHandler ffi)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hfresh : ∀ (context : CompileContext α) (expression : SourceWordExp α)
      (compiled : CrepExp α),
      compileExp context expression.toExp = ([compiled], .one) →
      ∀ temporary, context.maxVar < temporary →
        temporary ∉ crepExpVars compiled) :
    PanValueCrepProgramCorrect
      (.extCall function configuration configurationLength array arrayLength) := by
  have hconfigurationToExp :
      (sourceWordExpOf configuration hconfiguration).toExp = configuration :=
    sourceWordExpOf_toExp configuration hconfiguration
  have hconfigurationLengthToExp :
      (sourceWordExpOf configurationLength hconfigurationLength).toExp =
        configurationLength :=
    sourceWordExpOf_toExp configurationLength hconfigurationLength
  have harrayToExp : (sourceWordExpOf array harray).toExp = array :=
    sourceWordExpOf_toExp array harray
  have harrayLengthToExp :
      (sourceWordExpOf arrayLength harrayLength).toExp = arrayLength :=
    sourceWordExpOf_toExp arrayLength harrayLength
  simpa [hconfigurationToExp, hconfigurationLengthToExp, harrayToExp,
    harrayLengthToExp] using
    (panValueCrepProgramCorrect_extCall_source_word function
      (sourceWordExpOf configuration hconfiguration)
      (sourceWordExpOf configurationLength hconfigurationLength)
      (sourceWordExpOf array harray)
      (sourceWordExpOf arrayLength harrayLength)
      hffi hbytesInWord hlookup hfresh)

theorem panValueCrepProgramStateCorrect_extCall_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (hconfiguration : wordExp configuration)
    (hconfigurationLength : wordExp configurationLength)
    (harray : wordExp array)
    (harrayLength : wordExp arrayLength)
    (hffi : ∀ (sourceHandler : PanValueFfiHandler α)
      (ffi : CrepFfiHandler α), panValueCrepExtCallCorrect sourceHandler ffi)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hfresh : ∀ (context : CompileContext α) (expression : SourceWordExp α)
      (compiled : CrepExp α),
      compileExp context expression.toExp = ([compiled], .one) →
      ∀ temporary, context.maxVar < temporary →
        temporary ∉ crepExpVars compiled) :
    PanValueCrepProgramStateCorrect
      (.extCall function configuration configurationLength array arrayLength) := by
  have hconfigurationToExp :
      (sourceWordExpOf configuration hconfiguration).toExp = configuration :=
    sourceWordExpOf_toExp configuration hconfiguration
  have hconfigurationLengthToExp :
      (sourceWordExpOf configurationLength hconfigurationLength).toExp =
        configurationLength :=
    sourceWordExpOf_toExp configurationLength hconfigurationLength
  have harrayToExp : (sourceWordExpOf array harray).toExp = array :=
    sourceWordExpOf_toExp array harray
  have harrayLengthToExp :
      (sourceWordExpOf arrayLength harrayLength).toExp = arrayLength :=
    sourceWordExpOf_toExp arrayLength harrayLength
  simpa [hconfigurationToExp, hconfigurationLengthToExp, harrayToExp,
    harrayLengthToExp] using
    (panValueCrepProgramStateCorrect_extCall_source_word function
      (sourceWordExpOf configuration hconfiguration)
      (sourceWordExpOf configurationLength hconfigurationLength)
      (sourceWordExpOf array harray)
      (sourceWordExpOf arrayLength harrayLength)
      hffi hbytesInWord hlookup hfresh)

end Flapjack
