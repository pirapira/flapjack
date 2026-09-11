import Flapjack.PanValues

/-!
The source ExtCall evaluator first computes an argument list and then applies
the word-valued FFI pattern.  This file exposes that intermediate boundary so
the program correctness proof can perform the pattern inversion separately
from expression evaluation.
-/

namespace Flapjack

def evalPanValueExtCallValues
    (handler : PanValueFfiHandler α) (function : FunName)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (values : List (PanValue α)) : Option (PanValueControlResult α) :=
  match values with
  | [.word configuration, .word configurationLength, .word array,
      .word arrayLength] =>
      (handler function configuration configurationLength array arrayLength locals).bind
        fun locals => some (.normal locals globals memory)
  | _ => none

theorem evalPanValueExtCall_values
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (sourceResult : PanValueControlResult α)
    (hsource : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive handler structs functions baseAddress topAddress bytesInWord (fuel + 1)
      locals globals memory
      (.extCall function configuration configurationLength array arrayLength) =
      some sourceResult) :
    ∃ values,
      evalPanValueExps structs locals globals memory baseAddress topAddress bytesInWord
          [configuration, configurationLength, array, arrayLength] = some values ∧
      evalPanValueExtCallValues handler function locals globals memory values =
        some sourceResult := by
  have hsource' := hsource
  simp only [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource'
  cases hvalues : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord
      [configuration, configurationLength, array, arrayLength] with
  | none =>
      simp [hvalues] at hsource'
  | some values =>
      rw [hvalues] at hsource'
      refine ⟨values, rfl, ?_⟩
      unfold evalPanValueExtCallValues
      exact hsource'

theorem evalPanValueExtCallValues_word_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : PanValueFfiHandler α) (function : FunName)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (values : List (PanValue α))
    (sourceResult : PanValueControlResult α)
    (hresult : evalPanValueExtCallValues handler function locals globals memory
      values = some sourceResult) :
    ∃ configuration configurationLength array arrayLength locals',
      values = [.word configuration, .word configurationLength,
        .word array, .word arrayLength] ∧
      handler function configuration configurationLength array arrayLength locals =
        some locals' ∧
      sourceResult = .normal locals' globals memory := by
  simp only [evalPanValueExtCallValues] at hresult
  split at hresult
  · rename_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ values configuration
      configurationLength array arrayLength
    cases hhandler : handler function configuration configurationLength array
        arrayLength locals with
    | none =>
        simp [hhandler] at hresult
    | some locals' =>
        refine ⟨configuration, configurationLength, array, arrayLength,
          locals', rfl, hhandler, ?_⟩
        simp [hhandler] at hresult
        exact hresult.symm
  · simp_all

end Flapjack
