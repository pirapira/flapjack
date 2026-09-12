import Flapjack.CrepeExpressionFieldContractCorrectness
import Flapjack.CrepeProgramReturnGeneralCorrectness

/-!
Program-level correctness for returning a selected field of a constant-word
record.  The field expression contract supplies the selected Crep value; the
generic return constructor supplies the source/Crep control boundary.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_return_rField_const_words
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (values : List α) (index : Nat) (value : α)
    (hfield : values[index]? = some value) :
    PanValueCrepProgramCorrect
      (.return (.rField index (.rStruct (values.map (fun value => .const value))))) := by
  exact panValueCrepProgramCorrect_return_of_expression_relation
    (.rField index (.rStruct (values.map (fun value => .const value))))
    (panValueCrepExpressionCorrect_rField_const_words values index value hfield)

theorem panValueCrepProgramStateCorrect_return_rField_const_words
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (values : List α) (index : Nat) (value : α)
    (hfield : values[index]? = some value) :
    PanValueCrepProgramStateCorrect
      (.return (.rField index (.rStruct (values.map (fun value => .const value))))) := by
  exact panValueCrepProgramStateCorrect_return_of_expression_relation
    (.rField index (.rStruct (values.map (fun value => .const value))))
    (panValueCrepExpressionStateCorrect_rField_const_words values index value hfield)

end Flapjack
