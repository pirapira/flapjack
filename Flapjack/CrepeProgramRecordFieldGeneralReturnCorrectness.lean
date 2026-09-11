import Flapjack.CrepeExpressionFieldGeneralCorrectness
import Flapjack.CrepeProgramReturnGeneralCorrectness

/-!
Program-level correctness for returning a selected field of a record whose
fields are arbitrary scalar source expressions.  The expression theorem
supplies the selected Crep value; the generic return constructor supplies the
source/Crep control boundary and its arbitrary-fuel statement.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_return_rField_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (fields : List (SourceWordExp α)) (index : Nat)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect
      (.return (.rField index (.rStruct (fields.map SourceWordExp.toExp)))) := by
  exact panValueCrepProgramCorrect_return_of_expression_relation
    (.rField index (.rStruct (fields.map SourceWordExp.toExp)))
    (panValueCrepExpressionCorrect_rField_word_record fields index
      hbytesInWord hlookup)

end Flapjack
