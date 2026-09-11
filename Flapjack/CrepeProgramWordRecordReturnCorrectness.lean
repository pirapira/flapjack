import Flapjack.CrepeExpressionContractCorrectness
import Flapjack.CrepeProgramReturnGeneralCorrectness

/-!
Program-level correctness for returning a record whose fields are scalar word
expressions.  The expression contract supplies the recursive flattening and
payload bound; the generic return constructor supplies the source/Crep control
boundary and its arbitrary-fuel statement.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_return_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (fields : List (SourceWordExp α))
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsize : fields.length ≤ 32) :
    PanValueCrepProgramCorrect
      (.return (.rStruct (fields.map SourceWordExp.toExp))) := by
  exact panValueCrepProgramCorrect_return_of_expression_relation
    (.rStruct (fields.map SourceWordExp.toExp))
    (panValueCrepExpressionCorrect_word_record fields hbytesInWord hlookup hsize)

end Flapjack
