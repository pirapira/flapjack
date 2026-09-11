import Flapjack.CrepeExpressionContractCorrectness
import Flapjack.CrepeProgramReturnGeneralCorrectness

/-!
Program-level correctness for a return of a one-word shaped load.  The
expression contract discharges the address compilation and source/Crep memory
agreement; the generic return constructor supplies the fuel-polymorphic
control-result boundary.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_return_load_one
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect (.return (.load .one address.toExp)) := by
  exact panValueCrepProgramCorrect_return_of_expression_relation
    (.load .one address.toExp)
    (panValueCrepExpressionCorrect_load_one address hbytesInWord hlookup)

end Flapjack
