import Flapjack.CrepeExpressionContractCorrectness
import Flapjack.CrepeProgramReturnGeneralCorrectness

/-!
Program-level correctness for a return of a Load32 expression.  The
expression contract supplies the fixed-width memory agreement; the generic
return constructor supplies the source/Crep control boundary and its
arbitrary-fuel statement.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_return_load32
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
    PanValueCrepProgramCorrect (.return (.load32 address.toExp)) := by
  exact panValueCrepProgramCorrect_return_of_expression_relation
    (.load32 address.toExp)
    (panValueCrepExpressionCorrect_load32 address hbytesInWord hlookup)

theorem panValueCrepProgramStateCorrect_return_load32
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
    PanValueCrepProgramStateCorrect (.return (.load32 address.toExp)) := by
  exact panValueCrepProgramStateCorrect_return_of_expression_relation
    (.load32 address.toExp)
    (panValueCrepExpressionStateCorrect_load32 address hbytesInWord hlookup)

end Flapjack
