import Flapjack.CrepeWordExpressionContract
import Flapjack.CrepeProgramIteCorrectness
import Flapjack.CrepeProgramReturnGeneralCorrectness

/-!
Lift the scalar expression contract from the auxiliary `SourceWordExp`
datatype to the original Pancake `Exp` syntax at program boundaries.  These
are the first program-induction cases that can now be stated directly over
the source AST's `wordExp` invariant.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_return_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : Exp α) (hword : wordExp expression)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect (.return expression) := by
  exact panValueCrepProgramCorrect_return_of_expression_relation expression
    (panValueCrepExpressionCorrect_wordExp expression hword hbytesInWord hlookup)

theorem panValueCrepProgramCorrect_ite_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : Exp α) (hcondition : wordExp condition)
    (thenBranch elseBranch : Prog α)
    (hthen : PanValueCrepProgramCorrect thenBranch)
    (helse : PanValueCrepProgramCorrect elseBranch)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect (.ite condition thenBranch elseBranch) := by
  have hconditionToExp :
      (sourceWordExpOf condition hcondition).toExp = condition :=
    sourceWordExpOf_toExp condition hcondition
  simpa [hconditionToExp] using
    (panValueCrepProgramCorrect_ite_source_word
      (sourceWordExpOf condition hcondition) thenBranch elseBranch hthen helse
      hbytesInWord hlookup)

end Flapjack
