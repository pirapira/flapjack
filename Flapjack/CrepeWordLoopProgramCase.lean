import Flapjack.CrepeWordExpressionContract
import Flapjack.CrepeProgramWhileCorrectness

/-!
Lift the source-word `while` correctness constructor to original Pancake
expressions.  The loop-control safety premise remains explicit because it is
the semantic invariant needed by the fuel-polymorphic loop proof.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_while_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : Exp α) (hcondition : wordExp condition)
    (body : Prog α)
    (hbody : PanValueCrepProgramCorrect body)
    (hbodySafe : PanValueCrepProgramLoopControlSafe body)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect (.while condition body) := by
  have hconditionToExp :
      (sourceWordExpOf condition hcondition).toExp = condition :=
    sourceWordExpOf_toExp condition hcondition
  simpa [hconditionToExp] using
    (panValueCrepProgramCorrect_while_source_word
      (sourceWordExpOf condition hcondition) body hbody hbodySafe
      hbytesInWord hlookup)

theorem panValueCrepProgramStateCorrect_while_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : Exp α) (hcondition : wordExp condition)
    (body : Prog α)
    (hbody : PanValueCrepProgramStateCorrect body)
    (hbodySafe : PanValueCrepProgramLoopStateControlSafe body)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect (.while condition body) := by
  have hconditionToExp :
      (sourceWordExpOf condition hcondition).toExp = condition :=
    sourceWordExpOf_toExp condition hcondition
  simpa [hconditionToExp] using
    (panValueCrepProgramStateCorrect_while_source_word
      (sourceWordExpOf condition hcondition) body hbody hbodySafe
      hbytesInWord hlookup)

end Flapjack
