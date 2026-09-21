import Flapjack.PanToCrepCallHandlerControlSafety

/-!
# Control safety for source primitive statements

Cake's `pc_compile_correct[Primitive]` branch can only expose a normal
source result after evaluating its arguments, invoking the primitive handler,
and checking the destination shape.  The source handler-safety lemma already
proves this operational fact; this file assembles it at the
`PanValueCrepProgramStateControlSafe` boundary used by the recursive
correctness theorem.
-/

namespace Flapjack

theorem panValueCrepProgramStateControlSafe_primitive
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (operator : PrimOp) (arguments : List (Exp α)) :
    PanValueCrepProgramStateControlSafe
      (.primitive name operator arguments) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  obtain ⟨hnotBroke, hnotContinued⟩ :=
    PanValueProgNotBrokeContinued_primitive primitive sourceHandler structs
      sourceFunctions baseAddress topAddress bytesInWord name operator arguments
      sourceFuel sourceLocals sourceGlobals sourceMemory sourceResult hsource
  exact panValuePcControlLabelSafe_of_not_broke_continued sourceResult crepResult
    ⟨hnotBroke, hnotContinued⟩

end Flapjack
