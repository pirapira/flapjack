import Flapjack.PanToCrepCallHandlerControlSafety
import Flapjack.CrepeProgramDeclarationContract

namespace Flapjack

theorem panValueCrepProgramStateControlSafe_dec
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (hbody : ∀ (primitive : PanPrimitiveHandler α)
      (handler : PanValueFfiHandler α) (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α),
      PanValueProgNotBrokeContinued primitive handler structs functions
        baseAddress topAddress bytesInWord body) :
    PanValueCrepProgramStateControlSafe (.dec name shape value body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hnot := PanValueProgNotBrokeContinued_dec primitive sourceHandler structs
    sourceFunctions baseAddress topAddress bytesInWord name shape value body
    (hbody primitive sourceHandler structs sourceFunctions baseAddress topAddress
      bytesInWord)
  exact panValuePcControlLabelSafe_of_not_broke_continued sourceResult crepResult
    (hnot sourceFuel sourceLocals sourceGlobals sourceMemory sourceResult hsource)

end Flapjack
