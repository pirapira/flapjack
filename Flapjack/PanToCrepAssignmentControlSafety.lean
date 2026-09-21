import Flapjack.PanToCrepCorrectnessBoundary

/-!
# Control safety for source assignments

Cake's `pc_compile_correct[Assign]` branch has no source loop-control result:
an assignment either fails while evaluating/validating its right-hand side or
returns a normal state.  This is the direct Flapjack counterpart needed to
pair the existing local-assignment state-correctness constructors with the
program correctness boundary.
-/

namespace Flapjack

theorem panValueCrepProgramStateControlSafe_assign
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (kind : VarKind) (name : VarName) (value : Exp α) :
    PanValueCrepProgramStateControlSafe (.assign kind name value) := by
  cases kind
  · intro context structs sourceFunctions functions sourceLocals sourceGlobals
      sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
      baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
      sourceResult crepResult hstate hsource hcrep
    cases sourceFuel with
    | zero =>
        simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
    | succ sourceFuel =>
        cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
            sourceMemory baseAddress topAddress bytesInWord value with
        | none =>
            simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
        | some valueResult =>
            cases hvalid : panValueAssignmentValid structs sourceLocals sourceGlobals
                .local name valueResult with
            | false =>
                simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid]
                  at hsource
            | true =>
                simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid]
                  at hsource
                cases hsource
                simp [panValuePcControlLabelSafe]
  · intro context structs sourceFunctions functions sourceLocals sourceGlobals
      sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
      baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
      sourceResult crepResult hstate hsource hcrep
    cases sourceFuel with
    | zero =>
        simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
    | succ sourceFuel =>
        cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
            sourceMemory baseAddress topAddress bytesInWord value with
        | none =>
            simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
        | some valueResult =>
            cases hvalid : panValueAssignmentValid structs sourceLocals sourceGlobals
                .global name valueResult with
            | false =>
                simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid]
                  at hsource
            | true =>
                simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid]
                  at hsource
                cases hsource
                simp [panValuePcControlLabelSafe]

end Flapjack
