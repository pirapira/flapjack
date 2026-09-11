import Flapjack.CrepeProgramRelation

/-!
The target-side normal-call inversion has two branches: a normal callee result
or a returned callee result followed by destination assignment.  When the
source callee is known to return, recursive program correctness rules out the
first branch.  This lemma isolates that branch selection for declaration-call
correctness.
-/

namespace Flapjack

theorem crepReturnedCall_normal_branch_impossible_of_body_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (calleeContext : CompileContext α)
    (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceCalleeLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (caller : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceBody : Prog α) (targetBody : CrepProg α)
    (sourceBodyLocals sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceValues : List (PanValue α))
    (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α)
    (hbodyCorrect : PanValueCrepProgramCorrect sourceBody)
    (hrelCallee : panValueCrepStateRel structs calleeContext
      sourceCalleeLocals sourceGlobals sourceCalleeMemory
      { locals := targetCalleeLocals, memory := caller.memory })
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceCalleeLocals sourceGlobals sourceCalleeMemory sourceBody =
      some (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        sourceValues))
    (hcompileBody : compileProg calleeContext sourceBody = targetBody)
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory } targetBody =
      some (.normal targetCallee)) :
    False := by
  have hcrepBody' : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory }
      (compileProg calleeContext sourceBody) = some (.normal targetCallee) := by
    rw [hcompileBody]
    exact hcrepBody
  have hbodyRel := hbodyCorrect calleeContext structs sourceFunctions functions
    sourceCalleeLocals sourceGlobals sourceCalleeMemory
    { locals := targetCalleeLocals, memory := caller.memory }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory sourceValues)
    (.normal targetCallee) hrelCallee hsourceBody hcrepBody'
  simp [panValueCrepControlRel] at hbodyRel

end Flapjack
