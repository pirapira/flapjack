import Flapjack.CrepeStateRelation

/-!
Relation-aware correctness for the compiled call constructor.

The call evaluator and compiler equation leave callee and handler behavior as
explicit witnesses.  This theorem adds the source-to-Crep control relation
that the full program induction carries across the call boundary.
-/

namespace Flapjack

theorem compile_full_pan_value_call_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α))
    (compiledArguments : List (CrepExp α))
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hcompileProg : compileProg context (.call info function arguments) =
      .call compiledInfo function (compileArgs context arguments))
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory info function arguments =
      some sourceResult)
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledInfo function compiledArguments =
      some crepResult)
    (hrel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.call info function arguments) = some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.call info function arguments)) = some crepResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult := by
  have hresult := compile_full_pan_value_call_compose
    context structs sourceFunctions functions
    sourceLocals sourceGlobals sourceMemory state
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord fuel
    info compiledInfo function arguments compiledArguments
    sourceResult crepResult hcompileArgs hcompileProg hsourceCall hcrepCall
  exact ⟨hresult.1, hresult.2, hrel⟩

end Flapjack
