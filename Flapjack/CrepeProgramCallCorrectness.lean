import Flapjack.CrepeProgramRelation

/-!
Program-level correctness for ordinary function calls.

The call evaluator is shared by source `Prog.call` and by declaration calls.
This predicate packages the remaining callee simulation: once a source call and
its lowered Crep call produce related control results, the enclosing program
constructor is immediate.  Keeping the compiled call information as a
function of the compile context is important because handlers and destinations
are lowered using that context.
-/

namespace Flapjack

def PanValueCrepCallCorrect
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : CompileContext α →
      Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α)) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α),
    evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory info function arguments =
      some sourceResult →
    evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state (compiledInfo context)
      function (compileArgs context arguments) = some crepResult →
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult

theorem panValueCrepProgramCorrect_call_of_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : CompileContext α →
      Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α))
    (hcompile : ∀ (context : CompileContext α),
      compileProg context (.call info function arguments) =
        .call (compiledInfo context) function (compileArgs context arguments))
    (hcall : PanValueCrepCallCorrect info compiledInfo function arguments) :
    PanValueCrepProgramCorrect (.call info function arguments) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          have hsourceCall :
              evalPanValueCallWithPrimitiveCallsAndFfi
                primitive sourceHandler structs sourceFunctions
                baseAddress topAddress bytesInWord sourceFuel
                sourceLocals sourceGlobals sourceMemory info function arguments =
                some sourceResult := by
            simpa [evalPanValueProgWithPrimitiveCallsAndFfi] using hsource
          have hcrepCall :
              evalCrepFullCall functions crepPrimitive ffi sharedMem
                baseAddress topAddress targetFuel state
                (compiledInfo context) function (compileArgs context arguments) =
                some crepResult := by
            rw [hcompile context] at hcrep
            simpa [evalCrepFullProg] using hcrep
          exact hcall context structs sourceFunctions functions
            sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
            crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
            sourceFuel targetFuel exceptionRel sourceResult crepResult
            hsourceCall hcrepCall


def PanValueCrepCallStateCorrect
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : CompileContext α →
      Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α)) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α),
    evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory info function arguments =
      some sourceResult →
    evalCrepFullCallState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state (compiledInfo context)
      function (compileArgs context arguments) = some crepResult →
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult

theorem panValueCrepProgramStateCorrect_call_of_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : CompileContext α →
      Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α))
    (hcompile : ∀ (context : CompileContext α),
      compileProg context (.call info function arguments) =
        .call (compiledInfo context) function (compileArgs context arguments))
    (hcall : PanValueCrepCallStateCorrect info compiledInfo function arguments) :
    PanValueCrepProgramStateCorrect (.call info function arguments) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          have hsourceCall :
              evalPanValueCallWithPrimitiveCallsAndFfi
                primitive sourceHandler structs sourceFunctions
                baseAddress topAddress bytesInWord sourceFuel
                sourceLocals sourceGlobals sourceMemory info function arguments =
                some sourceResult := by
            simpa [evalPanValueProgWithPrimitiveCallsAndFfi] using hsource
          have hcrepCall :
              evalCrepFullCallState functions crepPrimitive ffi sharedMem
                baseAddress topAddress targetFuel state
                (compiledInfo context) function (compileArgs context arguments) =
                some crepResult := by
            rw [hcompile context] at hcrep
            simpa [evalCrepFullProgState] using hcrep
          exact hcall context structs sourceFunctions functions
            sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
            crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
            sourceFuel targetFuel exceptionRel sourceResult crepResult
            hsourceCall hcrepCall


end Flapjack
