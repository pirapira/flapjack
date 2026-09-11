import Flapjack.CrepeCallArgumentCorrectness

/-!
Constructor assembly for ordinary calls whose arguments are word-valued.

The argument adapter supplies the compiler-side evaluation witness, while the
callee and handler simulation remains a separate relation premise.  This is
the call case used by the program-correctness induction.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_call_of_word_arguments
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
    (hword : ∀ expression ∈ arguments, wordExp expression)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstate : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (state : CrepState α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory state)
    (hcall : ∀ (context : CompileContext α) (structs : StructContext)
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
      (crepResult : CrepControlResult α)
      (compiledArguments : List (CrepExp α)) (argumentValues : List α),
      evalPanValueCallWithPrimitiveCallsAndFfi
        primitive sourceHandler structs sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel
        sourceLocals sourceGlobals sourceMemory info function arguments =
        some sourceResult →
      evalCrepFullExps state.locals state.memory baseAddress topAddress
        compiledArguments = some argumentValues →
      evalCrepFullCall functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel state (compiledInfo context) function
        compiledArguments = some crepResult →
      panValueCrepControlRel structs context exceptionRel sourceResult crepResult) :
    PanValueCrepProgramCorrect (.call info function arguments) := by
  apply panValueCrepProgramCorrect_call_of_relation info compiledInfo function
    arguments hcompile
  exact panValueCrepCallCorrect_of_word_arguments info compiledInfo function
    arguments hword hbytesInWord hlookup hstate hcall

end Flapjack
