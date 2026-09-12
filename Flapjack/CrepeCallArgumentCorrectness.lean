import Flapjack.CrepeArgumentCorrectness
import Flapjack.CrepeProgramCallCorrectness

/-!
Package localized argument compilation/evaluation for ordinary calls.  The
callee and handler simulation remains an explicit relation premise; this
theorem supplies the compiler-side argument witness needed by that relation.
-/

namespace Flapjack

theorem panValueCrepCallCorrect_of_expression_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : CompileContext α →
      Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α))
    (hexpression : ∀ expression ∈ arguments,
      PanValueCrepExpressionCorrect expression)
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
    PanValueCrepCallCorrect info compiledInfo function arguments := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueCallWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hvalues : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord arguments with
      | none =>
          simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues] at hsource
      | some argumentValues =>
          obtain ⟨compiledArguments, hcompileArguments, hcompiledArguments⟩ :=
            compileArgs_evalCrepFullExps_of_expression_correct context structs sourceLocals
              sourceGlobals sourceMemory state baseAddress topAddress bytesInWord
              arguments argumentValues hexpression
              (hstate context structs sourceLocals sourceGlobals sourceMemory state)
              hvalues
          have hcrep' :
              evalCrepFullCall functions crepPrimitive ffi sharedMem
                baseAddress topAddress targetFuel state (compiledInfo context) function
                compiledArguments = some crepResult := by
            rw [← hcompileArguments]
            exact hcrep
          exact hcall context structs sourceFunctions functions sourceLocals sourceGlobals
            sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
            baseAddress topAddress bytesInWord (sourceFuel + 1) targetFuel exceptionRel
            sourceResult crepResult compiledArguments
            (argumentValues.flatMap panValueFlatWords) hsource
            hcompiledArguments hcrep'

theorem panValueCrepCallCorrect_of_word_arguments
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : CompileContext α →
      Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α))
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
    PanValueCrepCallCorrect info compiledInfo function arguments := by
  exact panValueCrepCallCorrect_of_expression_correct info compiledInfo function
    arguments
    (fun expression hmember => panValueCrepExpressionCorrect_wordExp expression
      (hword expression hmember) hbytesInWord hlookup)
    hstate hcall

theorem panValueCrepCallStateCorrect_of_expression_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : CompileContext α →
      Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α))
    (hexpression : ∀ expression ∈ arguments,
      PanValueCrepExpressionStateCorrect expression)
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
      evalCrepFullExpsState state baseAddress topAddress compiledArguments =
        some argumentValues →
      evalCrepFullCallState functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel state (compiledInfo context) function
        compiledArguments = some crepResult →
      panValueCrepControlRel structs context exceptionRel sourceResult crepResult) :
    PanValueCrepCallStateCorrect info compiledInfo function arguments := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueCallWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hvalues : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord arguments with
      | none =>
          simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues] at hsource
      | some argumentValues =>
          obtain ⟨compiledArguments, hcompileArguments, hcompiledArguments⟩ :=
            compileArgs_evalCrepFullExpsState_of_expression_correct context structs
              sourceLocals sourceGlobals sourceMemory state baseAddress topAddress
              bytesInWord arguments argumentValues hexpression
              (hstate context structs sourceLocals sourceGlobals sourceMemory state)
              hvalues
          have hcrep' :
              evalCrepFullCallState functions crepPrimitive ffi sharedMem
                baseAddress topAddress targetFuel state (compiledInfo context) function
                compiledArguments = some crepResult := by
            rw [← hcompileArguments]
            exact hcrep
          exact hcall context structs sourceFunctions functions sourceLocals sourceGlobals
            sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
            baseAddress topAddress bytesInWord (sourceFuel + 1) targetFuel exceptionRel
            sourceResult crepResult compiledArguments
            (argumentValues.flatMap panValueFlatWords) hsource
            hcompiledArguments hcrep'

theorem panValueCrepCallStateCorrect_of_word_arguments
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (compiledInfo : CompileContext α →
      Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (Exp α))
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
      evalCrepFullExpsState state baseAddress topAddress compiledArguments =
        some argumentValues →
      evalCrepFullCallState functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel state (compiledInfo context) function
        compiledArguments = some crepResult →
      panValueCrepControlRel structs context exceptionRel sourceResult crepResult) :
    PanValueCrepCallStateCorrect info compiledInfo function arguments := by
  exact panValueCrepCallStateCorrect_of_expression_correct info compiledInfo function
    arguments
    (fun expression hmember => panValueCrepExpressionStateCorrect_wordExp expression
      (hword expression hmember) hbytesInWord hlookup)
    hstate hcall

end Flapjack
