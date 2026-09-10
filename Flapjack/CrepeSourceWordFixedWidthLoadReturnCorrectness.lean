import Flapjack.CrepeSourceWordLoadCorrectness
import Flapjack.CrepeReturnCorrectness

/-!
Return-boundary wrappers for the fixed-width source loads.  Their address
evaluation and memory arguments are discharged by the corresponding
expression-level load relations.
-/

namespace Flapjack

theorem compile_full_pan_value_return_load32_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α) (baseAddress topAddress bytesInWord : α)
    (address : SourceWordExp α) (addressValue value : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.load32 address.toExp) = some (.word value)) :
    evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler structs
      sourceFunctions baseAddress topAddress bytesInWord 1 sourceLocals sourceGlobals
      sourceMemory (.return (.load32 address.toExp)) =
      some (.returned (fun _ => none) sourceGlobals sourceMemory [.word value]) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem baseAddress topAddress 1 state
      (compileProg context (.return (.load32 address.toExp))) =
      some (.returned state [value]) ∧
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory [.word value])
      (.returned state [value]) := by
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWord_load32_relation
    context structs sourceLocals sourceGlobals sourceMemory state baseAddress
    topAddress bytesInWord address addressValue value hbytesInWord hlocals hlookup
    hsourceAddress hsource
  have hcompileShape : compileExp context (.load32 address.toExp) =
      ([compiled], panValueShape structs (.word value)) := by
    simpa [panValueShape] using hcompile
  have hcompiledList : evalCrepFullExps state.locals state.memory
      baseAddress topAddress [compiled] = some [value] := by
    simp [evalCrepFullExps, hcompiled]
  exact compile_full_pan_value_return_relation context structs sourceFunctions
    functions sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
    (.load32 address.toExp) (.word value) [compiled] exceptionRel hsource
    (panValuePayloadWithinLimit_word structs value) hcompileShape hcompiledList hlocals

theorem compile_full_pan_value_return_loadByte_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α) (baseAddress topAddress bytesInWord : α)
    (address : SourceWordExp α) (addressValue value : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.loadByte address.toExp) = some (.word value)) :
    evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler structs
      sourceFunctions baseAddress topAddress bytesInWord 1 sourceLocals sourceGlobals
      sourceMemory (.return (.loadByte address.toExp)) =
      some (.returned (fun _ => none) sourceGlobals sourceMemory [.word value]) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem baseAddress topAddress 1 state
      (compileProg context (.return (.loadByte address.toExp))) =
      some (.returned state [value]) ∧
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory [.word value])
      (.returned state [value]) := by
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWord_loadByte_relation
    context structs sourceLocals sourceGlobals sourceMemory state baseAddress
    topAddress bytesInWord address addressValue value hbytesInWord hlocals hlookup
    hsourceAddress hsource
  have hcompileShape : compileExp context (.loadByte address.toExp) =
      ([compiled], panValueShape structs (.word value)) := by
    simpa [panValueShape] using hcompile
  have hcompiledList : evalCrepFullExps state.locals state.memory
      baseAddress topAddress [compiled] = some [value] := by
    simp [evalCrepFullExps, hcompiled]
  exact compile_full_pan_value_return_relation context structs sourceFunctions
    functions sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
    (.loadByte address.toExp) (.word value) [compiled] exceptionRel hsource
    (panValuePayloadWithinLimit_word structs value) hcompileShape hcompiledList hlocals

end Flapjack
