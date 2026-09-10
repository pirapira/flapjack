import Flapjack.CrepeStateRelation

/-!
Relation-aware exception propagation at the source-to-Crep boundary.
-/

namespace Flapjack

theorem compile_full_pan_value_raise_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord value : α)
    (exception : ExceptionId) (exceptionCode : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hexception : exceptionRel exception (.word value) exceptionCode) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 3
      sourceLocals sourceGlobals sourceMemory
      (.raise exception (.const value)) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.word value)) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 10 state
      (compileProg context (.raise exception (.const value))) =
      some (.raised
        { state with memory := updateMemory state.memory 0 value }
        exceptionCode) ∧
    panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory exception (.word value)
      { state with memory := updateMemory state.memory 0 value }
      exceptionCode 0 := by
  have hresult := compile_full_pan_value_raise_word_correct
    context structs sourceFunctions functions
    sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord value
    exception exceptionCode hlookup
  have hstate := panValueCrepRaisedStateRel_word_spill
    structs context sourceLocals sourceGlobals sourceMemory state 0 value hrel
  exact ⟨hresult.1, hresult.2, hstate, hexception⟩

theorem compile_full_pan_value_raise_two_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord left right : α)
    (exception : ExceptionId) (exceptionCode : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hexception : exceptionRel exception
      (.rStruct [.word left, .word right]) exceptionCode) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 5
      sourceLocals sourceGlobals sourceMemory
      (.raise exception (.rStruct [.const left, .const right])) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.rStruct [.word left, .word right])) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 15 state
      (compileProg context
        (.raise exception (.rStruct [.const left, .const right]))) =
      some (.raised
        { state with
          memory := updateMemory
            (updateMemory state.memory 0 left)
            (0 + bytesInWord) right }
        exceptionCode) ∧
    panValueCrepRaisedControlRelExcept structs context exceptionRel
      sourceGlobals sourceMemory exception
      (.rStruct [.word left, .word right])
      { locals := state.locals
        memory := updateMemory
          (updateMemory state.memory 0 left) (0 + bytesInWord) right }
      exceptionCode
      (fun address => address = 0 ∨ address = 0 + bytesInWord) := by
  have hresult := compile_full_pan_value_raise_two_word_correct
    context structs sourceFunctions functions
    sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord left right
    exception exceptionCode hlookup hbytesInWord
  have hstate := panValueCrepRaisedStateRel_two_word_spill
    structs context sourceLocals sourceGlobals sourceMemory state
    0 bytesInWord left right hrel
  exact ⟨hresult.1, hresult.2, hstate, hexception⟩

end Flapjack
