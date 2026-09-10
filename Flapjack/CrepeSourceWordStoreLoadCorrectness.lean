import Flapjack.CrepeSourceWordStoreCorrectness
import Flapjack.CrepeSourceWordLoadReturnCorrectness
import Flapjack.CrepeSequenceCorrectness

/-!
Compose a source-word store with a one-word load return.

This is the first nontrivial program-induction instance for the source-word
correctness boundary: the store establishes the updated memory relation, and
the return theorem consumes that relation for the continuation.
-/

namespace Flapjack

theorem compile_full_pan_value_store32_load_one_source_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (baseAddress topAddress bytesInWord : α)
    (storeAddress storeValue loadAddress : SourceWordExp α)
    (storeAddressValue storeValueValue loadAddressValue loadValue : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstoreAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord storeAddress.toExp =
      some (.word storeAddressValue))
    (hstoreValue : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord storeValue.toExp =
      some (.word storeValueValue))
    (hloadAddress : evalPanValueExp structs sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory storeAddressValue (.word storeValueValue))
      baseAddress topAddress bytesInWord loadAddress.toExp =
      some (.word loadAddressValue))
    (hload : evalPanValueExp structs sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory storeAddressValue (.word storeValueValue))
      baseAddress topAddress bytesInWord (.load .one loadAddress.toExp) =
      some (.word loadValue)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 2 sourceLocals sourceGlobals sourceMemory
      (.seq (.store32 storeAddress.toExp storeValue.toExp)
        (.return (.load .one loadAddress.toExp))) =
      some (.returned (fun _ => none) sourceGlobals
        (updatePanValueMemory sourceMemory storeAddressValue (.word storeValueValue))
        [.word loadValue]) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 2 state
      (compileProg context
        (.seq (.store32 storeAddress.toExp storeValue.toExp)
          (.return (.load .one loadAddress.toExp)))) =
      some (.returned
        { state with memory := updateMemory state.memory storeAddressValue storeValueValue }
        [loadValue]) ∧
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals
        (updatePanValueMemory sourceMemory storeAddressValue (.word storeValueValue))
        [.word loadValue])
      (.returned
        { state with memory := updateMemory state.memory storeAddressValue storeValueValue }
        [loadValue]) := by
  obtain ⟨storeSource, ⟨_, _, _, _, storeCrepEval, storeRel⟩⟩ :=
    compile_full_pan_value_store32_source_word_relation context structs
      sourceFunctions functions sourceLocals sourceGlobals sourceMemory state
      primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
      bytesInWord 0 storeAddress storeValue storeAddressValue storeValueValue
      hbytesInWord hlocals hlookup hstoreAddress hstoreValue
  let storeState : CrepState α :=
    { state with memory := updateMemory state.memory storeAddressValue storeValueValue }
  obtain ⟨loadSource, loadCrep, loadRel⟩ :=
    compile_full_pan_value_return_load_one_relation context structs
      sourceFunctions functions sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory storeAddressValue (.word storeValueValue))
      storeState primitive sourceHandler crepPrimitive ffi sharedMem
      baseAddress topAddress bytesInWord loadAddress loadAddressValue loadValue
      exceptionRel hbytesInWord storeRel hlookup hloadAddress hload
  have hsequence := compile_full_pan_value_seq_normal_relation context structs
    sourceFunctions functions sourceLocals sourceGlobals sourceMemory
    sourceLocals sourceGlobals
    (updatePanValueMemory sourceMemory storeAddressValue (.word storeValueValue))
    state storeState primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord 0
    (.store32 storeAddress.toExp storeValue.toExp)
    (.return (.load .one loadAddress.toExp))
    (compileProg context (.store32 storeAddress.toExp storeValue.toExp))
    (compileProg context (.return (.load .one loadAddress.toExp)))
    (.returned (fun _ => none) sourceGlobals
      (updatePanValueMemory sourceMemory storeAddressValue (.word storeValueValue))
      [.word loadValue])
    (.returned
      { state with memory := updateMemory state.memory storeAddressValue storeValueValue }
      [loadValue]) exceptionRel rfl rfl storeSource storeCrepEval
    loadSource loadCrep loadRel
  simpa using hsequence

end Flapjack
