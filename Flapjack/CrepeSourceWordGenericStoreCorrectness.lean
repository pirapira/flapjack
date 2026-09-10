import Flapjack.CrepeExpressionRelation

/-!
Source-word correctness for the general `Store` statement.

The compiler lowers a word store through two fresh temporary slots.  The
explicit stability hypotheses are the freshness interface needed by this
lowering: compiled address/value expressions must keep their evaluations when
the temporaries are installed.
-/

namespace Flapjack

theorem compile_full_pan_value_store_source_word_relation
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
    (address value : SourceWordExp α) (addressValue valueValue : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsourceValue : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord value.toExp = some (.word valueValue))
    (haddressStable : ∀ compiled,
      compileExp context address.toExp = ([compiled], .one) →
      evalCrepFullExp
      (updateCrepLocal state.locals (context.maxVar + 1) addressValue)
      state.memory baseAddress topAddress compiled = some addressValue)
    (hvalueStable : ∀ compiled,
      compileExp context value.toExp = ([compiled], .one) →
      evalCrepFullExp
      (updateCrepLocal state.locals (context.maxVar + 1) addressValue)
      state.memory baseAddress topAddress compiled = some valueValue) :
    evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler structs
      sourceFunctions baseAddress topAddress bytesInWord 4 sourceLocals sourceGlobals
      sourceMemory (.store address.toExp value.toExp) =
      some (.normal sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory addressValue (.word valueValue))) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem baseAddress topAddress 4 state
      (compileProg context (.store address.toExp value.toExp)) =
      some (.normal
        { state with memory := updateMemory state.memory addressValue valueValue }) ∧
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory addressValue (.word valueValue))
      { state with memory := updateMemory state.memory addressValue valueValue } := by
  obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
    compileSourceWordExp_relation context structs sourceLocals
    sourceGlobals sourceMemory state.locals state.memory baseAddress topAddress
    bytesInWord hbytesInWord hlocals.2.1 hlookup address addressValue hsourceAddress
  obtain ⟨compiledValue, hcompileValue, hcrepValue⟩ :=
    compileSourceWordExp_relation context structs sourceLocals
    sourceGlobals sourceMemory state.locals state.memory baseAddress topAddress
    bytesInWord hbytesInWord hlocals.2.1 hlookup value valueValue hsourceValue
  have haddressStable' := haddressStable compiledAddress hcompileAddress
  have hvalueStable' := hvalueStable compiledValue hcompileValue
  have hstoreMemory : panValueStoreWithAccess sourceMemory bytesInWord
      addressValue (.word valueValue) =
      some (updatePanValueMemory sourceMemory addressValue (.word valueValue)) := by
    simp [panValueStoreWithAccess, panValueFlatStoreWords, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatOffset, updatePanValueMemory]
  have hsource : evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler
      structs sourceFunctions baseAddress topAddress bytesInWord 4
      sourceLocals sourceGlobals sourceMemory (.store address.toExp value.toExp) =
      some (.normal sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory addressValue (.word valueValue))) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceAddress, hsourceValue,
      hstoreMemory]
  have hcompile : compileProg context (.store address.toExp value.toExp) =
      nestedDecs [context.maxVar + 1, context.maxVar + 2]
        [compiledAddress, compiledValue]
        (crepNestedSeq
          (stores (.var (context.maxVar + 1)) [.var (context.maxVar + 2)]
            0 context.bytesInWord)) := by
    simp [compileProg, hcompileAddress, hcompileValue, freshNames,
      nestedDecs, stores, crepNestedSeq]
  have hrestore :
      restoreCrepLocal
          (restoreCrepLocal
            (updateCrepLocal
              (updateCrepLocal state.locals (context.maxVar + 1) addressValue)
              (context.maxVar + 2) valueValue)
            (context.maxVar + 2) (state.locals (context.maxVar + 2)))
          (context.maxVar + 1) (state.locals (context.maxVar + 1)) = state.locals := by
    funext current
    by_cases haddress : current = context.maxVar + 1
    · simp [restoreCrepLocal, haddress]
    by_cases hvalue : current = context.maxVar + 2
    · simp [restoreCrepLocal, hvalue]
    · simp [restoreCrepLocal, updateCrepLocal, haddress, hvalue]
  have hcrep : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 4 state
      (compileProg context (.store address.toExp value.toExp)) =
      some (.normal
        { state with memory := updateMemory state.memory addressValue valueValue }) := by
    rw [hcompile]
    simp [nestedDecs, crepNestedSeq, stores, evalCrepFullProg,
      evalCrepFullExp, hcrepAddress, hvalueStable', updateCrepLocal,
      restoreCrepResult, hrestore]
  have hmemory := panValueCrepMemoryRel_update_word sourceMemory state.memory
    addressValue valueValue hlocals.2.2
  exact ⟨hsource, hcrep, ⟨hlocals.1, hlocals.2.1, by
    simpa [updateMemory] using hmemory⟩⟩

end Flapjack
