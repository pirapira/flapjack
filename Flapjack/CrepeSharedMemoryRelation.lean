import Flapjack.CrepeStateRelation

/-!
Relation-aware shared-memory boundaries.

The existing equations establish the evaluator plumbing and the handler
transition.  These wrappers add the source-to-Crep state relation required by
the program correctness induction, leaving the concrete shared-memory model
and its post-handler relation explicit.
-/

namespace Flapjack

theorem compile_full_pan_value_shMemLoad_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state targetState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (size : OpSize) (name : VarName) (slot : Nat)
    (address value oldValue : α)
    (sourceAddress : Exp α) (compiledAddress : CrepExp α)
    (lookup : lookupInfo name context.vars = some (.one, [slot]))
    (haddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord sourceAddress = some (.word address))
    (hmemory : sourceMemory address = some (.word value))
    (hcompiledAddress : firstCompiledExp context sourceAddress =
      some compiledAddress)
    (hcrepAddress : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledAddress = some address)
    (hsharedMem : sharedMem (loadMemOp size) slot address state =
      some targetState)
    (hlocals : sourceLocals name = some (.word oldValue))
    (htargetRel : panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals
      sourceMemory targetState) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.shMemLoad size .local name sourceAddress) =
      some (.normal (updatePanValueMap sourceLocals name (.word value))
        sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context
        (.shMemLoad size .local name sourceAddress)) =
      some (.normal targetState) ∧
    panValueCrepControlRel structs context (fun _ _ _ => True)
      (.normal (updatePanValueMap sourceLocals name (.word value))
        sourceGlobals sourceMemory) (.normal targetState) := by
  have hsteps := compile_full_pan_value_shMemLoad_word_correct
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state targetState primitive sourceHandler crepPrimitive ffi
    sharedMem baseAddress topAddress bytesInWord fuel size name slot address
    value oldValue sourceAddress compiledAddress lookup haddress hmemory
    hcompiledAddress hcrepAddress hsharedMem hlocals
  exact ⟨hsteps.1, hsteps.2,
    by simpa [panValueCrepControlRel] using htargetRel⟩

theorem compile_full_pan_value_shMemStore_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state targetState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (size : OpSize) (address value : α)
    (sourceAddress sourceValue : Exp α)
    (compiledAddress compiledValue : CrepExp α)
    (haddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord sourceAddress = some (.word address))
    (hvalue : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord sourceValue = some (.word value))
    (hcompiledAddress : firstCompiledExp context sourceAddress =
      some compiledAddress)
    (hcompiledValue : firstCompiledExp context sourceValue =
      some compiledValue)
    (hcrepAddress : evalCrepFullExp
      (updateCrepLocal state.locals (context.maxVar + 1) value) state.memory
      baseAddress topAddress compiledAddress = some address)
    (hcrepValue : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledValue = some value)
    (hsharedMem : sharedMem (storeMemOp size) (context.maxVar + 1) address
      { state with
        locals := updateCrepLocal state.locals (context.maxVar + 1) value } =
      some targetState)
    (htargetRel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory address (.word value))
      { targetState with
        locals := restoreCrepLocal targetState.locals
          (context.maxVar + 1) (state.locals (context.maxVar + 1)) }) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 2)
      sourceLocals sourceGlobals sourceMemory
      (.shMemStore size sourceAddress sourceValue) =
      some (.normal sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory address (.word value))) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (compileProg context (.shMemStore size sourceAddress sourceValue)) =
      some (.normal
        { targetState with
          locals := restoreCrepLocal targetState.locals
            (context.maxVar + 1) (state.locals (context.maxVar + 1)) }) ∧
    panValueCrepControlRel structs context (fun _ _ _ => True)
      (.normal sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory address (.word value)))
      (.normal
        { targetState with
          locals := restoreCrepLocal targetState.locals
            (context.maxVar + 1) (state.locals (context.maxVar + 1)) }) := by
  have hsteps := compile_full_pan_value_shMemStore_word_correct
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state targetState primitive sourceHandler crepPrimitive ffi
    sharedMem baseAddress topAddress bytesInWord fuel size address value
    sourceAddress sourceValue compiledAddress compiledValue haddress hvalue
    hcompiledAddress hcompiledValue hcrepAddress hcrepValue hsharedMem
  exact ⟨hsteps.1, hsteps.2,
    by simpa [panValueCrepControlRel] using htargetRel⟩

end Flapjack
