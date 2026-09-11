import Flapjack.CrepeStateRelation

/-!
Relation-aware ordinary fixed-width stores.

The source semantics stores a word into the structured memory map, while the
Crep semantics updates its word memory directly.  This is the memory-changing
induction case for `Store32`; `StoreByte` has the same abstract word-memory
equation and is kept for the following layer.
-/

namespace Flapjack

theorem compile_full_pan_value_store32_relation
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
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (address value : Exp α)
    (compiledAddress compiledValue : CrepExp α)
    (sourceAddress targetAddress sourceValue targetValue : α)
    (hcompileAddress : compileExp context address =
      ([compiledAddress], .one))
    (hcompileValue : compileExp context value =
      ([compiledValue], .one))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord address =
      some (.word sourceAddress))
    (hsourceValue : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord value =
      some (.word sourceValue))
    (hcrepAddress : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledAddress = some targetAddress)
    (hcrepValue : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledValue = some targetValue)
    (haddress : targetAddress = sourceAddress)
    (hvalue : targetValue = sourceValue)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory (.store32 address value) =
      some (.normal sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory sourceAddress (.word sourceValue))) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.store32 address value)) =
      some (.normal { state with
        memory := updateMemory state.memory targetAddress targetValue }) ∧
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory sourceAddress (.word sourceValue))
      { state with memory := updateMemory state.memory targetAddress targetValue } := by
  have hcompile : compileProg context (.store32 address value) =
      .store32 compiledAddress compiledValue := by
    simp [compileProg, hcompileAddress, hcompileValue]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceAddress,
      hsourceValue]
  constructor
  · simp [evalCrepFullProg, hcrepAddress, hcrepValue, haddress, hvalue]
  · refine ⟨hrel.1, hrel.2.1, ?_⟩
    simpa [haddress, hvalue] using
      (panValueCrepMemoryRel_update_word sourceMemory state.memory
        sourceAddress sourceValue hrel.2.2)

end Flapjack
