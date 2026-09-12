import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeStoreRelation

/-!
Lift the structural source-word expression relation through the relation-aware
`Store32` statement rule.  The store theorem itself is already state-threaded;
this wrapper supplies both expression obligations compositionally.
-/

namespace Flapjack

theorem compile_full_pan_value_store32_source_word_relation
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
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (address value : SourceWordExp α)
    (addressValue valueValue : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsourceValue : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord value.toExp = some (.word valueValue)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.store32 address.toExp value.toExp) =
      some (.normal sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory addressValue (.word valueValue))) ∧
    ∃ compiledAddress compiledValue,
      compileExp context address.toExp = ([compiledAddress], .one) ∧
      compileExp context value.toExp = ([compiledValue], .one) ∧
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress (fuel + 1) state
        (compileProg context (.store32 address.toExp value.toExp)) =
      some (.normal { state with
        memory := updateMemory state.memory addressValue valueValue }) ∧
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory addressValue (.word valueValue))
      { state with memory := updateMemory state.memory addressValue valueValue } := by
  obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup address addressValue hsourceAddress
  obtain ⟨compiledValue, hcompileValue, hcrepValue⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup value valueValue hsourceValue
  have hstore := compile_full_pan_value_store32_relation context structs
    sourceFunctions functions sourceLocals sourceGlobals sourceMemory state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord fuel address.toExp value.toExp compiledAddress compiledValue
    addressValue addressValue valueValue valueValue hcompileAddress hcompileValue
    hsourceAddress hsourceValue hcrepAddress hcrepValue rfl rfl hlocals
  exact ⟨hstore.1, ⟨compiledAddress, compiledValue, hcompileAddress,
    hcompileValue, hstore.2.1, hstore.2.2⟩⟩

theorem compile_full_pan_value_store32_source_word_state_relation
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
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (address value : SourceWordExp α)
    (addressValue valueValue : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsourceValue : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord value.toExp = some (.word valueValue)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.store32 address.toExp value.toExp) =
      some (.normal sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory addressValue (.word valueValue))) ∧
    ∃ compiledAddress compiledValue,
      compileExp context address.toExp = ([compiledAddress], .one) ∧
      compileExp context value.toExp = ([compiledValue], .one) ∧
      evalCrepFullProgState functions crepPrimitive ffi sharedMem
        baseAddress topAddress (fuel + 1) state
        (compileProg context (.store32 address.toExp value.toExp)) =
      some (.normal { state with
        memory := updateMemory state.memory addressValue valueValue }) ∧
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory addressValue (.word valueValue))
      { state with memory := updateMemory state.memory addressValue valueValue } := by
  obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup address addressValue hsourceAddress
  obtain ⟨compiledValue, hcompileValue, hcrepValue⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup value valueValue hsourceValue
  obtain ⟨compiledAddress', hcompileAddress', hnoGlobalAddress⟩ :=
    compileSourceWordExp_noGlobal context structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord hlookup address addressValue
      hsourceAddress
  obtain ⟨compiledValue', hcompileValue', hnoGlobalValue⟩ :=
    compileSourceWordExp_noGlobal context structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord hlookup value valueValue
      hsourceValue
  have haddressEq : compiledAddress = compiledAddress' := by
    have hpair : ([compiledAddress], Shape.one) = ([compiledAddress'], Shape.one) :=
      hcompileAddress.symm.trans hcompileAddress'
    exact (List.cons.inj (congrArg Prod.fst hpair)).1
  have hvalueEq : compiledValue = compiledValue' := by
    have hpair : ([compiledValue], Shape.one) = ([compiledValue'], Shape.one) :=
      hcompileValue.symm.trans hcompileValue'
    exact (List.cons.inj (congrArg Prod.fst hpair)).1
  subst compiledAddress'
  subst compiledValue'
  have hcrepAddressState :
      evalCrepFullExpState state baseAddress topAddress compiledAddress =
        some addressValue := by
    calc
      evalCrepFullExpState state baseAddress topAddress compiledAddress =
          evalCrepFullExp state.locals state.memory
            baseAddress topAddress compiledAddress :=
        evalCrepFullExpState_eq_of_noGlobal state baseAddress topAddress
          compiledAddress hnoGlobalAddress
      _ = some addressValue := hcrepAddress
  have hcrepValueState :
      evalCrepFullExpState state baseAddress topAddress compiledValue =
        some valueValue := by
    calc
      evalCrepFullExpState state baseAddress topAddress compiledValue =
          evalCrepFullExp state.locals state.memory
            baseAddress topAddress compiledValue :=
        evalCrepFullExpState_eq_of_noGlobal state baseAddress topAddress
          compiledValue hnoGlobalValue
      _ = some valueValue := hcrepValue
  have hstore := compile_full_pan_value_store32_state_relation context structs
    sourceFunctions functions sourceLocals sourceGlobals sourceMemory state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord fuel address.toExp value.toExp compiledAddress compiledValue
    addressValue addressValue valueValue valueValue hcompileAddress hcompileValue
    hsourceAddress hsourceValue hcrepAddressState hcrepValueState rfl rfl hlocals
  exact ⟨hstore.1, ⟨compiledAddress, compiledValue, hcompileAddress,
    hcompileValue, hstore.2.1, hstore.2.2⟩⟩

theorem compile_full_pan_value_storeByte_source_word_relation
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
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (address value : SourceWordExp α)
    (addressValue valueValue : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsourceValue : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord value.toExp = some (.word valueValue)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.storeByte address.toExp value.toExp) =
      some (.normal sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory addressValue (.word valueValue))) ∧
    ∃ compiledAddress compiledValue,
      compileExp context address.toExp = ([compiledAddress], .one) ∧
      compileExp context value.toExp = ([compiledValue], .one) ∧
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress (fuel + 1) state
        (compileProg context (.storeByte address.toExp value.toExp)) =
      some (.normal { state with
        memory := updateMemory state.memory addressValue valueValue }) ∧
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory addressValue (.word valueValue))
      { state with memory := updateMemory state.memory addressValue valueValue } := by
  obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup address addressValue hsourceAddress
  obtain ⟨compiledValue, hcompileValue, hcrepValue⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup value valueValue hsourceValue
  have hstore := compile_full_pan_value_storeByte_relation context structs
    sourceFunctions functions sourceLocals sourceGlobals sourceMemory state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord fuel address.toExp value.toExp compiledAddress compiledValue
    addressValue addressValue valueValue valueValue hcompileAddress hcompileValue
    hsourceAddress hsourceValue hcrepAddress hcrepValue rfl rfl hlocals
  exact ⟨hstore.1, ⟨compiledAddress, compiledValue, hcompileAddress,
    hcompileValue, hstore.2.1, hstore.2.2⟩⟩

end Flapjack
