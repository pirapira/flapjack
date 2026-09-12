import Flapjack.CrepeExpressionRelation

/-!
One-word source loads are the expression-level memory boundary needed by the
store and control-flow relations.  The source load is shape-directed while
the one-word Crep lowering is a direct load from the related word memory.
-/

namespace Flapjack

theorem compileSourceWord_load_one_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (baseAddress topAddress bytesInWord : α)
    (address : SourceWordExp α) (addressValue value : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.load .one address.toExp) =
      some (.word value)) :
    ∃ compiled,
      compileExp context (.load .one address.toExp) = ([compiled], .one) ∧
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value := by
  obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup address addressValue hsourceAddress
  have hsourceMemory : sourceMemory addressValue = some (.word value) := by
    have hsource' := hsource
    simp [evalPanValueExp, hsourceAddress, panValueFlatLoad,
      panValueFlatLoadFuel, panValueFlatReadWord] at hsource'
    cases hmemory' : sourceMemory addressValue with
    | none => simp [hmemory'] at hsource'
    | some current =>
        cases current with
        | word current =>
            have hvalue : current = value := by
              simpa [hmemory'] using hsource'.2
            simp [hvalue]
        | rStruct fields => simp [hmemory'] at hsource'
        | nStruct name fields => simp [hmemory'] at hsource'
  have hmemory : panValueWordMemory sourceMemory addressValue =
      state.memory addressValue := congrFun hlocals.2.2 addressValue
  have htargetMemory : state.memory addressValue = some value := by
    rw [← hmemory]
    simp [panValueWordMemory, hsourceMemory]
  refine ⟨.load compiledAddress, ?_, ?_⟩
  · simp [compileExp, hcompileAddress, loadShape]
  · simp [evalCrepFullExp, hcrepAddress, htargetMemory]

theorem compileSourceWord_load_one_state_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (baseAddress topAddress bytesInWord : α)
    (address : SourceWordExp α) (addressValue value : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.load .one address.toExp) =
      some (.word value)) :
    ∃ compiled,
      compileExp context (.load .one address.toExp) = ([compiled], .one) ∧
      evalCrepFullExpState state baseAddress topAddress compiled = some value := by
  obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
    compileSourceWordExp_state_relation context structs sourceLocals sourceGlobals
      sourceMemory state baseAddress topAddress bytesInWord hbytesInWord
      hlocals.2.1 hlookup address addressValue hsourceAddress
  have hsourceMemory : sourceMemory addressValue = some (.word value) := by
    have hsource' := hsource
    simp [evalPanValueExp, hsourceAddress, panValueFlatLoad,
      panValueFlatLoadFuel, panValueFlatReadWord] at hsource'
    cases hmemory' : sourceMemory addressValue with
    | none => simp [hmemory'] at hsource'
    | some current =>
        cases current with
        | word current =>
            have hvalue : current = value := by
              simpa [hmemory'] using hsource'.2
            simp [hvalue]
        | rStruct fields => simp [hmemory'] at hsource'
        | nStruct name fields => simp [hmemory'] at hsource'
  have hmemory : panValueWordMemory sourceMemory addressValue =
      state.memory addressValue := congrFun hlocals.2.2 addressValue
  have htargetMemory : state.memory addressValue = some value := by
    rw [← hmemory]
    simp [panValueWordMemory, hsourceMemory]
  refine ⟨.load compiledAddress, ?_, ?_⟩
  · simp [compileExp, hcompileAddress, loadShape]
  · simp [evalCrepFullExpState, hcrepAddress, htargetMemory]

theorem compileSourceWord_load32_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (baseAddress topAddress bytesInWord : α)
    (address : SourceWordExp α) (addressValue value : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.load32 address.toExp) =
      some (.word value)) :
    ∃ compiled,
      compileExp context (.load32 address.toExp) = ([compiled], .one) ∧
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value := by
  obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup address addressValue hsourceAddress
  have hsourceMemory : sourceMemory addressValue = some (.word value) := by
    have hsource' := hsource
    simp [evalPanValueExp, hsourceAddress] at hsource'
    cases hmemory' : sourceMemory addressValue with
    | none => simp [hmemory'] at hsource'
    | some current =>
        cases current with
        | word current =>
            have hvalue : current = value := by
              simpa [hmemory'] using hsource'
            simp [hvalue]
        | rStruct fields => simp [hmemory'] at hsource'
        | nStruct name fields => simp [hmemory'] at hsource'
  have hmemory : panValueWordMemory sourceMemory addressValue =
      state.memory addressValue := congrFun hlocals.2.2 addressValue
  have htargetMemory : state.memory addressValue = some value := by
    rw [← hmemory]
    simp [panValueWordMemory, hsourceMemory]
  refine ⟨.load32 compiledAddress, ?_, ?_⟩
  · simp [compileExp, hcompileAddress]
  · simp [evalCrepFullExp, hcrepAddress, htargetMemory]

theorem compileSourceWord_loadByte_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (baseAddress topAddress bytesInWord : α)
    (address : SourceWordExp α) (addressValue value : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.loadByte address.toExp) =
      some (.word value)) :
    ∃ compiled,
      compileExp context (.loadByte address.toExp) = ([compiled], .one) ∧
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value := by
  obtain ⟨compiledAddress, hcompileAddress, hcrepAddress⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup address addressValue hsourceAddress
  have hsourceMemory : sourceMemory addressValue = some (.word value) := by
    have hsource' := hsource
    simp [evalPanValueExp, hsourceAddress] at hsource'
    cases hmemory' : sourceMemory addressValue with
    | none => simp [hmemory'] at hsource'
    | some current =>
        cases current with
        | word current =>
            have hvalue : current = value := by
              simpa [hmemory'] using hsource'
            simp [hvalue]
        | rStruct fields => simp [hmemory'] at hsource'
        | nStruct name fields => simp [hmemory'] at hsource'
  have hmemory : panValueWordMemory sourceMemory addressValue =
      state.memory addressValue := congrFun hlocals.2.2 addressValue
  have htargetMemory : state.memory addressValue = some value := by
    rw [← hmemory]
    simp [panValueWordMemory, hsourceMemory]
  refine ⟨.loadByte compiledAddress, ?_, ?_⟩
  · simp [compileExp, hcompileAddress]
  · simp [evalCrepFullExp, hcrepAddress, htargetMemory]

end Flapjack
