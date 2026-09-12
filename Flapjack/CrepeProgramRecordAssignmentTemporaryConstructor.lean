import Flapjack.CrepeProgramRecordAssignmentConstructor
import Flapjack.CrepeNestedDecsAssignmentInversion
import Flapjack.CrepeTemporaryAssignmentCorrectness

/-!
The temporary structured-assignment constructor.  Fresh compiled values are
bound by nested declarations, copied into the destination slots, and restored
on exit.  The compiler-derived obligations are explicit because they are
discharged by the static-context invariant in the final syntax induction.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_assign_local_record_temporary
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (fields : List (SourceWordExp α))
    (hrecord : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
      (baseAddress topAddress bytesInWord : α) (sourceValue : PanValue α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory state →
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord
        (.rStruct (fields.map SourceWordExp.toExp)) = some sourceValue →
      ∃ values compiled,
        sourceValue = .rStruct (values.map (fun value => .word value)) ∧
        compileExp context (.rStruct (fields.map SourceWordExp.toExp)) =
          (compiled, .comb (values.map (fun _ => .one))) ∧
        compiled.length = values.length ∧
        evalCrepFullExps state.locals state.memory baseAddress topAddress
          compiled = some values)
    (htemporaryPath : ∀ (context : CompileContext α)
      (sourceValue : PanValue α) (values : List α) (compiled : List (CrepExp α))
      (shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      sourceValue = .rStruct (values.map (fun value => .word value)) →
      compileExp context (.rStruct (fields.map SourceWordExp.toExp)) =
        (compiled, .comb (values.map (fun _ => .one))) →
      distinctLists slots (compiled.flatMap crepExpVars) = false ∧
      slots.length = values.length ∧
      CrepDistinctNames slots ∧
      (∀ temporary ∈ freshNames context slots.length 1,
        ∀ expression ∈ compiled, temporary ∉ crepExpVars expression) ∧
      CrepDistinctNames (freshNames context slots.length 1) ∧
      (∀ slot ∈ slots, ∀ temporary ∈ freshNames context slots.length 1,
        slot ≠ temporary))
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α)) (oldValue : PanValue α),
      sourceLocals name = some oldValue →
      ∃ shape slots, lookupInfo name context.vars = some (shape, slots))
    (hnoalias : ∀ (context : CompileContext α) (shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      ∀ oldName oldShape oldSlots,
        oldName ≠ name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        ∀ slot ∈ slots, slot ∉ oldSlots) :
    PanValueCrepProgramCorrect
      (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hsourceInfo : ∃ sourceValue oldValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord
        (.rStruct (fields.map SourceWordExp.toExp)) = some sourceValue ∧
      sourceLocals name = some oldValue ∧
      panShapeMatches (panValueShape structs sourceValue)
        (panValueShape structs oldValue) = true ∧
      sourceResult = .normal (updatePanValueMap sourceLocals name sourceValue)
        sourceGlobals sourceMemory := by
    cases sourceFuel with
    | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
    | succ sourceFuel =>
        have hsource' : evalPanValueProgWithPrimitiveCallsAndFfi
            primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord (sourceFuel + 1)
            sourceLocals sourceGlobals sourceMemory
            (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
            some sourceResult := by simpa using hsource
        obtain ⟨sourceValue, oldValue, hvalue, hold, hvalid, hresult⟩ :=
          evalPanValueProg_assign_local_inv primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord sourceFuel sourceLocals sourceGlobals
            sourceMemory name (.rStruct (fields.map SourceWordExp.toExp)) sourceResult hsource'
        exact ⟨sourceValue, oldValue, hvalue, hold, hvalid, hresult⟩
  obtain ⟨sourceValue, oldValue, hvalue, hold, hvalid, hsourceResult⟩ := hsourceInfo
  obtain ⟨values, compiled, hrecordValue, hcompile, hcompiledLength, hcompiled⟩ :=
    hrecord context structs sourceLocals sourceGlobals sourceMemory state
      baseAddress topAddress bytesInWord sourceValue hrel hvalue
  obtain ⟨shape, slots, hlookupName⟩ := hlookup context sourceLocals oldValue hold
  have holdRel := hrel.2.1 name oldValue shape slots hold hlookupName
  have hnewShape : panValueShape structs sourceValue =
      .comb (values.map (fun _ => .one)) := by
    rw [hrecordValue]
    simp [panValueShape]
  have hshapeNewContext : panShapeMatches
      (.comb (values.map (fun _ => .one))) shape = true := by
    have htrans := panShapeMatches_trans
      (panValueShape structs sourceValue) (panValueShape structs oldValue) shape
      hvalid holdRel.1
    simpa [hnewShape] using htrans
  have hshapeContext := panShapeMatches_word_record_shape_inv values shape
    hshapeNewContext
  have hlookupExact : lookupInfo name context.vars =
      some (.comb (values.map (fun _ => .one)), slots) := by
    simpa [hshapeContext] using hlookupName
  obtain ⟨hnotDistinct, hslotLength, hslotsDistinct, hcompiledFresh,
      htemporaryDistinct, hnoOverlap⟩ := htemporaryPath context sourceValue values
    compiled shape slots hlookupName hrecordValue hcompile
  let temporarySlots := freshNames context slots.length 1
  have htemporaryLength : temporarySlots.length = values.length := by
    simp [temporarySlots, freshNames, hslotLength]
  have hcompileProg :
      compileProg context
        (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
      nestedDecs temporarySlots compiled
        (crepNestedSeq (slots.zipWith
          (fun slot temporary => .assign slot (.var temporary)) temporarySlots)) := by
    simp [temporarySlots, compileProg, hlookupExact, hcompile, hslotLength,
      hcompiledLength, hnotDistinct, freshNames]
  rw [hcompileProg] at hcrep
  obtain ⟨nestedFuel, innerResult, htargetFuel, hnested, hrestore⟩ :=
    crepNestedDecsEval_of_eval functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state temporarySlots compiled
      (crepNestedSeq (slots.zipWith
        (fun slot temporary => .assign slot (.var temporary)) temporarySlots))
      crepResult htemporaryDistinct
      (by exact htemporaryLength.trans hcompiledLength.symm) hcrep
  have hbodyEval := evalCrepFullExps_varList_updateCrepLocalList
    state.locals state.memory baseAddress topAddress temporarySlots values
    htemporaryLength htemporaryDistinct
  have hbodyResult := crepNestedDecsEval_assignList_inv
    functions crepPrimitive ffi sharedMem baseAddress topAddress nestedFuel state
    temporarySlots compiled values
    (crepNestedSeq (slots.zipWith
      (fun slot temporary => .assign slot (.var temporary)) temporarySlots))
    innerResult (by exact htemporaryLength.trans hcompiledLength.symm)
    htemporaryDistinct hcompiledFresh hcompiled hnested
  rw [← crepAssignZipWith_map_right] at hbodyResult
  have hbodyTarget := evalCrepFullProg_assignList_inv
    functions crepPrimitive ffi sharedMem baseAddress topAddress nestedFuel
    { state with locals := updateCrepLocalList state.locals temporarySlots values }
    slots (temporarySlots.map (fun temporary => .var temporary)) values innerResult
    (by simpa [htemporaryLength] using hslotLength)
    hslotsDistinct
    (by
      intro slot hslot expression hexpression
      obtain ⟨temporary, htemporaryMem, htemporaryEq⟩ :=
        List.mem_map.1 hexpression
      subst expression
      simpa [crepExpVars] using
        (hnoOverlap slot hslot temporary htemporaryMem))
    hbodyEval hbodyResult
  have hinner : innerResult = .normal { state with
      locals := updateCrepLocalList
        (updateCrepLocalList state.locals temporarySlots values) slots values } := by
    exact hbodyTarget
  have hrestored := restoreCrepResultList_normal_updateList state.locals
    (updateCrepLocalList
      (updateCrepLocalList state.locals temporarySlots values) slots values)
    temporarySlots slots values state.memory state.globals htemporaryLength hslotLength
    hslotsDistinct
    (by
      intro temporary htemporaryMem hslot
      exact (hnoOverlap temporary hslot temporary htemporaryMem) rfl)
    rfl
  have hcrepResult : crepResult = .normal { state with
      locals := updateCrepLocalList state.locals slots values } := by
    have hrestored' := hrestore
    rw [hinner] at hrestored'
    rw [hrestored] at hrestored'
    exact hrestored'.symm
  have hnoalias' := hnoalias context shape slots hlookupName
  have hrel' := panValueCrepLocalsRel_update_word_list structs context sourceLocals
    state.locals name slots values hrel.2.1 hlookupExact hslotLength
    hslotsDistinct hnoalias'
  cases hrecordValue
  cases hsourceResult
  cases hcrepResult
  exact ⟨hrel.1, hrel', hrel.2.2⟩

theorem panValueCrepProgramStateCorrect_assign_local_record_temporary
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (fields : List (SourceWordExp α))
    (hrecord : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
      (baseAddress topAddress bytesInWord : α) (sourceValue : PanValue α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory state →
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord
        (.rStruct (fields.map SourceWordExp.toExp)) = some sourceValue →
      ∃ values compiled,
        sourceValue = .rStruct (values.map (fun value => .word value)) ∧
        compileExp context (.rStruct (fields.map SourceWordExp.toExp)) =
          (compiled, .comb (values.map (fun _ => .one))) ∧
        compiled.length = values.length ∧
        evalCrepFullExpsState state baseAddress topAddress compiled =
          some values)
    (htemporaryPath : ∀ (context : CompileContext α)
      (sourceValue : PanValue α) (values : List α) (compiled : List (CrepExp α))
      (shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      sourceValue = .rStruct (values.map (fun value => .word value)) →
      compileExp context (.rStruct (fields.map SourceWordExp.toExp)) =
        (compiled, .comb (values.map (fun _ => .one))) →
      distinctLists slots (compiled.flatMap crepExpVars) = false ∧
      slots.length = values.length ∧
      CrepDistinctNames slots ∧
      (∀ temporary ∈ freshNames context slots.length 1,
        ∀ expression ∈ compiled, temporary ∉ crepExpVars expression) ∧
      CrepDistinctNames (freshNames context slots.length 1) ∧
      (∀ slot ∈ slots, ∀ temporary ∈ freshNames context slots.length 1,
        slot ≠ temporary))
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α)) (oldValue : PanValue α),
      sourceLocals name = some oldValue →
      ∃ shape slots, lookupInfo name context.vars = some (shape, slots))
    (hnoalias : ∀ (context : CompileContext α) (shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      ∀ oldName oldShape oldSlots,
        oldName ≠ name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        ∀ slot ∈ slots, slot ∉ oldSlots) :
    PanValueCrepProgramStateCorrect
      (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hsourceInfo : ∃ sourceValue oldValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord
        (.rStruct (fields.map SourceWordExp.toExp)) = some sourceValue ∧
      sourceLocals name = some oldValue ∧
      panShapeMatches (panValueShape structs sourceValue)
        (panValueShape structs oldValue) = true ∧
      sourceResult = .normal (updatePanValueMap sourceLocals name sourceValue)
        sourceGlobals sourceMemory := by
    cases sourceFuel with
    | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
    | succ sourceFuel =>
        have hsource' : evalPanValueProgWithPrimitiveCallsAndFfi
            primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord (sourceFuel + 1)
            sourceLocals sourceGlobals sourceMemory
            (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
            some sourceResult := by simpa using hsource
        obtain ⟨sourceValue, oldValue, hvalue, hold, hvalid, hresult⟩ :=
          evalPanValueProg_assign_local_inv primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord sourceFuel sourceLocals sourceGlobals
            sourceMemory name (.rStruct (fields.map SourceWordExp.toExp)) sourceResult hsource'
        exact ⟨sourceValue, oldValue, hvalue, hold, hvalid, hresult⟩
  obtain ⟨sourceValue, oldValue, hvalue, hold, hvalid, hsourceResult⟩ := hsourceInfo
  obtain ⟨values, compiled, hrecordValue, hcompile, hcompiledLength, hcompiled⟩ :=
    hrecord context structs sourceLocals sourceGlobals sourceMemory state
      baseAddress topAddress bytesInWord sourceValue hrel hvalue
  obtain ⟨shape, slots, hlookupName⟩ := hlookup context sourceLocals oldValue hold
  have holdRel := hrel.2.1 name oldValue shape slots hold hlookupName
  have hnewShape : panValueShape structs sourceValue =
      .comb (values.map (fun _ => .one)) := by
    rw [hrecordValue]
    simp [panValueShape]
  have hshapeNewContext : panShapeMatches
      (.comb (values.map (fun _ => .one))) shape = true := by
    have htrans := panShapeMatches_trans
      (panValueShape structs sourceValue) (panValueShape structs oldValue) shape
      hvalid holdRel.1
    simpa [hnewShape] using htrans
  have hshapeContext := panShapeMatches_word_record_shape_inv values shape
    hshapeNewContext
  have hlookupExact : lookupInfo name context.vars =
      some (.comb (values.map (fun _ => .one)), slots) := by
    simpa [hshapeContext] using hlookupName
  obtain ⟨hnotDistinct, hslotLength, hslotsDistinct, hcompiledFresh,
      htemporaryDistinct, hnoOverlap⟩ := htemporaryPath context sourceValue values
    compiled shape slots hlookupName hrecordValue hcompile
  let temporarySlots := freshNames context slots.length 1
  have htemporaryLength : temporarySlots.length = values.length := by
    simp [temporarySlots, freshNames, hslotLength]
  have hcompileProg :
      compileProg context
        (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
      nestedDecs temporarySlots compiled
        (crepNestedSeq (slots.zipWith
          (fun slot temporary => .assign slot (.var temporary)) temporarySlots)) := by
    simp [temporarySlots, compileProg, hlookupExact, hcompile, hslotLength,
      hcompiledLength, hnotDistinct, freshNames]
  rw [hcompileProg] at hcrep
  obtain ⟨nestedFuel, innerResult, htargetFuel, hnested, hrestore⟩ :=
    crepNestedDecsStateEval_of_eval functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state temporarySlots compiled
      (crepNestedSeq (slots.zipWith
        (fun slot temporary => .assign slot (.var temporary)) temporarySlots))
      crepResult htemporaryDistinct
      (by exact htemporaryLength.trans hcompiledLength.symm) hcrep
  have hbodyEval := evalCrepFullExpsState_varList_updateCrepLocalList
    state baseAddress topAddress temporarySlots values
    htemporaryLength htemporaryDistinct
  have hbodyResult := crepNestedDecsStateEval_assignList_inv
    functions crepPrimitive ffi sharedMem baseAddress topAddress nestedFuel state
    temporarySlots compiled values
    (crepNestedSeq (slots.zipWith
      (fun slot temporary => .assign slot (.var temporary)) temporarySlots))
    innerResult (by exact htemporaryLength.trans hcompiledLength.symm)
    htemporaryDistinct hcompiledFresh hcompiled hnested
  rw [← crepAssignZipWith_map_right] at hbodyResult
  have hbodyTarget := evalCrepFullProgState_assignList_inv
    functions crepPrimitive ffi sharedMem baseAddress topAddress nestedFuel
    { state with locals := updateCrepLocalList state.locals temporarySlots values }
    slots (temporarySlots.map (fun temporary => .var temporary)) values innerResult
    (by simpa [htemporaryLength] using hslotLength)
    hslotsDistinct
    (by
      intro slot hslot expression hexpression
      obtain ⟨temporary, htemporaryMem, htemporaryEq⟩ :=
        List.mem_map.1 hexpression
      subst expression
      simpa [crepExpVars] using
        (hnoOverlap slot hslot temporary htemporaryMem))
    hbodyEval hbodyResult
  have hinner : innerResult = .normal { state with
      locals := updateCrepLocalList
        (updateCrepLocalList state.locals temporarySlots values) slots values } := by
    exact hbodyTarget
  have hrestored := restoreCrepResultList_normal_updateList state.locals
    (updateCrepLocalList
      (updateCrepLocalList state.locals temporarySlots values) slots values)
    temporarySlots slots values state.memory state.globals htemporaryLength hslotLength
    hslotsDistinct
    (by
      intro temporary htemporaryMem hslot
      exact (hnoOverlap temporary hslot temporary htemporaryMem) rfl)
    rfl
  have hcrepResult : crepResult = .normal { state with
      locals := updateCrepLocalList state.locals slots values } := by
    have hrestored' := hrestore
    rw [hinner] at hrestored'
    rw [hrestored] at hrestored'
    exact hrestored'.symm
  have hnoalias' := hnoalias context shape slots hlookupName
  have hrel' := panValueCrepLocalsRel_update_word_list structs context sourceLocals
    state.locals name slots values hrel.2.1 hlookupExact hslotLength
    hslotsDistinct hnoalias'
  cases hrecordValue
  cases hsourceResult
  cases hcrepResult
  exact ⟨hrel.1, hrel', hrel.2.2⟩

end Flapjack
