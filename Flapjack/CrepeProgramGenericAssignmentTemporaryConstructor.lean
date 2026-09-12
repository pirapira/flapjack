import Flapjack.CrepeAllocationNameLemmas
import Flapjack.CrepeAssignmentSequenceInversion
import Flapjack.CrepeDistinctLists
import Flapjack.CrepeLocalsRelationUpdateGeneral
import Flapjack.CrepeNestedDecsAssignmentInversion
import Flapjack.CrepeProgramSourceAssignmentInversion
import Flapjack.PanShapeMatches
import Flapjack.CrepeTemporaryAssignmentCorrectness

/-!
Generic temporary local-assignment correctness.  This is the temporary
assignment branch for an arbitrary structured Pancake value; the expression
contract supplies its flattened target words, while the compiler-specific
freshness and destination metadata obligations remain explicit.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_assign_local_temporary
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (expression : Exp α)
    (hvalue : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
      (baseAddress topAddress bytesInWord : α) (sourceValue : PanValue α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory state →
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression = some sourceValue →
      ∃ compiled compileShape values,
        compileExp context expression = (compiled, compileShape) ∧
        compileShape = panValueShape structs sourceValue ∧
        compiled.length = values.length ∧
        evalCrepFullExps state.locals state.memory baseAddress topAddress
          compiled = some values ∧
        panValueFlatWords sourceValue = values)
    (htemporaryPath : ∀ (context : CompileContext α) (structs : StructContext)
      (_sourceValue : PanValue α) (_values : List α) (compiled : List (CrepExp α))
      (compileShape shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      compileExp context expression = (compiled, compileShape) →
      compileShape = panValueShape structs _sourceValue →
      panShapeMatches (panValueShape structs _sourceValue) shape = true →
      distinctLists slots (compiled.flatMap crepExpVars) = false ∧
      (∀ expression ∈ compiled, ∀ varName ∈ crepExpVars expression,
        varName ≤ context.maxVar))
    (hmetadata : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceValue : PanValue α)
      (compileShape shape : Shape) (slots : List Nat) (values : List α),
      lookupInfo name context.vars = some (shape, slots) →
      compileShape = panValueShape structs sourceValue →
      panShapeMatches (panValueShape structs sourceValue) shape = true →
      slots.length = values.length ∧ CrepDistinctNames slots)
    (hbounded : ∀ (context : CompileContext α) oldName oldShape oldSlots,
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ oldSlots, slot ≤ context.maxVar)
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
    PanValueCrepProgramCorrect (.assign .local name expression) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hsourceInfo : ∃ sourceValue oldValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression = some sourceValue ∧
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
            (.assign .local name expression) = some sourceResult := by
          simpa using hsource
        obtain ⟨sourceValue, oldValue, hvalue', hold, hvalid, hresult⟩ :=
          evalPanValueProg_assign_local_inv primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord sourceFuel sourceLocals sourceGlobals
            sourceMemory name expression sourceResult hsource'
        exact ⟨sourceValue, oldValue, hvalue', hold, hvalid, hresult⟩
  obtain ⟨sourceValue, oldValue, hvalue', hold, hvalid, hsourceResult⟩ := hsourceInfo
  obtain ⟨compiled, compileShape, values, hcompile, hcompileShape,
      hcompiledLength, hcompiled, hflat⟩ :=
    hvalue context structs sourceLocals sourceGlobals sourceMemory state
      baseAddress topAddress bytesInWord sourceValue hrel hvalue'
  obtain ⟨shape, slots, hlookupName⟩ := hlookup context sourceLocals oldValue hold
  have holdRel := hrel.2.1 name oldValue shape slots hold hlookupName
  have hshapeNewContext : panShapeMatches
      (panValueShape structs sourceValue) shape = true := by
    exact panShapeMatches_trans
      (panValueShape structs sourceValue) (panValueShape structs oldValue) shape
      hvalid holdRel.1
  obtain ⟨hnotDistinct, hcompiledBounded⟩ := htemporaryPath context structs
    sourceValue values compiled compileShape shape slots hlookupName hcompile
    hcompileShape hshapeNewContext
  obtain ⟨hslotLength, hslotsDistinct⟩ := hmetadata context structs sourceValue
    compileShape shape slots values hlookupName hcompileShape hshapeNewContext
  have htemporaryDistinct := crepDistinctNames_freshNames context slots.length 1
  have hslotBound : ∀ slot ∈ slots, slot ≤ context.maxVar :=
    hbounded context name shape slots hlookupName
  have hcompiledFresh := freshNames_not_mem_of_expVars_bounded context
    slots.length 1 compiled (by omega)
    hcompiledBounded
  have hnoOverlap := freshNames_not_mem_of_bounded context slots.length 1 slots
    (by omega) hslotBound
  let temporarySlots := freshNames context slots.length 1
  have htemporaryLength : temporarySlots.length = values.length := by
    simp [temporarySlots, freshNames, hslotLength]
  have hcompileProg :
      compileProg context (.assign .local name expression) =
        nestedDecs temporarySlots compiled
          (crepNestedSeq (slots.zipWith
            (fun slot temporary => .assign slot (.var temporary)) temporarySlots)) := by
    simp [temporarySlots, compileProg, hlookupName, hcompile, hslotLength,
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
      have hne : slot ≠ temporary := by
        intro heq
        apply hnoOverlap temporary htemporaryMem
        simpa [heq] using hslot
      simpa [crepExpVars] using hne)
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
      intro temporary htemporaryMem
      exact hnoOverlap temporary htemporaryMem)
    rfl
  have hcrepResult : crepResult = .normal { state with
      locals := updateCrepLocalList state.locals slots values } := by
    have hrestored' := hrestore
    rw [hinner] at hrestored'
    rw [hrestored] at hrestored'
    exact hrestored'.symm
  have hnoalias' := hnoalias context shape slots hlookupName
  have hrel' := panValueCrepLocalsRel_update_value structs context sourceLocals
    state.locals name shape slots sourceValue values hrel.2.1 hlookupName
    hshapeNewContext hslotLength hslotsDistinct hflat hnoalias'
  cases hsourceResult
  cases hcrepResult
  exact ⟨hrel.1, hrel', hrel.2.2⟩

end Flapjack
