import Flapjack.CrepeAssignmentSequenceInversion
import Flapjack.CrepeDistinctLists
import Flapjack.CrepeLocalsRelationUpdateGeneral
import Flapjack.CrepeProgramSourceAssignmentInversion
import Flapjack.PanShapeMatches

/-!
Generic direct local-assignment correctness.  Unlike the record-specific
constructor, this result is parameterized by the expression contract for an
arbitrary flattened Pancake value.  It is the direct-assignment branch needed
by the general `assign` case of the program induction.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_assign_local_direct
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
    (hdirect : ∀ (context : CompileContext α)
      (compiled : List (CrepExp α)) (compileShape shape : Shape)
      (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      compileExp context expression = (compiled, compileShape) →
      distinctLists slots (compiled.flatMap crepExpVars) = true)
    (hmetadata : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceValue : PanValue α)
      (compileShape shape : Shape) (slots : List Nat) (values : List α),
      lookupInfo name context.vars = some (shape, slots) →
      compileShape = panValueShape structs sourceValue →
      panShapeMatches (panValueShape structs sourceValue) shape = true →
      slots.length = values.length ∧ CrepDistinctNames slots)
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
            sourceLocals sourceGlobals sourceMemory (.assign .local name expression) =
            some sourceResult := by simpa using hsource
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
  obtain ⟨hslotLength, hslotsDistinct⟩ := hmetadata context structs sourceValue compileShape
    shape slots values hlookupName hcompileShape hshapeNewContext
  have hlookupExact : lookupInfo name context.vars = some (shape, slots) := hlookupName
  have hdirect' := hdirect context compiled compileShape shape slots
    hlookupName hcompile
  have hnot := distinctLists_flatMap_not_mem slots compiled hdirect'
  have hcompileProg :
      compileProg context (.assign .local name expression) =
        crepNestedSeq (slots.zipWith
          (fun slot expression => .assign slot expression) compiled) := by
    simp [compileProg, hlookupExact, hcompile, hslotLength, hcompiledLength,
      hdirect']
  rw [hcompileProg] at hcrep
  have htarget := evalCrepFullProg_assignList_inv functions crepPrimitive ffi sharedMem
    baseAddress topAddress targetFuel state slots compiled values crepResult
    (by exact hslotLength.trans hcompiledLength.symm) hslotsDistinct hnot hcompiled hcrep
  have hnoalias' := hnoalias context shape slots hlookupName
  have hrel' := panValueCrepLocalsRel_update_value structs context sourceLocals
    state.locals name shape slots sourceValue values hrel.2.1 hlookupName
    hshapeNewContext hslotLength hslotsDistinct hflat hnoalias'
  cases hsourceResult
  cases htarget
  exact ⟨hrel.1, hrel', hrel.2.2⟩

theorem panValueCrepProgramStateCorrect_assign_local_direct
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
        evalCrepFullExpsState state baseAddress topAddress compiled = some values ∧
        panValueFlatWords sourceValue = values)
    (hdirect : ∀ (context : CompileContext α)
      (compiled : List (CrepExp α)) (compileShape shape : Shape)
      (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      compileExp context expression = (compiled, compileShape) →
      distinctLists slots (compiled.flatMap crepExpVars) = true)
    (hmetadata : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceValue : PanValue α)
      (compileShape shape : Shape) (slots : List Nat) (values : List α),
      lookupInfo name context.vars = some (shape, slots) →
      compileShape = panValueShape structs sourceValue →
      panShapeMatches (panValueShape structs sourceValue) shape = true →
      slots.length = values.length ∧ CrepDistinctNames slots)
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
    PanValueCrepProgramStateCorrect (.assign .local name expression) := by
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
  obtain ⟨hslotLength, hslotsDistinct⟩ := hmetadata context structs sourceValue compileShape
    shape slots values hlookupName hcompileShape hshapeNewContext
  have hlookupExact : lookupInfo name context.vars = some (shape, slots) := hlookupName
  have hdirect' := hdirect context compiled compileShape shape slots
    hlookupName hcompile
  have hnot := distinctLists_flatMap_not_mem slots compiled hdirect'
  have hcompileProg :
      compileProg context (.assign .local name expression) =
        crepNestedSeq (slots.zipWith
          (fun slot expression => .assign slot expression) compiled) := by
    simp [compileProg, hlookupExact, hcompile, hslotLength, hcompiledLength,
      hdirect']
  rw [hcompileProg] at hcrep
  have htarget := evalCrepFullProgState_assignList_inv functions crepPrimitive ffi sharedMem
    baseAddress topAddress targetFuel state slots compiled values crepResult
    (by exact hslotLength.trans hcompiledLength.symm) hslotsDistinct hnot hcompiled hcrep
  have hnoalias' := hnoalias context shape slots hlookupName
  have hrel' := panValueCrepLocalsRel_update_value structs context sourceLocals
    state.locals name shape slots sourceValue values hrel.2.1 hlookupName
    hshapeNewContext hslotLength hslotsDistinct hflat hnoalias'
  cases hsourceResult
  cases htarget
  exact ⟨hrel.1, hrel', hrel.2.2⟩

end Flapjack
