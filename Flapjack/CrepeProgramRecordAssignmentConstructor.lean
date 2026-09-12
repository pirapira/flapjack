import Flapjack.CrepeProgramRecordAssignmentGeneralCorrectness
import Flapjack.CrepeProgramSourceAssignmentInversion
import Flapjack.CrepeAssignmentSequenceInversion
import Flapjack.CrepeDistinctLists
import Flapjack.CrepeShapeInversion
import Flapjack.PanShapeMatches
import Flapjack.PanValueShapeInversion

/-!
The direct structured-assignment constructor for the compositional program
correctness predicate.  The expression contract is deliberately explicit:
the expression induction will supply the record value, compiled expressions,
and their evaluation.  This theorem then supplies the source assignment
inversion, destination-shape reasoning, target sequence inversion, and local
state update.

The temporary lowering is a separate constructor because it additionally
needs declaration inversion and restoration; keeping the direct case isolated
makes the eventual syntax-induction hypothesis easier to instantiate.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_assign_local_record_direct
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
    (hdirect : ∀ (context : CompileContext α)
      (sourceValue : PanValue α)
      (values : List α) (compiled : List (CrepExp α))
      (shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      sourceValue = .rStruct (values.map (fun value => .word value)) →
      compileExp context (.rStruct (fields.map SourceWordExp.toExp)) =
        (compiled, .comb (values.map (fun _ => .one))) →
      distinctLists slots (compiled.flatMap crepExpVars) = true)
    (hmetadata : ∀ (context : CompileContext α) (shape : Shape) (slots : List Nat)
      (values : List α),
      lookupInfo name context.vars = some (shape, slots) →
      shape = .comb (values.map (fun _ => .one)) →
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
    | zero =>
        simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
    | succ sourceFuel =>
        have hsource' : evalPanValueProgWithPrimitiveCallsAndFfi
            primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord (sourceFuel + 1)
            sourceLocals sourceGlobals sourceMemory
            (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
            some sourceResult := by
          simpa using hsource
        obtain ⟨sourceValue, oldValue, hvalue, hold, hvalid, hsourceResult⟩ :=
          evalPanValueProg_assign_local_inv primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord sourceFuel sourceLocals sourceGlobals
            sourceMemory name (.rStruct (fields.map SourceWordExp.toExp)) sourceResult hsource'
        exact ⟨sourceValue, oldValue, hvalue, hold, hvalid, hsourceResult⟩
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
  obtain ⟨hslotLength, hslotsDistinct⟩ := hmetadata context shape slots values
    hlookupName hshapeContext
  have hdirect' := hdirect context sourceValue values compiled
    shape slots hlookupName hrecordValue hcompile
  have hnot := distinctLists_flatMap_not_mem slots compiled hdirect'
  have hcompileProg :
      compileProg context
        (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
        crepNestedSeq (slots.zipWith
          (fun slot expression => .assign slot expression) compiled) := by
    simp [compileProg, hlookupExact, hcompile, hslotLength, hcompiledLength,
      hdirect']
  rw [hcompileProg] at hcrep
  have htarget := evalCrepFullProg_assignList_inv functions crepPrimitive ffi sharedMem
    baseAddress topAddress targetFuel state slots compiled values
    crepResult (by exact hslotLength.trans hcompiledLength.symm)
    hslotsDistinct hnot hcompiled hcrep
  have hnoalias' := hnoalias context shape slots hlookupName
  have hrel' := panValueCrepLocalsRel_update_word_list structs context sourceLocals
    state.locals name slots values hrel.2.1 hlookupExact
    hslotLength hslotsDistinct hnoalias'
  cases hrecordValue
  cases hsourceResult
  cases htarget
  exact ⟨hrel.1, hrel', hrel.2.2⟩

theorem panValueCrepProgramStateCorrect_assign_local_record_direct
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
    (hdirect : ∀ (context : CompileContext α)
      (sourceValue : PanValue α)
      (values : List α) (compiled : List (CrepExp α))
      (shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      sourceValue = .rStruct (values.map (fun value => .word value)) →
      compileExp context (.rStruct (fields.map SourceWordExp.toExp)) =
        (compiled, .comb (values.map (fun _ => .one))) →
      distinctLists slots (compiled.flatMap crepExpVars) = true)
    (hmetadata : ∀ (context : CompileContext α) (shape : Shape) (slots : List Nat)
      (values : List α),
      lookupInfo name context.vars = some (shape, slots) →
      shape = .comb (values.map (fun _ => .one)) →
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
    | zero =>
        simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
    | succ sourceFuel =>
        have hsource' : evalPanValueProgWithPrimitiveCallsAndFfi
            primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord (sourceFuel + 1)
            sourceLocals sourceGlobals sourceMemory
            (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
            some sourceResult := by
          simpa using hsource
        obtain ⟨sourceValue, oldValue, hvalue, hold, hvalid, hsourceResult⟩ :=
          evalPanValueProg_assign_local_inv primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord sourceFuel sourceLocals sourceGlobals
            sourceMemory name (.rStruct (fields.map SourceWordExp.toExp)) sourceResult hsource'
        exact ⟨sourceValue, oldValue, hvalue, hold, hvalid, hsourceResult⟩
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
  obtain ⟨hslotLength, hslotsDistinct⟩ := hmetadata context shape slots values
    hlookupName hshapeContext
  have hdirect' := hdirect context sourceValue values compiled
    shape slots hlookupName hrecordValue hcompile
  have hnot := distinctLists_flatMap_not_mem slots compiled hdirect'
  have hcompileProg :
      compileProg context
        (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
        crepNestedSeq (slots.zipWith
          (fun slot expression => .assign slot expression) compiled) := by
    simp [compileProg, hlookupExact, hcompile, hslotLength, hcompiledLength,
      hdirect']
  rw [hcompileProg] at hcrep
  have htarget := evalCrepFullProgState_assignList_inv functions crepPrimitive ffi
    sharedMem baseAddress topAddress targetFuel state slots compiled values
    crepResult (by exact hslotLength.trans hcompiledLength.symm)
    hslotsDistinct hnot hcompiled hcrep
  have hnoalias' := hnoalias context shape slots hlookupName
  have hrel' := panValueCrepLocalsRel_update_word_list structs context sourceLocals
    state.locals name slots values hrel.2.1 hlookupExact
    hslotLength hslotsDistinct hnoalias'
  cases hrecordValue
  cases hsourceResult
  cases htarget
  exact ⟨hrel.1, hrel', hrel.2.2⟩

end Flapjack
