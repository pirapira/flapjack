import Flapjack.CrepeAssignmentSequenceCorrectness
import Flapjack.CrepeSourceWordRecordShapeCorrectness
import Flapjack.CrepeProgramRelation

/-!
The direct lowering of a structured local assignment with an arbitrary number
of scalar word fields.  This is the first general assignment case needed by
the Pancake correctness induction: source evaluation keeps the record shape,
while Crep evaluates and installs its flattened words one destination slot at
a time.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_local_assign_record_source_word_general
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (name : VarName) (slots : List Nat) (oldValues values : List α)
    (fields : List (SourceWordExp α)) (compiled : List (CrepExp α))
    (hlookup : lookupInfo name context.vars =
      some (.comb (values.map (fun _ => .one)), slots))
    (hlength : slots.length = values.length)
    (hdistinct : CrepDistinctNames slots)
    (hlocals : sourceLocals name =
      some (.rStruct (oldValues.map (fun value => .word value))))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct (fields.map SourceWordExp.toExp)) =
      some (.rStruct (values.map (fun value => .word value))))
    (hvalid : panShapeMatches
      (panValueShape structs (.rStruct (values.map (fun value => .word value))))
      (panValueShape structs (.rStruct (oldValues.map (fun value => .word value)))) =
      true)
    (hcompile : compileExp context
      (.rStruct (fields.map SourceWordExp.toExp)) =
      (compiled, .comb (values.map (fun _ => .one))))
    (hcompiledLength : compiled.length = values.length)
    (hcompiled : evalCrepFullExps state.locals state.memory
      baseAddress topAddress compiled = some values)
    (hdirect : distinctLists slots (compiled.flatMap crepExpVars) = true)
    (hnot : ∀ slot ∈ slots, ∀ expression ∈ compiled,
      slot ∉ crepExpVars expression)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ slots, slot ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.assign .local name
        (.rStruct (fields.map SourceWordExp.toExp))) =
      some (.normal
        (updatePanValueMap sourceLocals name
          (.rStruct (values.map (fun value => .word value))))
        sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + slots.length + 1) state
      (compileProg context
        (.assign .local name
          (.rStruct (fields.map SourceWordExp.toExp)))) =
      some (.normal { state with
        locals := updateCrepLocalList state.locals slots values }) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name
        (.rStruct (values.map (fun value => .word value))))
      sourceGlobals sourceMemory
      { state with locals := updateCrepLocalList state.locals slots values } := by
  have hcompileProg :
      compileProg context
        (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
        crepNestedSeq (slots.zipWith
          (fun slot expression => .assign slot expression) compiled) := by
    simp [compileProg, hlookup, hcompile, hlength, hcompiledLength, hdirect]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hvalid, hlocals,
      panValueAssignmentValid, updatePanValueMap]
  constructor
  · rw [hcompileProg]
    exact evalCrepFullProg_assignList functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state slots compiled values
      (hlength.trans hcompiledLength.symm) hdistinct hnot
      hcompiled
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_word_list structs context sourceLocals
      state.locals name slots values hrel.2.1 hlookup hlength hdistinct hnoalias

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_local_assign_record_source_word_general_state_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (name : VarName) (slots : List Nat) (oldValues values : List α)
    (fields : List (SourceWordExp α)) (compiled : List (CrepExp α))
    (hlookup : lookupInfo name context.vars =
      some (.comb (values.map (fun _ => .one)), slots))
    (hlength : slots.length = values.length)
    (hdistinct : CrepDistinctNames slots)
    (hlocals : sourceLocals name =
      some (.rStruct (oldValues.map (fun value => .word value))))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct (fields.map SourceWordExp.toExp)) =
      some (.rStruct (values.map (fun value => .word value))))
    (hvalid : panShapeMatches
      (panValueShape structs (.rStruct (values.map (fun value => .word value))))
      (panValueShape structs (.rStruct (oldValues.map (fun value => .word value)))) =
      true)
    (hcompile : compileExp context
      (.rStruct (fields.map SourceWordExp.toExp)) =
      (compiled, .comb (values.map (fun _ => .one))))
    (hcompiledLength : compiled.length = values.length)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hdirect : distinctLists slots (compiled.flatMap crepExpVars) = true)
    (hnot : ∀ slot ∈ slots, ∀ expression ∈ compiled,
      slot ∉ crepExpVars expression)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ slots, slot ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.assign .local name
        (.rStruct (fields.map SourceWordExp.toExp))) =
      some (.normal
        (updatePanValueMap sourceLocals name
          (.rStruct (values.map (fun value => .word value))))
        sourceGlobals sourceMemory) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + slots.length + 1) state
      (compileProg context
        (.assign .local name
          (.rStruct (fields.map SourceWordExp.toExp)))) =
      some (.normal { state with
        locals := updateCrepLocalList state.locals slots values }) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name
        (.rStruct (values.map (fun value => .word value))))
      sourceGlobals sourceMemory
      { state with locals := updateCrepLocalList state.locals slots values } := by
  have hcompileProg :
      compileProg context
        (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
        crepNestedSeq (slots.zipWith
          (fun slot expression => .assign slot expression) compiled) := by
    simp [compileProg, hlookup, hcompile, hlength, hcompiledLength, hdirect]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hvalid, hlocals,
      panValueAssignmentValid, updatePanValueMap]
  constructor
  · rw [hcompileProg]
    exact evalCrepFullProgState_assignList functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state slots compiled values
      (hlength.trans hcompiledLength.symm) hdistinct hnot
      hcompiled
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_word_list structs context sourceLocals
      state.locals name slots values hrel.2.1 hlookup hlength hdistinct hnoalias

end Flapjack
