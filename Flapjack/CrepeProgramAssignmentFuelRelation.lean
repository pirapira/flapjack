import Flapjack.CrepeSourceWordAssignmentCorrectness

/-!
Fuel-polymorphic scalar assignment boundaries for the source-to-Crep
program relation.  The fixed-fuel relations remain useful for small examples;
these variants are the forms consumed by compositional program induction.
-/

namespace Flapjack

theorem compile_full_pan_value_local_assign_source_word_relation_fuel
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
    (name : VarName) (slot : Nat) (oldValue value : α)
    (expression : SourceWordExp α) (compiled : CrepExp α)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hold : sourceLocals name = some (.word oldValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value))
    (hcompile : compileExp context expression.toExp = ([compiled], .one))
    (hcompiled : evalCrepFullExp state.locals state.memory baseAddress topAddress
      compiled = some value)
    (hdistinct : distinctLists [slot] (crepExpVars compiled))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.assign .local name expression.toExp) =
      some (.normal (updatePanValueMap sourceLocals name (.word value))
        sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 2) state
      (compileProg context (.assign .local name expression.toExp)) =
      some (.normal { state with locals := updateCrepLocal state.locals slot value }) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  have hcompileProg : compileProg context (.assign .local name expression.toExp) =
      .seq (.assign slot compiled) .skip := by
    simp [compileProg, hlookup, hcompile, hdistinct, crepNestedSeq]
  rw [hcompileProg]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hold,
      panValueAssignmentValid, panValueShape, panShapeMatches]
  constructor
  · simp [evalCrepFullProg, hcompiled]
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_word structs context sourceLocals
      state.locals name slot value hrel.2.1 hlookup hnoalias

theorem compile_full_pan_value_local_assign_source_word_state_relation_fuel
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
    (name : VarName) (slot : Nat) (oldValue value : α)
    (expression : SourceWordExp α) (compiled : CrepExp α)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hlookupAll : ∀ localName localValue,
      sourceLocals localName = some localValue →
      ∃ localSlot, lookupInfo localName context.vars = some (.one, [localSlot]))
    (hold : sourceLocals name = some (.word oldValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value))
    (hcompile : compileExp context expression.toExp = ([compiled], .one))
    (hcompiled : evalCrepFullExp state.locals state.memory baseAddress topAddress
      compiled = some value)
    (hdistinct : distinctLists [slot] (crepExpVars compiled))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.assign .local name expression.toExp) =
      some (.normal (updatePanValueMap sourceLocals name (.word value))
        sourceGlobals sourceMemory) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 2) state
      (compileProg context (.assign .local name expression.toExp)) =
      some (.normal { state with locals := updateCrepLocal state.locals slot value }) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  have hcompileProg : compileProg context (.assign .local name expression.toExp) =
      .seq (.assign slot compiled) .skip := by
    simp [compileProg, hlookup, hcompile, hdistinct, crepNestedSeq]
  rw [hcompileProg]
  have hnoGlobal : CrepExpNoGlobal compiled := by
    obtain ⟨compiled', hcompile', hnoGlobal'⟩ := compileSourceWordExp_noGlobal
      context structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord hlookupAll expression value hsource
    have hpair : ([compiled], Shape.one) = ([compiled'], Shape.one) :=
      hcompile.symm.trans hcompile'
    have hcompiledEq : compiled = compiled' :=
      (List.cons.inj (congrArg Prod.fst hpair)).1
    simpa [hcompiledEq] using hnoGlobal'
  have hcompiledState :
      evalCrepFullExpState state baseAddress topAddress compiled = some value := by
    calc
      evalCrepFullExpState state baseAddress topAddress compiled =
          evalCrepFullExp state.locals state.memory
            baseAddress topAddress compiled :=
        evalCrepFullExpState_eq_of_noGlobal state baseAddress topAddress
          compiled hnoGlobal
      _ = some value := hcompiled
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hold,
      panValueAssignmentValid, panValueShape, panShapeMatches]
  constructor
  · simp [evalCrepFullProgState, hcompiledState]
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_word structs context sourceLocals
      state.locals name slot value hrel.2.1 hlookup hnoalias

theorem compile_full_pan_value_local_assign_source_word_temporary_relation_fuel
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
    (name : VarName) (slot temporary : Nat) (oldValue value : α)
    (expression : SourceWordExp α) (compiled : CrepExp α)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hold : sourceLocals name = some (.word oldValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value))
    (hcompile : compileExp context expression.toExp = ([compiled], .one))
    (hcompiled : evalCrepFullExp state.locals state.memory baseAddress topAddress
      compiled = some value)
    (hnotDistinct : distinctLists [slot] (crepExpVars compiled) = false)
    (hfresh : temporary = context.maxVar + 1)
    (htemporary : state.locals temporary = none)
    (htemporaryNe : temporary ≠ slot)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.assign .local name expression.toExp) =
      some (.normal (updatePanValueMap sourceLocals name (.word value))
        sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 3) state
      (compileProg context (.assign .local name expression.toExp)) =
      some (.normal { state with locals := updateCrepLocal state.locals slot value }) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  have hcompileProg : compileProg context (.assign .local name expression.toExp) =
      .dec temporary compiled (.seq (.assign slot (.var temporary)) .skip) := by
    subst temporary
    simp [compileProg, hlookup, hcompile, hnotDistinct, freshNames, nestedDecs,
      crepNestedSeq]
  rw [hcompileProg]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hold,
      panValueAssignmentValid, panValueShape, panShapeMatches]
  constructor
  · have htemporaryRead : evalCrepFullExp
        (updateCrepLocal state.locals temporary value) state.memory
        baseAddress topAddress (.var temporary) = some value := by
      simp [evalCrepFullExp, updateCrepLocal]
    have hslotNe : slot ≠ temporary := Ne.symm htemporaryNe
    have hrestore :
        restoreCrepLocal
            (updateCrepLocal (updateCrepLocal state.locals temporary value) slot value)
            temporary none = updateCrepLocal state.locals slot value := by
      funext current
      by_cases hcurrentTemporary : current = temporary
      · subst current
        simp [restoreCrepLocal, updateCrepLocal, htemporary, htemporaryNe]
      · by_cases hcurrentSlot : current = slot
        · subst current
          simp [restoreCrepLocal, updateCrepLocal, hslotNe]
        · simp [restoreCrepLocal, updateCrepLocal, hcurrentTemporary,
            hcurrentSlot]
    simp [evalCrepFullProg, hcompiled, htemporary, htemporaryRead, hrestore,
      restoreCrepResult]
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_word structs context sourceLocals
      state.locals name slot value hrel.2.1 hlookup hnoalias

end Flapjack
