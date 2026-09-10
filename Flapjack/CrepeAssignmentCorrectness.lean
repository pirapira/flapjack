import Flapjack.CrepeStateRelation

/-!
Assignment correctness at the structured source-to-Crep boundary.

The evaluator equation comes from the generic assignment/return boundary; the
additional conclusion preserves the state relation needed by a continuation.
-/

namespace Flapjack

theorem compile_full_pan_value_local_assign_return_word_rel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (slot : Nat) (oldValue value : α)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hlocals : sourceLocals name = some (.word oldValue))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 20 state
        (compileProg context
          (.seq (.assign .local name (.const value))
            (.return (.var .local name)))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        sourceLocals sourceGlobals (fun address =>
          (state.memory address).map PanValue.word)
        (.seq (.assign .local name (.const value))
          (.return (.var .local name)))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name (.word value))
      sourceGlobals sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  constructor
  · exact compile_full_pan_value_local_assign_return_word_correct
      context structs sourceLocals sourceGlobals state primitive ffi sharedMem
      baseAddress topAddress bytesInWord name slot oldValue value hlookup hlocals
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_word structs context sourceLocals
      state.locals name slot value hrel.2.1 hlookup hnoalias

end Flapjack
