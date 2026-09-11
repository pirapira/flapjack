import Flapjack.CrepeSourceWordRecordAssignmentCorrectness

/-!
State-relation preservation for a two-word record declaration.

The declaration compiler allocates the two slots immediately above
`context.maxVar`, while the source environment gains the structured value.
This is the environment invariant required by the declaration case of the
Pancake correctness induction.
-/

namespace Flapjack

theorem panValueCrepStateRel_extend_record_two_words
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (left right : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hshape : panShapeMatches
      (panValueShape structs (.rStruct [.word left, .word right]))
      (.comb [.one, .one]) = true)
    (hread : readCrepLocals
        (updateCrepLocal (updateCrepLocal state.locals
          (context.maxVar + 1) left) (context.maxVar + 2) right)
        [context.maxVar + 1, context.maxVar + 2] = some [left, right])
    (hold : ∀ oldName oldValue oldShape oldSlots,
      oldName ≠ name →
      sourceLocals oldName = some oldValue →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
      readCrepLocals state.locals oldSlots = some (panValueFlatWords oldValue))
    (hfresh : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      context.maxVar + 1 ∉ oldSlots ∧ context.maxVar + 2 ∉ oldSlots) :
    panValueCrepStateRel structs
      { context with
          vars := (name, (.comb [.one, .one],
            [context.maxVar + 1, context.maxVar + 2])) :: context.vars
          maxVar := context.maxVar + 2 }
      (updatePanValueMap sourceLocals name
        (.rStruct [.word left, .word right])) sourceGlobals sourceMemory
      { state with locals :=
          (updateCrepLocal
            (updateCrepLocal state.locals (context.maxVar + 1) left)
            (context.maxVar + 2) right) } := by
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  have hold' : ∀ oldName oldValue oldShape oldSlots,
      oldName ≠ name →
      sourceLocals oldName = some oldValue →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
      readCrepLocals
          (updateCrepLocal (updateCrepLocal state.locals
            (context.maxVar + 1) left) (context.maxVar + 2) right)
          oldSlots = some (panValueFlatWords oldValue) := by
    intro oldName oldValue oldShape oldSlots hne hsource hlookup
    have holdValue := hold oldName oldValue oldShape oldSlots hne hsource hlookup
    have hslots := hfresh oldName oldShape oldSlots hne hlookup
    have hleft := readCrepLocals_update_of_not_mem state.locals
      (context.maxVar + 1) left oldSlots hslots.1
    have hright := readCrepLocals_update_of_not_mem
      (updateCrepLocal state.locals (context.maxVar + 1) left)
      (context.maxVar + 2) right oldSlots hslots.2
    exact ⟨holdValue.1, by
      rw [hright, hleft]
      exact holdValue.2⟩
  exact panValueCrepLocalsRel_extend structs context sourceLocals
    (updatePanValueMap sourceLocals name
      (.rStruct [.word left, .word right]))
    (updateCrepLocal (updateCrepLocal state.locals
      (context.maxVar + 1) left) (context.maxVar + 2) right)
    name (.comb [.one, .one]) [context.maxVar + 1, context.maxVar + 2]
    (.rStruct [.word left, .word right]) rfl hshape hread hold'

end Flapjack
