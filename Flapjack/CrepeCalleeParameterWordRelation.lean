import Flapjack.CrepeStateRelationExtension
import Flapjack.CrepeStateRelationWordUpdate

/-!
The one-word callee-parameter boundary.

The source evaluator binds a structured word under a parameter name, while
Crep receives the same word in one numbered slot.  This theorem packages the
resulting state relation so ordinary-call proofs can use the concrete binding
equations instead of supplying a fresh local-relation premise.
-/

namespace Flapjack

theorem bindPanValueParameters_single_word
    [OfNat α 0]
    (name : VarName) (value : α) :
    bindPanValueParameters [name] [.word value] =
      some ((([name].zip [PanValue.word value]) :
        List (VarName × PanValue α)).foldl
        (fun locals (parameterName, parameterValue) =>
          updatePanValueMap locals parameterName parameterValue)
        (fun _ : VarName => (none : Option (PanValue α)))) := by
  simp [bindPanValueParameters]

theorem assignCrepValues_single_word
    [OfNat α 0]
    (slot : Nat) (value : α) :
    assignCrepValues (fun _ => none) [slot] [value] =
      some (updateCrepLocal (fun _ => none) slot value) := by
  simp [assignCrepValues]

theorem panValueCrepStateRel_add_word_parameter
    [LawfulBEq String] [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (slot : Nat) (value : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hslot : state.locals slot = some value)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    panValueCrepStateRel structs
      { context with vars := (name, (.one, [slot])) :: context.vars }
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals
      sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  have hadded :
      panValueCrepStateRel structs
        { context with vars := (name, (.one, [slot])) :: context.vars }
        (updatePanValueMap sourceLocals name (.word value)) sourceGlobals
        sourceMemory state := by
    apply panValueCrepStateRel_extend structs context sourceLocals
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals
      sourceMemory state name .one [slot] (.word value) rfl
    · simp [panValueShape, panShapeMatches]
    · simp [readCrepLocals, hslot, panValueFlatWords, panValueFlatWordsFuel]
    · intro oldName oldValue oldShape oldSlots hne hsourceOld hlookupOld
      exact hrel.2.1 oldName oldValue oldShape oldSlots hsourceOld hlookupOld
    · exact hrel
  have hlookupNew :
      lookupInfo name
        ((name, (.one, [slot])) :: context.vars) = some (.one, [slot]) := by
    simp [lookupInfo]
  have hupdated := panValueCrepStateRel_update_word structs
    { context with vars := (name, (.one, [slot])) :: context.vars }
    (updatePanValueMap sourceLocals name (.word value)) sourceGlobals
    sourceMemory state name slot value hadded hlookupNew
    (by
      intro oldName oldShape oldSlots hne hlookupOld
      have hlookupContext : lookupInfo oldName context.vars =
          some (oldShape, oldSlots) := by
        simpa [lookupInfo, hne, Ne.symm hne] using hlookupOld
      exact hnoalias oldName oldShape oldSlots hne hlookupContext)
  have hsourceUpdate :
      updatePanValueMap
          (updatePanValueMap sourceLocals name (.word value)) name (.word value) =
        updatePanValueMap sourceLocals name (.word value) := by
    funext current
    by_cases hcurrent : current = name <;>
      simp [updatePanValueMap, hcurrent]
  simpa [hsourceUpdate] using hupdated

end Flapjack
