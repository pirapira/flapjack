import Flapjack.CrepeStateRelation

/-!
Transport a source-to-Crep state relation across the restoration performed by
a one-word declaration.  This is the scalar counterpart of the existing
two-word record restoration lemma and is needed by declaration-call lowering.
-/

namespace Flapjack

theorem panValueCrepStateRel_restore_one_word_declaration
    [BEq α] [LawfulBEq α] [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (oldValue : Option (PanValue α))
    (bodyLocals bodyGlobals : VarName → Option (PanValue α))
    (bodyMemory : α → Option (PanValue α))
    (state bodyState : CrepState α) (name : VarName)
    (hname : lookupInfo name context.vars = none)
    (hfresh : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      context.maxVar + 1 ∉ oldSlots)
    (hrel : panValueCrepStateRel structs
      { context with
          vars := (name, (Shape.one, [context.maxVar + 1])) :: context.vars
          maxVar := context.maxVar + 1 }
      bodyLocals bodyGlobals bodyMemory bodyState) :
    panValueCrepStateRel structs context
      (restorePanValueLocal bodyLocals name oldValue)
      bodyGlobals bodyMemory
      { bodyState with locals :=
          (restoreCrepLocal bodyState.locals
            (context.maxVar + 1) (state.locals (context.maxVar + 1))) } := by
  let restoredLocals :=
    restoreCrepLocal bodyState.locals
      (context.maxVar + 1) (state.locals (context.maxVar + 1))
  have hreadRestore : ∀ slots,
      context.maxVar + 1 ∉ slots →
      readCrepLocals restoredLocals slots =
        readCrepLocals bodyState.locals slots := by
    intro slots
    induction slots with
    | nil =>
        intro _
        rfl
    | cons head tail ih =>
        intro hnot
        have hhead : head ≠ context.maxVar + 1 := by
          intro heq
          apply hnot
          simp [heq]
        have htail : context.maxVar + 1 ∉ tail := by
          intro hmem
          apply hnot
          simp [hmem]
        simp [readCrepLocals, restoredLocals, restoreCrepLocal,
          hhead, ih htail]
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  intro current currentValue currentShape currentSlots hcurrent hlookup
  by_cases hcurrentName : current == name
  · have heq : current = name := by simpa using hcurrentName
    subst current
    rw [hname] at hlookup
    cases hlookup
  · have hbodyCurrent : bodyLocals current = some currentValue := by
      simp [restorePanValueLocal, hcurrentName] at hcurrent
      exact hcurrent
    have hnameCurrent : name ≠ current := by
      intro heq
      apply hcurrentName
      simp [heq]
    have hlookupBody :
        lookupInfo current
            ((name, (.one, [context.maxVar + 1])) :: context.vars) =
          some (currentShape, currentSlots) := by
      simp [lookupInfo, hnameCurrent, hlookup]
    have hbodyRel := hrel.2.1 current currentValue currentShape currentSlots
      hbodyCurrent hlookupBody
    have hnot := hfresh current currentShape currentSlots
      (by simpa using hcurrentName) hlookup
    exact ⟨hbodyRel.1,
      (hreadRestore currentSlots hnot).symm ▸ hbodyRel.2⟩

end Flapjack
