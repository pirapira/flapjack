import Flapjack.CrepeStateRelation

/-!
Transport a source-to-Crep state relation across the restoration performed by
a two-word declaration.  The declaration name is assumed to be fresh in the
outer context; all other outer bindings are looked up in the extended
context, and the two allocated Crep slots are assumed not to alias them.
-/

namespace Flapjack

theorem panValueCrepStateRel_restore_two_word_declaration
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
      context.maxVar + 1 ∉ oldSlots ∧ context.maxVar + 2 ∉ oldSlots)
    (hrel : panValueCrepStateRel structs
      { context with
          vars := (name, (.comb [.one, .one],
            [context.maxVar + 1, context.maxVar + 2])) :: context.vars
          maxVar := context.maxVar + 2 }
      bodyLocals bodyGlobals bodyMemory bodyState) :
    panValueCrepStateRel structs context
      (restorePanValueLocal bodyLocals name oldValue)
      bodyGlobals bodyMemory
      { bodyState with locals :=
          (restoreCrepLocal
            (restoreCrepLocal bodyState.locals
              (context.maxVar + 2) (state.locals (context.maxVar + 2)))
            (context.maxVar + 1) (state.locals (context.maxVar + 1))) } := by
  let restoredLocals :=
    restoreCrepLocal
      (restoreCrepLocal bodyState.locals
        (context.maxVar + 2) (state.locals (context.maxVar + 2)))
      (context.maxVar + 1) (state.locals (context.maxVar + 1))
  have hreadRestore : ∀ slots,
      context.maxVar + 1 ∉ slots → context.maxVar + 2 ∉ slots →
      readCrepLocals restoredLocals slots =
        readCrepLocals bodyState.locals slots := by
    intro slots
    induction slots with
    | nil =>
        intro _ _
        rfl
    | cons head tail ih =>
        intro hfirst hsecond
        have hheadFirst : head ≠ context.maxVar + 1 := by
          intro heq
          apply hfirst
          simp [heq]
        have hheadSecond : head ≠ context.maxVar + 2 := by
          intro heq
          apply hsecond
          simp [heq]
        have htailFirst : context.maxVar + 1 ∉ tail := by
          intro hmem
          apply hfirst
          simp [hmem]
        have htailSecond : context.maxVar + 2 ∉ tail := by
          intro hmem
          apply hsecond
          simp [hmem]
        simp [readCrepLocals, restoredLocals, restoreCrepLocal,
          hheadFirst, hheadSecond, ih htailFirst htailSecond]
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
            ((name, (.comb [.one, .one],
              [context.maxVar + 1, context.maxVar + 2])) :: context.vars) =
          some (currentShape, currentSlots) := by
      simp [lookupInfo, hnameCurrent, hlookup]
    have hbodyRel := hrel.2.1 current currentValue currentShape currentSlots
      hbodyCurrent hlookupBody
    have hnot := hfresh current currentShape currentSlots
      (by simpa using hcurrentName) hlookup
    exact ⟨hbodyRel.1,
      (hreadRestore currentSlots hnot.1 hnot.2).symm ▸ hbodyRel.2⟩

end Flapjack
