import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeNestedDecsStability

namespace Flapjack

theorem panValueCrepStateRelWithContext_updateCrepLocalList_fresh
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepState : CrepState α)
    (names : List Nat) (values : List α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory crepState)
    (hlength : names.length = values.length)
    (hfresh : ∀ name shape slots,
      lookupInfo name context.vars = some (shape, slots) →
        ∀ slot, slot ∈ names → slot ∉ slots) :
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory
      { crepState with
          locals := updateCrepLocalList crepState.locals names values } := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact panValueCrepStateRel_updateCrepLocalList_fresh structs context
    sourceLocals sourceGlobals sourceMemory crepState names values hrel.2.2
    hlength hfresh

theorem panValueCrepStateRelWithContext_update_fresh_slot
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepState : CrepState α)
    (slot : Nat) (value : α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory crepState)
    (hslot : context.maxVar < slot)
    (hbound : ∀ name shape slots,
      lookupInfo name context.vars = some (shape, slots) →
        ∀ current, current ∈ slots → current ≤ context.maxVar) :
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory
      { crepState with locals := updateCrepLocal crepState.locals slot value } := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact ⟨hrel.2.2.1,
    panValueCrepLocalsRel_update_fresh_slot structs context sourceLocals
      crepState.locals slot value hrel.2.2.2.1 hslot hbound,
    hrel.2.2.2.2⟩

end Flapjack
