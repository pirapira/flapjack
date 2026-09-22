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

end Flapjack
