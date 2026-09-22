import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeStateRelation

/-!
Context-aware raised-state relation for compiler-owned payload spill slots.
The raised relation intentionally ignores source-local contents and permits
Crep memory differences only in the explicit excluded region.
-/

namespace Flapjack

def panValueCrepRaisedStateRelExceptWithContext [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepState : CrepState α) (excluded : α → Prop) : Prop :=
  panValueNoOverlap context.vars ∧
    panValueCtxtMax context.maxVar context.vars ∧
    panValueCrepRaisedStateRelExcept structs context sourceGlobals sourceMemory
      crepState excluded

theorem panValueCrepRaisedStateRelExceptWithContext_two_word_spill
    [BEq α] [LawfulBEq α] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α) (spillAddress stride left right : α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state) :
    panValueCrepRaisedStateRelExceptWithContext structs context sourceGlobals
      sourceMemory
      { locals := state.locals
        memory := updateMemory (updateMemory state.memory spillAddress left)
          (spillAddress + stride) right }
      (fun address => address = spillAddress ∨
        address = spillAddress + stride) := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact panValueCrepRaisedStateRel_two_word_spill structs context sourceLocals
    sourceGlobals sourceMemory state spillAddress stride left right hrel.2.2

end Flapjack
