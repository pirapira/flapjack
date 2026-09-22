import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeStateRelation

/-!
Context-aware relation for states whose Crep memory may differ at
compiler-owned addresses.  This is the raised-call/spill boundary: source
memory remains related everywhere outside the excluded region.
-/

namespace Flapjack

def panValueCrepStateRelExceptWithContext [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepState : CrepState α) (excluded : α → Prop) : Prop :=
  panValueNoOverlap context.vars ∧
    panValueCtxtMax context.maxVar context.vars ∧
    panValueCrepStateRelExcept structs context sourceLocals sourceGlobals
      sourceMemory crepState excluded

theorem panValueCrepStateRelExceptWithContext_of_state_rel
    [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (excluded : α → Prop)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state) :
    panValueCrepStateRelExceptWithContext structs context sourceLocals
      sourceGlobals sourceMemory state excluded := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact panValueCrepStateRelExcept_of_state_rel structs context sourceLocals
    sourceGlobals sourceMemory state excluded hrel.2.2

theorem panValueCrepStateRelExceptWithContext_update_crep_at_excluded
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (address value : α) (excluded : α → Prop)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state)
    (hexcluded : excluded address) :
    panValueCrepStateRelExceptWithContext structs context sourceLocals
      sourceGlobals sourceMemory
      { state with memory := updateMemory state.memory address value }
      excluded := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact panValueCrepStateRelExcept_update_crep_at_excluded structs context
    sourceLocals sourceGlobals sourceMemory state address value excluded
    hrel.2.2 hexcluded

end Flapjack
