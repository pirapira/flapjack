import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeStateRelation

/-!
Memory-update transport at the strengthened state boundary.  A source word
store updates structured memory at one address, while Crep updates its word
memory at the same address; all local/context components remain unchanged.
-/

namespace Flapjack

theorem panValueCrepStateRel_update_memory_word
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (address value : α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory address (.word value))
      { state with memory := updateMemory state.memory address value } := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact panValueCrepMemoryRel_update_word sourceMemory state.memory address
    value hrel.2.2

theorem panValueCrepStateRelWithContext_update_memory_word
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (address value : α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state) :
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      (updatePanValueMemory sourceMemory address (.word value))
      { state with memory := updateMemory state.memory address value } := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact panValueCrepStateRel_update_memory_word structs context sourceLocals
    sourceGlobals sourceMemory state address value hrel.2.2

end Flapjack
