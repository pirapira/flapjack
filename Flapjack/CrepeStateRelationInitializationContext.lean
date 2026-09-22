import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeStateRelationExtension

/-!
Context-aware state transport for the local initialization performed before a
compiled nested declaration.  Initialization only changes fresh Crep locals,
so the compiler context invariants and the source-global/memory components
remain unchanged.
-/

namespace Flapjack

theorem panValueCrepStateRelWithContext_initialize
    [OfNat α 0] [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (slots : List Nat)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory state)
    (hname : lookupInfo name context.vars = none)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ temporary, temporary ∈ slots → temporary ∉ oldSlots) :
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory
      { state with locals := initializeCrepLocals state.locals slots } := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact panValueCrepStateRel_initialize structs context sourceLocals
    sourceGlobals sourceMemory state name slots hrel.2.2 hname hnoalias

end Flapjack
