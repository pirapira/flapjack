import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeCalleeParameterWordRelation

/-!
Context-aware initial callee-state relation for a single word parameter.  The
source globals and memory correspondence remain explicit, while the
extended context obligations are carried at the same boundary.
-/

namespace Flapjack

theorem panValueCrepCalleeStateRelWithContext_single_word
    [LawfulBEq String] [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (name : VarName) (slot : Nat) (value : α)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hname : lookupInfo name context.vars = none)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots)
    (hoverlap : panValueNoOverlap
      ((name, (.one, [slot])) :: context.vars))
    (hmax : panValueCtxtMax context.maxVar
      ((name, (.one, [slot])) :: context.vars)) :
    panValueCrepStateRelWithContext structs
      { context with vars := (name, (.one, [slot])) :: context.vars }
      (updatePanValueMap (fun _ => none) name (.word value)) sourceGlobals
      sourceMemory
      { locals := updateCrepLocal (fun _ => none) slot value,
        memory := crepMemory } := by
  refine ⟨hoverlap, hmax, ?_⟩
  exact panValueCrepCalleeStateRel_single_word structs context sourceGlobals
    sourceMemory crepMemory name slot value hglobals hmemory hname hnoalias

end Flapjack
