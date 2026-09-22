import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeCalleeParameterContextRelation

/-!
Context-aware callee bind/assign transport.  The evaluator-facing theorem
already relates the bound source locals and assigned Crep locals; this wrapper
adds the final context invariants needed by the strengthened state relation.
-/

namespace Flapjack

theorem panValueCrepStateRelWithContext_parameters_append_of_context_bind_assign
    [OfNat α 0] [LawfulBEq String]
    (structs : StructContext) (context targetContext : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (parameters : List (CalleeParameter α))
    (calleeLocals : VarName → Option (PanValue α))
    (targetCalleeLocals : Nat → Option α)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hbind : bindPanValueParameters (parameters.map CalleeParameter.name)
        (parameters.map CalleeParameter.value) = some calleeLocals)
    (hassign : assignCrepValues (fun _ => none)
        (parameters.flatMap CalleeParameter.slots)
        (parameters.flatMap CalleeParameter.values) = some targetCalleeLocals)
    (hfresh : CalleeParameterListFreshAppend structs context parameters)
    (hvars : targetContext.vars =
      (foldCalleeParameterContextAppend context parameters).vars)
    (hoverlap : panValueNoOverlap targetContext.vars)
    (hmax : panValueCtxtMax targetContext.maxVar targetContext.vars) :
    panValueCrepStateRelWithContext structs targetContext calleeLocals
      sourceGlobals sourceMemory { locals := targetCalleeLocals, memory := crepMemory } := by
  refine ⟨hoverlap, hmax, ?_⟩
  exact panValueCrepStateRel_parameters_append_of_context_bind_assign structs
    context targetContext sourceGlobals sourceMemory crepMemory parameters
    calleeLocals targetCalleeLocals hglobals hmemory hbind hassign hfresh hvars

end Flapjack
