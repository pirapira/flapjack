import Flapjack.CrepeRaisedResultRestoration

/-!
Transport control relations across an ordinary call boundary.

An ordinary Crep call returns the caller's locals while retaining the
callee's memory.  These lemmas turn a recursive relation at the callee state
into the relation observed by the caller, for returned and raised results.
-/

namespace Flapjack

theorem panValueCrepControlRel_call_returned
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (calleeLocals : VarName → Option (PanValue α))
    (callee : CrepState α) (callerLocals : Nat → Option α)
    (sourceValues : List (PanValue α)) (crepValues : List α)
    (hrel : panValueCrepControlRel structs context exceptionRel
      (.returned calleeLocals sourceGlobals sourceMemory sourceValues)
      (.returned callee crepValues)) :
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory sourceValues)
      (.returned { locals := callerLocals, memory := callee.memory } crepValues) := by
  refine ⟨?_, hrel.2⟩
  exact ⟨hrel.1.1,
    panValueCrepLocalsRel_empty structs context callerLocals,
    hrel.1.2.2⟩

theorem panValueCrepControlRel_call_raised
    [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (calleeLocals : VarName → Option (PanValue α))
    (callee : CrepState α) (callerLocals : Nat → Option α)
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (crepException : α)
    (hrel : panValueCrepControlRel structs context exceptionRel
      (.raised calleeLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised callee crepException)) :
    panValueCrepControlRel structs context exceptionRel
      (.raised (fun _ => none) sourceGlobals sourceMemory sourceException sourceValue)
      (.raised { locals := callerLocals, memory := callee.memory } crepException) := by
  have hrel' : panValueCrepControlRel structs context exceptionRel
      (.raised (fun _ => none) sourceGlobals sourceMemory sourceException sourceValue)
      (.raised callee crepException) := by
    simpa [panValueCrepControlRel] using hrel
  exact panValueCrepControlRel_restore_local_raised
    structs context exceptionRel
    (fun _ => none) sourceGlobals sourceMemory sourceException sourceValue
    callee crepException callerLocals hrel'

theorem panValueCrepControlRel_call_returned_of_contexts
    (structs : StructContext) (calleeContext callerContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (calleeLocals : VarName → Option (PanValue α))
    (callee : CrepState α) (callerLocals : Nat → Option α)
    (sourceValues : List (PanValue α)) (crepValues : List α)
    (hrel : panValueCrepControlRel structs calleeContext exceptionRel
      (.returned calleeLocals sourceGlobals sourceMemory sourceValues)
      (.returned callee crepValues)) :
    panValueCrepControlRel structs callerContext exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory sourceValues)
      (.returned { locals := callerLocals, memory := callee.memory } crepValues) := by
  refine ⟨?_, hrel.2⟩
  exact ⟨hrel.1.1,
    panValueCrepLocalsRel_empty structs callerContext callerLocals,
    hrel.1.2.2⟩

theorem panValueCrepControlRel_call_raised_of_contexts
    (structs : StructContext) (calleeContext callerContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (calleeLocals : VarName → Option (PanValue α))
    (callee : CrepState α) (callerLocals : Nat → Option α)
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (crepException : α)
    (hrel : panValueCrepControlRel structs calleeContext exceptionRel
      (.raised calleeLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised callee crepException)) :
    panValueCrepControlRel structs callerContext exceptionRel
      (.raised (fun _ => none) sourceGlobals sourceMemory sourceException sourceValue)
      (.raised { locals := callerLocals, memory := callee.memory } crepException) := by
  have hrel' : panValueCrepControlRel structs calleeContext exceptionRel
      (.raised (fun _ => none) sourceGlobals sourceMemory sourceException sourceValue)
      (.raised callee crepException) := by
    simpa [panValueCrepControlRel] using hrel
  obtain ⟨spillAddress, hstate, hexception⟩ := hrel'
  refine ⟨spillAddress, ?_, hexception⟩
  exact ⟨hstate.1,
    panValueCrepLocalsRel_empty structs callerContext callerLocals,
    hstate.2.2⟩

end Flapjack
