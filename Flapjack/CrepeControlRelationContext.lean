import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeRaisedStateRelationContext

/-!
Strengthened source/Crep control-result relation carrying context invariants
through normal, returned, and raised outcomes.  The raised branch records the
compiler-owned spill region explicitly.
-/

namespace Flapjack

def panValueCrepControlRelWithContext [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α) : Prop :=
  match sourceResult, crepResult with
  | .normal sourceLocals sourceGlobals sourceMemory,
      .normal crepState =>
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory crepState
  | .returned sourceLocals sourceGlobals sourceMemory sourceValues,
      .returned crepState crepValues =>
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory crepState ∧
      panValueCrepValuesRel sourceValues crepValues
  | .raised _sourceLocals sourceGlobals sourceMemory exception value,
      .raised crepState exceptionCode =>
      ∃ spillAddress,
        panValueCrepRaisedStateRelExceptWithContext structs context sourceGlobals
          sourceMemory crepState (fun address => address = spillAddress) ∧
        exceptionRel exception value exceptionCode
  | .broke sourceLocals sourceGlobals sourceMemory, .broke crepState _ =>
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory crepState
  | .continued sourceLocals sourceGlobals sourceMemory, .continued crepState _ =>
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory crepState
  | _, _ => False

theorem panValueCrepControlRelWithContext_normal
    [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepState : CrepState α)
    (hstate : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory crepState) :
    panValueCrepControlRelWithContext structs context exceptionRel
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal crepState) :=
  hstate

theorem panValueCrepControlRelWithContext_returned
    [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceValues : List (PanValue α)) (crepState : CrepState α)
    (crepValues : List α)
    (hstate : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory crepState)
    (hvalues : panValueCrepValuesRel sourceValues crepValues) :
    panValueCrepControlRelWithContext structs context exceptionRel
      (.returned sourceLocals sourceGlobals sourceMemory sourceValues)
      (.returned crepState crepValues) :=
  ⟨hstate, hvalues⟩

theorem panValueCrepControlRelWithContext_raised
    [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (exception : ExceptionId)
    (value : PanValue α) (crepState : CrepState α) (exceptionCode : α)
    (spillAddress : α)
    (hstate : panValueCrepRaisedStateRelExceptWithContext structs context
      sourceGlobals sourceMemory crepState
      (fun address => address = spillAddress))
    (hexception : exceptionRel exception value exceptionCode) :
    panValueCrepControlRelWithContext structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory exception value)
      (.raised crepState exceptionCode) :=
  ⟨spillAddress, hstate, hexception⟩

 theorem panValueCrepControlRelWithContext_normal_to_controlRel
    [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepState : CrepState α)
    (hrel : panValueCrepControlRelWithContext structs context exceptionRel
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal crepState)) :
    panValueCrepControlRel structs context exceptionRel
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal crepState) :=
  hrel.2.2

theorem panValueCrepControlRelWithContext_returned_to_controlRel
    [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceValues : List (PanValue α)) (crepState : CrepState α)
    (crepValues : List α)
    (hrel : panValueCrepControlRelWithContext structs context exceptionRel
      (.returned sourceLocals sourceGlobals sourceMemory sourceValues)
      (.returned crepState crepValues)) :
    panValueCrepControlRel structs context exceptionRel
      (.returned sourceLocals sourceGlobals sourceMemory sourceValues)
      (.returned crepState crepValues) :=
  ⟨hrel.1.2.2, hrel.2⟩

theorem panValueCrepControlRelWithContext_raised_to_controlRel
    [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (exception : ExceptionId)
    (value : PanValue α) (crepState : CrepState α) (exceptionCode : α)
    (hrel : panValueCrepControlRelWithContext structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory exception value)
      (.raised crepState exceptionCode)) :
    panValueCrepControlRel structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory exception value)
      (.raised crepState exceptionCode) := by
  rcases hrel with ⟨spillAddress, hstate, hexception⟩
  exact ⟨spillAddress, ⟨hstate.2.2, hexception⟩⟩

end Flapjack
