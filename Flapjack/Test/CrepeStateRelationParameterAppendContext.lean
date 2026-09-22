import Flapjack.CrepeStateRelationParameterAppendContext

namespace Flapjack.Test.CrepeStateRelationParameterAppendContext

open Flapjack

def baseContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 2, bytesInWord := 8 }

def parameter : CalleeParameter Nat :=
  { name := "x", shape := .one, slots := [2], value := .word 7, values := [7] }

def targetContext : CompileContext Nat :=
  addCalleeParameterContextAppend baseContext parameter

theorem parameter_append_context_fixture :
    panValueCrepStateRelWithContext ([] : StructContext) targetContext
      (updatePanValueMap (fun _ => none) "x" (.word 7)) (fun _ => none)
      (fun _ => none)
      { locals := updateCrepLocalList (fun _ => none) [2] [7]
        memory := fun _ => none } := by
  apply panValueCrepStateRelWithContext_add_parameter_append_fresh
    ([] : StructContext) baseContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none }
    parameter
  · refine ⟨panValueNoOverlap_empty, panValueCtxtMax_empty 2 (by omega), ?_⟩
    exact ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩
  · simp [parameter, baseContext, lookupInfo]
  · simp [parameter, panValueShape, panShapeMatches]
  · rfl
  · simp [parameter, CrepDistinctNames]
  · simp [parameter, panValueFlatWords, panValueFlatWordsFuel]
  · intro oldName oldShape oldSlots hne hlookup slot hslot
    simp [baseContext, lookupInfo] at hlookup
  · refine ⟨?_, ?_⟩
    · simp [parameter, addCalleeParameterContextAppend, baseContext, lookupInfo]
    · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
      have hname : name = "x" := by
        by_cases hne : name = "x"
        · exact hne
        · simp [parameter, addCalleeParameterContextAppend, baseContext, lookupInfo, Ne.symm hne] at hlookup
      have hname' : name' = "x" := by
        by_cases hne : name' = "x"
        · exact hne
        · simp [parameter, addCalleeParameterContextAppend, baseContext, lookupInfo, Ne.symm hne] at hlookup'
      exact hname.trans hname'.symm
  · simp [parameter, addCalleeParameterContextAppend, baseContext, panValueCtxtMax, lookupInfo]

#check @Flapjack.panValueCrepStateRelWithContext_add_parameter_append_fresh

end Flapjack.Test.CrepeStateRelationParameterAppendContext
