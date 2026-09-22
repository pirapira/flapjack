import Flapjack.CrepeCalleeParameterListContextRelation

namespace Flapjack.Test.CrepeCalleeParameterListContextRelation

open Flapjack

def baseContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 2, bytesInWord := 8 }

def parameter : CalleeParameter Nat :=
  { name := "x", shape := .one, slots := [2], value := .word 7, values := [7] }

def parameters : List (CalleeParameter Nat) := [parameter]

theorem callee_parameter_list_context_fixture :
    panValueCrepStateRelWithContext ([] : StructContext)
      (foldCalleeParameterContextAppend baseContext parameters)
      (foldCalleeParameterSource (fun _ => none) parameters) (fun _ => none)
      (fun _ => none)
      { locals := foldCalleeParameterLocals (fun _ => none) parameters,
        memory := fun _ => none } := by
  apply panValueCrepCalleeStateRelWithContext_parameters_append
    ([] : StructContext) baseContext (fun _ => none) (fun _ => none)
    (fun _ => none) parameters
  · rfl
  · rfl
  · refine ⟨?_, ?_, rfl, ?_, ?_, ?_, trivial⟩
    · simp [parameter, baseContext, lookupInfo]
    · simp [parameter, panValueShape, panShapeMatches]
    · simp [parameter, CrepDistinctNames]
    · simp [parameter, panValueFlatWords, panValueFlatWordsFuel]
    · intro oldName oldShape oldSlots hne hlookup slot hslot
      simp [baseContext, lookupInfo] at hlookup
  · refine ⟨?_, ?_⟩
    · simp [foldCalleeParameterContextAppend, addCalleeParameterContextAppend,
        parameter, parameters, baseContext, lookupInfo]
    · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
      have hname : name = "x" := by
        by_cases hne : name = "x"
        · exact hne
        · simp [foldCalleeParameterContextAppend,
            addCalleeParameterContextAppend, parameter, parameters,
            baseContext, lookupInfo, Ne.symm hne] at hlookup
      have hname' : name' = "x" := by
        by_cases hne : name' = "x"
        · exact hne
        · simp [foldCalleeParameterContextAppend,
            addCalleeParameterContextAppend, parameter, parameters,
            baseContext, lookupInfo, Ne.symm hne] at hlookup'
      exact hname.trans hname'.symm
  · refine ⟨by omega, ?_⟩
    intro name shape slots hlookup slot hslot
    have hname : name = "x" := by
      by_cases hne : name = "x"
      · exact hne
      · simp [foldCalleeParameterContextAppend,
          addCalleeParameterContextAppend, parameter, parameters,
          baseContext, lookupInfo, Ne.symm hne] at hlookup
    subst name
    have hpair : (Shape.one, [2]) = (shape, slots) := by
      simpa [foldCalleeParameterContextAppend,
        addCalleeParameterContextAppend, parameter, parameters,
        baseContext, lookupInfo] using hlookup
    have hslots : [2] = slots := congrArg Prod.snd hpair
    rw [← hslots] at hslot
    simp at hslot
    change slot ≤ 2
    omega

#check @Flapjack.panValueCrepCalleeStateRelWithContext_parameters_append

end Flapjack.Test.CrepeCalleeParameterListContextRelation
