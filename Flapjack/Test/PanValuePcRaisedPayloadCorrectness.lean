import Flapjack.PanToCrepCorrectnessBridge

namespace Flapjack.Test.PanValuePcRaisedPayloadCorrectness

open Flapjack

def raiseContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 9)], maxVar := 0,
    bytesInWord := 8 }

def raiseState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

def raiseResultExceptionCode : ExceptionId → Option Nat
  | "E" => some 9
  | _ => none

/-! A closed source raise supplies the concrete semantic premises needed by the
    Pc raised-result obligation.  In particular, the conclusion retains the
    post-state relation, exception-code lookup, and the flattened global
    payload observation rather than treating the raised branch as opaque. -/
theorem closed_word_raise_pc_hraise :
    panValueCrepStateRel [] raiseContext (fun _ => none) (fun _ => none)
        (fun _ => none) raiseState ∧
      (∃ spillAddress,
        panValueCrepRaisedControlRel [] raiseContext
          (fun _ _ code => code = 9) (fun _ => none) (fun _ => none)
          "E" (.word 3)
          { raiseState with globals := updateMemory raiseState.globals 0 3 }
          9 spillAddress ∧
        raiseResultExceptionCode "E" = some 9 ∧
        (1 ≤ Shape.shapeSize (panValueShape [] (.word 3)) →
          crepPcWordGlobalsLookup
            { raiseState with globals := updateMemory raiseState.globals 0 3 }
            (.word 3) = some (panValueFlatWords (.word 3))) ∧
        Shape.shapeSize (panValueShape [] (.word 3)) ≤ 32) := by
  have hstate : panValueCrepStateRel [] raiseContext
      (fun _ => none) (fun _ => none) (fun _ => none) raiseState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] raiseContext _, rfl⟩
  have h := panValuePcRaisedWordHraise
    (α := Nat) (context := raiseContext) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := raiseState)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (sourceFuel := 2) (targetFuel := 2) (exception := "E")
    (exceptionCode := 9) (value := 3) (expression := .const 3)
    (compiled := .const 3)
    (exceptionRel := fun _ _ code => code = 9)
    (resultExceptionCode := raiseResultExceptionCode)
    (hlookup := by simp [raiseContext, lookupInfo])
    (hcode := by simp [raiseResultExceptionCode])
    (hbytesInWord := rfl) (hrel := hstate)
    (hsource := by
      simp [SourceWordExp.toExp, evalPanValueExp])
    (hcompile := by simp [SourceWordExp.toExp, compileExp])
    (hcompiled := by simp [evalCrepFullExpState, raiseState])
    (hexception := by simp)
    (hfresh := by simp [raiseState, raiseContext])
  exact ⟨h.1, h.2⟩

end Flapjack.Test.PanValuePcRaisedPayloadCorrectness
