import Flapjack.CrepeSourceWordLoopCorrectness

namespace Flapjack

def sourceWordLoopContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordLoopState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

theorem closed_source_word_while_zero_bridge :
    ∃ result,
      evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 2 sourceWordLoopState
        (compileProg sourceWordLoopContext
          (.while (SourceWordExp.const (0 : Nat)).toExp .skip)) = some result := by
  have hrel : panValueCrepStateRel [] sourceWordLoopContext
      (fun _ => none) (fun _ => none) (fun _ => none) sourceWordLoopState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordLoopContext _, rfl⟩
  have h := compile_full_pan_value_while_source_word_zero_relation (α := Nat)
    (context := sourceWordLoopContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordLoopState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8) (fuel := 1)
    (condition := .const 0) (body := .skip) (compiledBody := .skip)
    (sourceCondition := 0) (targetCondition := 0)
    (exceptionRel := fun _ _ _ => True) (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceCondition := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hconditionAgreement := rfl) (hzero := rfl)
    (hcompileBody := by simp [compileProg])
  exact ⟨_, h.2.1⟩

end Flapjack
