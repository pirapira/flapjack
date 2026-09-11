import Flapjack.CrepeSourceWordConditionalCorrectness

namespace Flapjack

def sourceWordConditionalContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordConditionalState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

theorem closed_source_word_ite_then_bridge :
    ∃ result,
      evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 2 sourceWordConditionalState
        (compileProg sourceWordConditionalContext
          (.ite (SourceWordExp.const (1 : Nat)).toExp
            .skip .skip)) = some result := by
  have hrel : panValueCrepStateRel [] sourceWordConditionalContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      sourceWordConditionalState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordConditionalContext _, rfl⟩
  have h := compile_full_pan_value_ite_source_word_then_relation (α := Nat)
    (context := sourceWordConditionalContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordConditionalState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8) (fuel := 1)
    (condition := .const 1) (thenBranch := .skip) (elseBranch := .skip)
    (compiledThen := .skip) (compiledElse := .skip)
    (sourceCondition := 1) (targetCondition := 1)
    (sourceThenResult := .normal (fun _ => none) (fun _ => none) (fun _ => none))
    (crepThenResult := .normal sourceWordConditionalState)
    (exceptionRel := fun _ _ _ => True) (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceCondition := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hconditionAgreement := rfl) (hnonzero := by decide)
    (hcompileThen := by simp [compileProg]) (hcompileElse := by simp [compileProg])
    (hsourceThen := by simp [evalPanValueProgWithPrimitiveCallsAndFfi])
    (hcrepThen := by simp [evalCrepFullProg]) (hthenRel := hrel)
  exact ⟨_, h.2.1⟩

end Flapjack
