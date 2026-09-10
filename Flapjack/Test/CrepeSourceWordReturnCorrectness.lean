import Flapjack.CrepeSourceWordReturnCorrectness

namespace Flapjack

def sourceWordReturnContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordReturnState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

/-! A closed source-word return exercises the generic program bridge. -/
theorem closed_source_word_return_bridge :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) [] []
        (0 : Nat) 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none)
        (.return (SourceWordExp.const (7 : Nat)).toExp) =
      some (.returned (fun _ => none) (fun _ => none) (fun _ => none) [.word 7]) ∧
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 1 sourceWordReturnState
        (compileProg sourceWordReturnContext
          (.return (SourceWordExp.const (7 : Nat)).toExp)) =
      some (.returned sourceWordReturnState [7]) := by
  have hrel : panValueCrepStateRel [] sourceWordReturnContext
      (fun _ => none) (fun _ => none) (fun _ => none) sourceWordReturnState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordReturnContext _, ?_⟩
    rfl
  have hlookup : ∀ (name : VarName) (value : PanValue Nat),
      (fun _ => none) name = some value →
      ∃ slot, lookupInfo name sourceWordReturnContext.vars = some (.one, [slot]) := by
    intro name value hvalue
    simp at hvalue
  have h := compile_full_pan_value_return_source_word_relation (α := Nat)
    (context := sourceWordReturnContext) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none) (state := sourceWordReturnState)
    (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (expression := .const (7 : Nat)) (value := 7)
    (exceptionRel := fun _ _ _ => True) (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := hlookup)
    (hsource := by simp [SourceWordExp.toExp, evalPanValueExp])
  exact ⟨h.1, h.2.1⟩

end Flapjack
