import Flapjack.CrepeSourceWordLoadReturnCorrectness

namespace Flapjack

def sourceWordLoadReturnContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordLoadReturnState : CrepState Nat :=
  { locals := fun _ => none,
    memory := fun address => if address = 4 then some 1 else none }

theorem closed_source_word_load_return_bridge :
    ∃ result,
      evalCrepFullProgState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 1 sourceWordLoadReturnState
        (compileProg sourceWordLoadReturnContext
          (.return (.load .one (SourceWordExp.const (4 : Nat)).toExp))) =
      some result := by
  have hrel : panValueCrepStateRel [] sourceWordLoadReturnContext
      (fun _ => none) (fun _ => none)
      (fun address => if address = 4 then some (.word 1) else none)
      sourceWordLoadReturnState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordLoadReturnContext _, ?_⟩
    funext address
    by_cases haddress : address = 4 <;>
      simp [panValueWordMemory, sourceWordLoadReturnState, haddress]
  have h := compile_full_pan_value_return_load_one_relation (α := Nat)
    (context := sourceWordLoadReturnContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none)
    (sourceMemory := fun address =>
      if address = 4 then some (.word 1) else none)
    (state := sourceWordLoadReturnState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (address := .const 4) (addressValue := 4) (value := 1)
    (exceptionRel := fun _ _ _ => True) (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceAddress := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hsource := by
      simp [SourceWordExp.toExp, evalPanValueExp, panValueFlatLoad,
        panValueFlatLoadFuel, panValueFlatReadWord, isWfShape])
  exact ⟨_, h.2.1⟩

end Flapjack
