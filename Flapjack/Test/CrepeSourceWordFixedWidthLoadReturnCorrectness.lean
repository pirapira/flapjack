import Flapjack.CrepeSourceWordFixedWidthLoadReturnCorrectness

namespace Flapjack

def sourceWordFixedWidthLoadContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordFixedWidthLoadState : CrepState Nat :=
  { locals := fun _ => none,
    memory := fun address => if address = 4 then some 1 else none }

theorem closed_source_word_load32_return_bridge :
    ∃ result,
      evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 1 sourceWordFixedWidthLoadState
        (compileProg sourceWordFixedWidthLoadContext
          (.return (.load32 (SourceWordExp.const (4 : Nat)).toExp))) =
      some result := by
  have hrel : panValueCrepStateRel [] sourceWordFixedWidthLoadContext
      (fun _ => none) (fun _ => none)
      (fun address => if address = 4 then some (.word 1) else none)
      sourceWordFixedWidthLoadState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordFixedWidthLoadContext _, ?_⟩
    funext address
    by_cases haddress : address = 4 <;>
      simp [panValueWordMemory, sourceWordFixedWidthLoadState, haddress]
  have h := compile_full_pan_value_return_load32_relation (α := Nat)
    (context := sourceWordFixedWidthLoadContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none)
    (sourceMemory := fun address =>
      if address = 4 then some (.word 1) else none)
    (state := sourceWordFixedWidthLoadState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (address := .const 4) (addressValue := 4) (value := 1)
    (exceptionRel := fun _ _ _ => True) (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceAddress := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hsource := by simp [SourceWordExp.toExp, evalPanValueExp])
  exact ⟨_, h.2.1⟩

theorem closed_source_word_loadByte_return_bridge :
    ∃ result,
      evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 1 sourceWordFixedWidthLoadState
        (compileProg sourceWordFixedWidthLoadContext
          (.return (.loadByte (SourceWordExp.const (4 : Nat)).toExp))) =
      some result := by
  have hrel : panValueCrepStateRel [] sourceWordFixedWidthLoadContext
      (fun _ => none) (fun _ => none)
      (fun address => if address = 4 then some (.word 1) else none)
      sourceWordFixedWidthLoadState := by
    refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceWordFixedWidthLoadContext _, ?_⟩
    funext address
    by_cases haddress : address = 4 <;>
      simp [panValueWordMemory, sourceWordFixedWidthLoadState, haddress]
  have h := compile_full_pan_value_return_loadByte_relation (α := Nat)
    (context := sourceWordFixedWidthLoadContext) (structs := [])
    (sourceFunctions := []) (functions := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none)
    (sourceMemory := fun address =>
      if address = 4 then some (.word 1) else none)
    (state := sourceWordFixedWidthLoadState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none) (crepPrimitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none) (sharedMem := fun _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (address := .const 4) (addressValue := 4) (value := 1)
    (exceptionRel := fun _ _ _ => True) (hbytesInWord := rfl) (hlocals := hrel)
    (hlookup := by
      intro name value hvalue
      simp at hvalue)
    (hsourceAddress := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hsource := by simp [SourceWordExp.toExp, evalPanValueExp])
  exact ⟨_, h.2.1⟩

end Flapjack
