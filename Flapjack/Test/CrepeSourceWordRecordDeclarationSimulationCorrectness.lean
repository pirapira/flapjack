import Flapjack.CrepeSourceWordRecordDeclarationSimulationCorrectness

namespace Flapjack

def sourceWordRecordDeclarationSimulationContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def sourceWordRecordDeclarationSimulationState : CrepState Nat :=
  { locals := fun slot => if slot = 1 then some 9 else none,
    memory := fun _ => none }

theorem closed_source_word_record_declaration_skip_relation :
    panValueCrepStateRel [] sourceWordRecordDeclarationSimulationContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      sourceWordRecordDeclarationSimulationState →
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 10
        sourceWordRecordDeclarationSimulationState
        (compileProg sourceWordRecordDeclarationSimulationContext
          (.dec "x" (.comb [.one, .one])
            (.rStruct [.const 3, .const 4]) .skip)) =
      some (.normal sourceWordRecordDeclarationSimulationState) := by
  intro hrel
  exact (compile_full_pan_value_dec_two_word_skip_source_word_relation
    (α := Nat) (context := sourceWordRecordDeclarationSimulationContext)
    (structs := []) (sourceLocals := fun _ => none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordRecordDeclarationSimulationState)
    (primitive := fun _ _ => none) (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none) (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none) (baseAddress := 0) (topAddress := 0)
    (bytesInWord := 8) (name := "x") (left := 3) (right := 4) hrel).2.1

end Flapjack
