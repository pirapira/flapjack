import Flapjack.CrepeSourceWordRecordAssignmentCorrectness

namespace Flapjack

def sourceWordRecordAssignmentContext : CompileContext Nat :=
  { vars := [("x", (.comb [.one, .one], [0, 1]))], functions := [],
    exceptions := [], maxVar := 2, bytesInWord := 8 }

def sourceWordRecordAssignmentState : CrepState Nat :=
  { locals := fun slot => if slot = 0 then some 1 else
      if slot = 1 then some 2 else none,
    memory := fun _ => none }

theorem closed_source_word_record_assignment_relation :
    evalCrepFullResultState [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 30 sourceWordRecordAssignmentState
        (compileProg sourceWordRecordAssignmentContext
          (.seq (.assign .local "x"
              (.rStruct [.const 3, .const 4]))
            (.return (.var .local "x")))) =
      (evalPanValueProg [] 0 0 8
        (fun name => if name == "x" then
          some (.rStruct [.word 1, .word 2]) else none)
        (fun _ => none) (fun _ => none)
        (.seq (.assign .local "x"
            (.rStruct [.const 3, .const 4]))
          (.return (.var .local "x")))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  have hrel : panValueCrepStateRel [] sourceWordRecordAssignmentContext
      (fun name => if name == "x" then
        some (.rStruct [.word 1, .word 2]) else none)
      (fun _ => none) (fun _ => none) sourceWordRecordAssignmentState := by
    refine ⟨rfl, ?_, rfl⟩
    intro name value shape slots hvalue hlookup
    simp [sourceWordRecordAssignmentContext, lookupInfo] at hlookup
    rcases hlookup with ⟨rfl, rfl, rfl⟩
    simp at hvalue
    subst value
    simp [sourceWordRecordAssignmentState, readCrepLocals,
      panValueShape, panShapeMatches, panShapeMatches.panShapeListMatches,
      panValueFlatWords, panValueFlatWordsFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel]
  have h := compile_full_pan_value_local_assign_record_source_word_relation
    (α := Nat) (context := sourceWordRecordAssignmentContext) (structs := [])
    (sourceLocals := fun name => if name == "x" then
      some (.rStruct [.word 1, .word 2]) else none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordRecordAssignmentState)
    (primitive := fun _ _ => none) (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none) (baseAddress := 0) (topAddress := 0)
    (bytesInWord := 8) (name := "x") (slotLeft := 0) (slotRight := 1)
    (oldLeft := 1) (oldRight := 2) (left := 3) (right := 4)
    (hlookup := by simp [sourceWordRecordAssignmentContext, lookupInfo])
    (hdistinct := by decide) (hlocals := by simp)
    (hrel := hrel)
    (hnoalias := by
      intro oldName oldShape oldSlots hne hlookup
      simp [sourceWordRecordAssignmentContext, lookupInfo] at hlookup
      rcases hlookup with ⟨hname, _, _⟩
      exact False.elim (hne hname.symm))
  exact h.1

end Flapjack
