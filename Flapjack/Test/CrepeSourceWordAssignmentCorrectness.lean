import Flapjack.CrepeSourceWordAssignmentCorrectness

namespace Flapjack

def sourceWordAssignmentContext : CompileContext Nat :=
  { vars := [("x", (.one, [0]))], functions := [], exceptions := [],
    maxVar := 1, bytesInWord := 8 }

def sourceWordAssignmentState : CrepState Nat :=
  { locals := fun slot => if slot = 0 then some 3 else none,
    memory := fun _ => none }

theorem closed_source_word_assignment_bridge :
    ∃ result,
      evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 0 2 sourceWordAssignmentState
        (compileProg sourceWordAssignmentContext
          (.assign .local "x" (SourceWordExp.const (7 : Nat)).toExp)) =
      some result := by
  have hrel : panValueCrepStateRel [] sourceWordAssignmentContext
      (fun name => if name == "x" then some (.word 3) else none)
      (fun _ => none) (fun _ => none) sourceWordAssignmentState := by
    refine ⟨rfl, ?_, rfl⟩
    intro name value shape slots hvalue hlookup
    simp [sourceWordAssignmentContext, lookupInfo] at hlookup
    rcases hlookup with ⟨rfl, rfl, rfl⟩
    simp at hvalue
    subst value
    simp [sourceWordAssignmentState, readCrepLocals, panValueShape,
      panShapeMatches, panValueFlatWords, panValueFlatWordsFuel]
  have h := compile_full_pan_value_local_assign_source_word_relation (α := Nat)
    (context := sourceWordAssignmentContext) (structs := [])
    (sourceFunctions := []) (functions := [])
    (sourceLocals := fun name => if name == "x" then some (.word 3) else none)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceWordAssignmentState) (primitive := fun _ _ => none)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (crepPrimitive := fun _ _ => none) (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := fun _ _ _ _ => none) (baseAddress := 0) (topAddress := 0)
    (bytesInWord := 8) (name := "x") (slot := 0) (oldValue := 3) (value := 7)
    (expression := .const 7) (compiled := .const 7)
    (hlookup := by simp [sourceWordAssignmentContext, lookupInfo])
    (hold := by simp) (hsource := by simp [SourceWordExp.toExp, evalPanValueExp])
    (hcompile := by simp [SourceWordExp.toExp, compileExp])
    (hcompiled := by simp [evalCrepFullExp]) (hdistinct := by simp [distinctLists])
    (hrel := hrel)
    (hnoalias := by
      intro oldName oldShape oldSlots hne hlookup
      simp [sourceWordAssignmentContext, lookupInfo] at hlookup
      rcases hlookup with ⟨hname, _, _⟩
      exact False.elim (hne hname.symm))
  exact ⟨_, h.2.1⟩

end Flapjack
