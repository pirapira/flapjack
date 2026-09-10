import Flapjack.CrepeFfiRelation
import Flapjack.CrepeExpCorrectness
import Flapjack.Test.SourceToCrepeFfi
import Flapjack.Test.CrepeFfiCorrectness

/-!
Regression for the environment-parametric structured FFI relation.  The
external call itself does not inspect the function tables, but a correctness
boundary used inside the complete Pancake pass must preserve them rather than
silently reducing to the empty-environment fragment.
-/

namespace Flapjack

def sourceToCrepeFfiSourceFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("unused", [], .skip)]

def sourceToCrepeFfiFunctions : List (CompiledFunction (RiscV.Word 64)) :=
  [{ name := "unused", params := [], body := .skip, returnShape := .one }]

def sourceToCrepeFfiStructuredHandler :
    PanValueFfiHandler (RiscV.Word 64) :=
  fun function configuration _ _ _ locals =>
    if function == "inc" then
      some (updatePanValueMap locals "result"
        (.word (configuration + 1)))
    else none

def sourceToCrepeFfiStructuredLocals :
    VarName → Option (PanValue (RiscV.Word 64)) :=
  fun name => if name == "result" then some (.word 0) else none

def sourceToCrepeFfiStructuredAfter :
    VarName → Option (PanValue (RiscV.Word 64)) :=
  fun name => if name == "result" then
    some (.word (BitVec.ofNat 64 42)) else none

theorem sourceToCrepeFfi_nonempty_environment_relation :
    evalPanValueProgWithPrimitiveCallsAndFfi
      (fun _ _ => none) sourceToCrepeFfiStructuredHandler []
      sourceToCrepeFfiSourceFunctions
      0 100 8 26 sourceToCrepeFfiStructuredLocals
      (fun _ => none) (fun _ => none)
      sourceToCrepeFfiProgram =
      some (.normal sourceToCrepeFfiStructuredAfter
        (fun _ => none) (fun _ => none)) ∧
    evalCrepFullProg sourceToCrepeFfiFunctions
      (fun _ _ => none) sourceToCrepeFfiHandler sourceToCrepeFfiSharedMem
      0 100 30 sourceToCrepeFfiState
      (compileProg sourceToCrepeFfiContext sourceToCrepeFfiProgram) =
      some (.normal
        (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
          sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar)) ∧
    panValueCrepControlRel [] sourceToCrepeFfiContext
      (fun _ _ _ => False)
      (.normal sourceToCrepeFfiStructuredAfter
        (fun _ => none) (fun _ => none))
      (.normal
        (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
          sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar)) := by
  have hrel : panValueCrepStateRel [] sourceToCrepeFfiContext
      sourceToCrepeFfiStructuredAfter (fun _ => none) (fun _ => none)
      (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
        sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro name value shape slots hvalue hlookup
      simp [sourceToCrepeFfiStructuredAfter] at hvalue
      by_cases hname : name == "result"
      · have hname' : name = "result" := by simpa using hname
        subst name
        rcases hvalue with ⟨_, hvalue⟩
        have hlookup'' : Shape.one = shape ∧ [1] = slots := by
          simpa [sourceToCrepeFfiContext, lookupInfo] using hlookup
        have hlookup' : shape = .one ∧ slots = [1] :=
          ⟨hlookup''.1.symm, hlookup''.2.symm⟩
        rcases hlookup' with ⟨rfl, rfl⟩
        subst value
        simp [sourceToCrepeFfiContext,
          panValueShape, panShapeMatches, readCrepLocals,
          panValueFlatWords, panValueFlatWordsFuel,
          restoreCrepFfiTemps, sourceToCrepeFfiTargetAfter,
          sourceToCrepeFfiTargetAfterTemps, sourceToCrepeFfiState,
          updateCrepLocal, restoreCrepLocal]
      · have hvalue' : name == "result" := by simpa using hvalue.1
        exact False.elim (hname hvalue')
    · funext address
      simp [panValueWordMemory, restoreCrepFfiTemps,
        sourceToCrepeFfiTargetAfter, sourceToCrepeFfiTargetAfterTemps,
        sourceToCrepeFfiState]
  apply compile_full_pan_value_extCall_relation
    (context := sourceToCrepeFfiContext) (structs := [])
    (sourceFunctions := sourceToCrepeFfiSourceFunctions)
    (functions := sourceToCrepeFfiFunctions)
    (sourceLocals := sourceToCrepeFfiStructuredLocals)
    (sourceLocals' := sourceToCrepeFfiStructuredAfter)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (state := sourceToCrepeFfiState)
    (state' := sourceToCrepeFfiTargetAfter)
    (primitive := fun _ _ => none)
    (crepPrimitive := sourceToCrepeFfiPrimitive)
    (ffi := sourceToCrepeFfiHandler)
    (sharedMem := sourceToCrepeFfiSharedMem)
    (sourceHandler := sourceToCrepeFfiStructuredHandler)
    (baseAddress := 0) (topAddress := 100) (bytesInWord := 8)
    (fuel := 25) (function := "inc")
    (configuration := .const (BitVec.ofNat 64 41))
    (configurationLength := .const 0) (array := .const 0)
    (arrayLength := .const 0)
    (configuration' := .const (BitVec.ofNat 64 41))
    (configurationLength' := .const 0) (array' := .const 0)
    (arrayLength' := .const 0)
    (configurationValue := BitVec.ofNat 64 41)
    (configurationLengthValue := 0) (arrayValue := 0)
    (arrayLengthValue := 0)
    (hconfiguration := by
      simp [sourceToCrepeFfiContext, firstCompiledExp, compileExp])
    (hconfigurationLength := by
      simp [sourceToCrepeFfiContext, firstCompiledExp, compileExp])
    (harray := by
      simp [sourceToCrepeFfiContext, firstCompiledExp, compileExp])
    (harrayLength := by
      simp [sourceToCrepeFfiContext, firstCompiledExp, compileExp])
    (hsourceValues := by
      simpa [evalPanValueExps] using
        (evalPanValueExp_const_words_list [] sourceToCrepeFfiStructuredLocals
          (fun _ => none) (fun _ => none) 0 100 8
          [BitVec.ofNat 64 41, 0, 0, 0]))
    (hconfigurationValue := by
      simp [sourceToCrepeFfiState, evalCrepFullExp])
    (hconfigurationLengthValue := by
      simp [sourceToCrepeFfiState, evalCrepFullExp])
    (harrayValue := by
      simp [sourceToCrepeFfiState, evalCrepFullExp])
    (harrayLengthValue := by
      simp [sourceToCrepeFfiState, evalCrepFullExp])
    (hsource := by
      have hafter :
          updatePanValueMap sourceToCrepeFfiStructuredLocals "result"
              (.word (BitVec.ofNat 64 42)) =
            sourceToCrepeFfiStructuredAfter := by
        funext name
        by_cases hname : name == "result" <;>
          simp [sourceToCrepeFfiStructuredLocals,
            sourceToCrepeFfiStructuredAfter, updatePanValueMap, hname]
      simp only [sourceToCrepeFfiStructuredHandler, beq_self_eq_true,
        ite_true]
      simpa using congrArg some hafter)
    (hffi := by
      simp [sourceToCrepeFfiHandler, sourceToCrepeFfiState,
        sourceToCrepeFfiContext, sourceToCrepeFfiTargetAfterTemps,
        sourceToCrepeFfiTargetAfter])
    hrel

end Flapjack
