import Flapjack.CrepeSequenceCorrectness
import Flapjack.Test.CrepeFfiRelation

/-!
The structured FFI relation composes with a source continuation.  The
continuation test is deliberately run with different source and Crep fuel
budgets: the compiled FFI lowering consumes five target steps for one source
step.
-/

namespace Flapjack

def sourceToCrepeFfiStructuredContinuation : Prog (RiscV.Word 64) :=
  .return (.var .local "result")

def sourceToCrepeFfiStructuredSequence : Prog (RiscV.Word 64) :=
  .seq sourceToCrepeFfiProgram sourceToCrepeFfiStructuredContinuation

theorem sourceToCrepeFfi_sequence_relation :
    evalPanValueProgWithPrimitiveCallsAndFfi
      (fun _ _ => none) sourceToCrepeFfiStructuredHandler []
      sourceToCrepeFfiSourceFunctions
      0 100 8 27 sourceToCrepeFfiStructuredLocals
      (fun _ => none) (fun _ => none)
      sourceToCrepeFfiStructuredSequence =
      some (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        [.word (BitVec.ofNat 64 42)]) ∧
    evalCrepFullProgState sourceToCrepeFfiFunctions
      (fun _ _ => none) sourceToCrepeFfiHandler sourceToCrepeFfiSharedMem
      0 100 31 sourceToCrepeFfiState
      (compileProg sourceToCrepeFfiContext
        sourceToCrepeFfiStructuredSequence) =
      some (.returned
        (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
          sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar)
        [BitVec.ofNat 64 42]) ∧
    panValueCrepControlRel [] sourceToCrepeFfiContext
      (fun _ _ _ => False)
      (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        [.word (BitVec.ofNat 64 42)])
      (.returned
        (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
          sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar)
        [BitVec.ofNat 64 42]) := by
  have hfirst := sourceToCrepeFfi_nonempty_environment_relation
  let targetAfter :=
    restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
      sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar
  have hsourceSecond :
      evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) sourceToCrepeFfiStructuredHandler [] 
        sourceToCrepeFfiSourceFunctions
        0 100 8 (25 + 1) sourceToCrepeFfiStructuredAfter
        (fun _ => none) (fun _ => none)
        sourceToCrepeFfiStructuredContinuation =
      some (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        [.word (BitVec.ofNat 64 42)]) := by
    simp [sourceToCrepeFfiStructuredContinuation,
      sourceToCrepeFfiStructuredAfter,
      evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp]
  have hfirstCrepState :
      evalCrepFullProgState sourceToCrepeFfiFunctions
        (fun _ _ => none) sourceToCrepeFfiHandler sourceToCrepeFfiSharedMem
        0 100 30 sourceToCrepeFfiState
        (compileProg sourceToCrepeFfiContext sourceToCrepeFfiProgram) =
      some (.normal targetAfter) := by
    simp [sourceToCrepeFfiProgram, sourceToCrepeFfiContext,
      sourceToCrepeFfiState, sourceToCrepeFfiHandler,
      targetAfter,
      sourceToCrepeFfiTargetAfter, sourceToCrepeFfiTargetAfterTemps,
      restoreCrepFfiTemps, compileProg, firstCompiledExp, compileExp,
      nestedDecs, evalCrepFullProgState, evalCrepFullExpState,
      updateCrepLocal, restoreCrepResult]
  have htargetLocal : targetAfter.locals 1 =
      some (BitVec.ofNat 64 42) := by
    simp [targetAfter, restoreCrepFfiTemps, sourceToCrepeFfiTargetAfter,
      sourceToCrepeFfiTargetAfterTemps, sourceToCrepeFfiState,
      updateCrepLocal, restoreCrepLocal]
    decide
  have hcompileSecond :
      compileProg sourceToCrepeFfiContext
        sourceToCrepeFfiStructuredContinuation = .return [.var 1] := by
    simp [sourceToCrepeFfiStructuredContinuation,
      sourceToCrepeFfiContext, compileProg, compileExp, lookupInfo]
  have hcrepSecond :
      evalCrepFullProgState sourceToCrepeFfiFunctions
        (fun _ _ => none) sourceToCrepeFfiHandler sourceToCrepeFfiSharedMem
        0 100 (29 + 1) targetAfter
        (.return [.var 1]) =
      some (.returned targetAfter [BitVec.ofNat 64 42]) := by
    simp [evalCrepFullProgState, evalCrepFullExpsState, evalCrepFullExpState,
      htargetLocal]
  have hsecondRel :
      panValueCrepControlRel [] sourceToCrepeFfiContext
        (fun _ _ _ => False)
        (.returned (fun _ => none) (fun _ => none) (fun _ => none)
          [.word (BitVec.ofNat 64 42)])
        (.returned targetAfter [BitVec.ofNat 64 42]) := by
    have hpost :
        panValueCrepStateRel [] sourceToCrepeFfiContext
          (fun _ => none) (fun _ => none) (fun _ => none) targetAfter := by
      refine ⟨rfl, panValueCrepLocalsRel_empty [] sourceToCrepeFfiContext
        targetAfter.locals, ?_⟩
      funext address
      simp [panValueWordMemory, targetAfter, restoreCrepFfiTemps,
        sourceToCrepeFfiTargetAfter, sourceToCrepeFfiTargetAfterTemps,
        sourceToCrepeFfiState]
    exact ⟨hpost, panValueCrepValuesRel_singleton (.word
      (BitVec.ofNat 64 42))⟩
  apply compile_full_pan_value_seq_normal_relation_mixed_fuel
    (context := sourceToCrepeFfiContext) (structs := [])
    (sourceFunctions := sourceToCrepeFfiSourceFunctions)
    (functions := sourceToCrepeFfiFunctions)
    (sourceLocals := sourceToCrepeFfiStructuredLocals)
    (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
    (sourceFirstLocals := sourceToCrepeFfiStructuredAfter)
    (sourceFirstGlobals := fun _ => none)
    (sourceFirstMemory := fun _ => none)
    (state := sourceToCrepeFfiState) (firstState := targetAfter)
    (primitive := fun _ _ => none)
    (sourceHandler := sourceToCrepeFfiStructuredHandler)
    (crepPrimitive := sourceToCrepeFfiPrimitive)
    (ffi := sourceToCrepeFfiHandler)
    (sharedMem := sourceToCrepeFfiSharedMem)
    (baseAddress := 0) (topAddress := 100) (bytesInWord := 8)
    (sourceFuel := 25) (targetFuel := 29)
    (first := sourceToCrepeFfiProgram)
    (second := sourceToCrepeFfiStructuredContinuation)
    (compiledFirst := compileProg sourceToCrepeFfiContext
      sourceToCrepeFfiProgram)
    (compiledSecond := .return [.var 1])
    (sourceResult := .returned (fun _ => none) (fun _ => none)
      (fun _ => none) [.word (BitVec.ofNat 64 42)])
    (crepResult := .returned targetAfter [BitVec.ofNat 64 42])
    (exceptionRel := fun _ _ _ => False)
    (hcompileFirst := rfl) (hcompileSecond := hcompileSecond)
    (hsourceFirst := hfirst.1) (hcrepFirst := hfirstCrepState)
    (hsourceSecond := hsourceSecond) (hcrepSecond := hcrepSecond)
    hsecondRel

end Flapjack
