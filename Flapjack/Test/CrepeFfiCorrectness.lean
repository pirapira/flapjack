import Flapjack.CrepeFfiCorrectness
import Flapjack.Test.SourceToCrepeFfi

/-! A concrete regression for the reusable source-to-Crepe FFI boundary. -/

namespace Flapjack

def sourceToCrepeFfiSourceAfter : VarName → Option (RiscV.Word 64) :=
  updatePanLocal sourceToCrepeFfiSourceLocals "result"
    (BitVec.ofNat 64 41 + 1)

def sourceToCrepeFfiTargetAfterTemps : CrepState (RiscV.Word 64) :=
  { sourceToCrepeFfiState with
    locals :=
      updateCrepLocal
        (updateCrepLocal
          (updateCrepLocal
            (updateCrepLocal sourceToCrepeFfiState.locals 2
              (BitVec.ofNat 64 41))
            3 (BitVec.ofNat 64 0))
          4 (BitVec.ofNat 64 0))
        5 (BitVec.ofNat 64 0) }

def sourceToCrepeFfiTargetAfter : CrepState (RiscV.Word 64) :=
  { sourceToCrepeFfiTargetAfterTemps with
    locals := updateCrepLocal sourceToCrepeFfiTargetAfterTemps.locals 1
      (BitVec.ofNat 64 41 + 1) }

theorem sourceToCrepeFfi_simulation_theorem :
    evalCrepFullProg [] sourceToCrepeFfiPrimitive sourceToCrepeFfiHandler
      sourceToCrepeFfiSharedMem 0 100 30 sourceToCrepeFfiState
      (compileProg sourceToCrepeFfiContext sourceToCrepeFfiProgram) =
        some (.normal (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
          sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar)) ∧
      evalPanFfiProg sourceToCrepeFfiSourceHandler
        sourceToCrepeFfiSourceLocals sourceToCrepeFfiProgram =
        some sourceToCrepeFfiSourceAfter := by
  have h := compile_full_extCall_simulation
    (context := sourceToCrepeFfiContext)
    (sourceLocals := sourceToCrepeFfiSourceLocals)
    (sourceLocals' := sourceToCrepeFfiSourceAfter)
    (state := sourceToCrepeFfiState)
    (state' := sourceToCrepeFfiTargetAfter)
    (primitive := sourceToCrepeFfiPrimitive)
    (ffi := sourceToCrepeFfiHandler)
    (sharedMem := sourceToCrepeFfiSharedMem)
    (sourceHandler := sourceToCrepeFfiSourceHandler)
    (baseAddress := 0) (topAddress := 100) (fuel := 25)
    (function := "inc")
    (configuration := .const (BitVec.ofNat 64 41))
    (configurationLength := .const (BitVec.ofNat 64 0))
    (array := .const (BitVec.ofNat 64 0))
    (arrayLength := .const (BitVec.ofNat 64 0))
    (configuration' := .const (BitVec.ofNat 64 41))
    (configurationLength' := .const (BitVec.ofNat 64 0))
    (array' := .const (BitVec.ofNat 64 0))
    (arrayLength' := .const (BitVec.ofNat 64 0))
    (configurationValue := BitVec.ofNat 64 41)
    (configurationLengthValue := BitVec.ofNat 64 0)
    (arrayValue := BitVec.ofNat 64 0)
    (arrayLengthValue := BitVec.ofNat 64 0)
    (hconfiguration := by simp [sourceToCrepeFfiContext, firstCompiledExp,
      compileExp])
    (hconfigurationLength := by simp [sourceToCrepeFfiContext, firstCompiledExp,
      compileExp])
    (harray := by simp [sourceToCrepeFfiContext, firstCompiledExp, compileExp])
    (harrayLength := by simp [sourceToCrepeFfiContext, firstCompiledExp,
      compileExp])
    (hconfigurationValue := by simp [sourceToCrepeFfiState, evalCrepFullExp])
    (hconfigurationLengthValue := by
      simp [sourceToCrepeFfiState, evalCrepFullExp])
    (harrayValue := by simp [sourceToCrepeFfiState, evalCrepFullExp])
    (harrayLengthValue := by
      simp [sourceToCrepeFfiState, evalCrepFullExp])
    (hsource := by
      simp [sourceToCrepeFfiSourceAfter, sourceToCrepeFfiSourceHandler,
        evalPanExtCall, evalPanExp])
    (hffi := by
      simp [sourceToCrepeFfiHandler, sourceToCrepeFfiState,
        sourceToCrepeFfiContext, sourceToCrepeFfiTargetAfterTemps,
        sourceToCrepeFfiTargetAfter])
  have hprogram : sourceToCrepeFfiProgram =
      (.extCall "inc" (.const (BitVec.ofNat 64 41))
        (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 0))
        (.const (BitVec.ofNat 64 0))) := by
    simp [sourceToCrepeFfiProgram]
  rw [hprogram]
  simpa [evalPanFfiProg] using h

#guard sourceToCrepeFfiSourceAfter "result" = some (BitVec.ofNat 64 42)

end Flapjack
