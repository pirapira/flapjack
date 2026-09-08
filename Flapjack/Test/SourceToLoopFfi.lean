import Flapjack.CorrectnessFfi
import Flapjack.Test.CorrectnessFfi
import Flapjack.Test.SourceToLoop

/-!
Source-to-Loop FFI regression.

The source handler updates the declaration local named `result`; the generated
Loop handler must update that local's allocated slot instead.  The theorem
therefore exercises declaration lowering, FFI argument materialization, the
Loop FFI callback, and the caller's declaration-call continuation together.
-/

namespace Flapjack

open RiscV

def successfulLoopFfiHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    LoopState (Word 64) → Option (LoopState (Word 64)) :=
  fun _ configuration _ _ _ state =>
    some { state with
      locals := updateLoopLocal state.locals 1 configuration }

def successfulSourceFfiHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    (VarName → Option (Word 64)) → Option (VarName → Option (Word 64)) :=
  fun _ configuration _ _ _ locals =>
    some (updatePanLocal locals "result" configuration)

def sourceToLoopFfiState : LoopState (Word 64) :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def sourceToLoopFfiHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    LoopState (Word 64) → Option (LoopState (Word 64)) :=
  fun function configuration _ _ _ state =>
    if function == "inc" then
      some { state with
        locals := updateLoopLocal state.locals 2 (configuration + 1) }
    else none

theorem sourceToLoop_compiled_ffi_equation :
    evalLoopProgWithCallsAndFfi [] sourceToLoopFfiHandler 1
      sourceToLoopFfiState
      (loopCompileProg sourceToLoopLoopContext [7]
        (.extCall "inc" 1 2 3 4)) =
      (do
        let configuration ← sourceToLoopFfiState.locals 1
        let configurationLength ← sourceToLoopFfiState.locals 2
        let array ← sourceToLoopFfiState.locals 3
        let arrayLength ← sourceToLoopFfiState.locals 4
        let state ← sourceToLoopFfiHandler "inc" configuration configurationLength
          array arrayLength sourceToLoopFfiState
        pure (.normal state)) := by
  exact evalLoopCompiledExtCall sourceToLoopLoopContext [] sourceToLoopFfiHandler 0
    sourceToLoopFfiState [7] "inc" 1 2 3 4

#guard
    (evalLoopProgWithCallsAndFfi [] successfulLoopFfiHandler 40
      sourceToLoopFfiState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext
          (.extCall "inc" (.const (BitVec.ofNat 64 41))
            (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 0))
            (.const (BitVec.ofNat 64 0)))))).map loopResultValues =
      (evalPanProgWithCallsAndFfi [] successfulSourceFfiHandler 20
        (fun _ => none)
        (.extCall "inc" (.const (BitVec.ofNat 64 41))
          (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 0))
          (.const (BitVec.ofNat 64 0)))).map (fun result =>
            match result with
            | .normal _ => []
            | .returned _ values => values
            | .raised _ _ _ => [])

theorem sourceToLoop_ffi_simulation :
    (do
      let (_, main) ← lookupLoopFunction 2 sourceFfiPipeline.pipeline.loop
      let result ← evalLoopProgWithCallsAndFfi sourceFfiPipeline.pipeline.loop
        sourceToLoopFfiHandler 60 sourceToLoopFfiState main
      pure (loopResultValues result)) =
      (evalPanProgWithCallsAndFfi sourceFfiFunctions sourceFfiHandler 20
        (fun _ : VarName => none) sourceFfiMainBody).map (fun result =>
          match result with
          | .returned _ values => values
          | _ => []) := by
  native_decide

#guard
    (do
      let (_, main) ← lookupLoopFunction 2 sourceFfiPipeline.pipeline.loop
      let result ← evalLoopProgWithCallsAndFfi sourceFfiPipeline.pipeline.loop
        sourceToLoopFfiHandler 60 sourceToLoopFfiState main
      pure (loopResultValues result)) = some [BitVec.ofNat 64 42]

end Flapjack
