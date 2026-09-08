import Flapjack.Test.SourceToLoop
import Flapjack.CorrectnessCalls

/-!
Source-to-Loop call regression.

This keeps the source call evaluator and the generated Loop function table in
the same executable test.  The callee is deliberately small, but the caller
goes through the real declaration-call lowering and therefore exercises
function labels, argument temporaries, return-slot assignment, and the
continuation after the call.
-/

namespace Flapjack

open RiscV

theorem sourceToLoop_identity_call_simulation (value : Word 64) :
    (do
      let functions := pipelineLoopFunctions .rv64i 1
        (compileToCrepe identityCallCompileContext
          (identityCallDeclarations value))
      let (_, main) ← lookupLoopFunction 2 functions
      let result ← evalLoopProgWithFunctions functions 60
        identityCallLoopState main
      pure (loopResultValues result)) =
      (evalPanProgWithCalls identityCallSourceFunctions 20
        (fun _ => none) (identityCallSourceMain value)).map
        (fun result => result.2) := by
  exact compilePanToLoop_identity_call_correct value

#guard
    (do
      let (_, main) ← lookupLoopFunction 2 pipelineCallPipeline.pipeline.loop
      let result ← evalLoopProgWithFunctions pipelineCallPipeline.pipeline.loop
        40 sourceToLoopState main
      pure (loopResultValues result)) =
      (evalPanProgWithCalls pipelineCallSourceFunctions 20
        (fun _ : VarName => none) pipelineCallSourceMain).map
          (fun result => result.2)

#guard
    (do
      let (_, main) ← lookupLoopFunction 2 pipelineCallPipeline.pipeline.loop
      let result ← evalLoopProgWithFunctions pipelineCallPipeline.pipeline.loop
        40 sourceToLoopState main
      pure (loopResultValues result)) = some [BitVec.ofNat 64 41]

end Flapjack
