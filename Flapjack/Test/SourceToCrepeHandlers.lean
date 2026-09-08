import Flapjack.CrepeCorrectness
import Flapjack.Test.SourceToLoopHandlers

/-!
Source-to-full-Crepe exception-handler regression.

The source and compiled programs are evaluated through their respective
handler-aware semantics.  Unlike the smaller Crepe evaluator, the full
evaluator carries the global-memory payload used by `assignRet` across the
callee boundary.
-/

namespace Flapjack

open RiscV

def sourceToCrepeHandlerState : CrepState (Word 64) :=
  { locals := fun _ => none
    memory := fun _ => none }

def sourceToCrepeHandlerPrimitive : CrepPrimitiveHandler (Word 64) :=
  fun _ _ => none

def sourceToCrepeHandlerFfi : CrepFfiHandler (Word 64) :=
  noCrepFfi (Word 64)

def sourceToCrepeHandlerSharedMem : CrepSharedMemHandler (Word 64) :=
  defaultCrepSharedMemHandler

theorem sourceToCrepe_handler_simulation :
    (do
      let (_, main) ← lookupCompiledFunction "main"
        sourceToLoopHandlerPipeline.pipeline.crepe
      evalCrepFullResult sourceToLoopHandlerPipeline.pipeline.crepe
        sourceToCrepeHandlerPrimitive sourceToCrepeHandlerFfi
        sourceToCrepeHandlerSharedMem
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) 80
        sourceToCrepeHandlerState main) =
      (evalPanProgWithHandlers sourceToLoopHandlerFunctions 30
        (fun _ : VarName => none) sourceToLoopHandlerMain).map (fun result =>
          match result with
          | .returned _ values => values
          | _ => []) := by
  native_decide

theorem sourceToCrepe_handler_executes :
    (do
      let (_, main) ← lookupCompiledFunction "main"
        sourceToLoopHandlerPipeline.pipeline.crepe
      evalCrepFullResult sourceToLoopHandlerPipeline.pipeline.crepe
        sourceToCrepeHandlerPrimitive sourceToCrepeHandlerFfi
        sourceToCrepeHandlerSharedMem
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) 80
        sourceToCrepeHandlerState main) = some [BitVec.ofNat 64 7] := by
  native_decide

end Flapjack
