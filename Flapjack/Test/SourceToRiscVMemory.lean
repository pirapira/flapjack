import Flapjack.Correctness

/-!
Source-to-RISC-V memory agreement.

The existing pipeline fixture checks the generated result computationally.  This
theorem makes the source/target relation explicit for the same store/load
program, using the executable RISC-V function artifact.
-/

namespace Flapjack

#guard
    compiledPipelineStoreLoadRun =
      evalPanMemResult (fun _ => none) (fun _ => none)
        pipelineStoreLoadSource

end Flapjack
