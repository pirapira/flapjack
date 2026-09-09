import Flapjack.RiscV.CorrectnessSpill

/-!
# StackLang parallel-move correctness

The spill-aware function-entry lowering uses the scratch-aware physical
parallel-move compiler.  This file connects its singleton boundary to the
location-level machine relation; larger move lists can build on the same
equation while proving their scheduling invariants.
-/

namespace Flapjack.RiscV

theorem wordStackParallelLocationMove_singleton
    (config : WordStackConfig) (destination source : WordLocation)
    (hdestinationScratch : destination ≠ .register config.scratch)
    (hdestinationAddressScratch :
      destination ≠ .register config.addressScratch)
    (hsourceScratch : source ≠ .register config.scratch)
    (hsourceAddressScratch : source ≠ .register config.addressScratch) :
    wordStackParallelLocationMove (α := Nat) config [(destination, source)] =
      wordStackLocationMove (α := Nat) config destination source := by
  cases destination with
  | register destination =>
      cases source with
      | register source =>
          by_cases hsame : destination = source
          · subst source
            simp [wordStackParallelLocationMove,
              wordStackParallelLocationMoveAux,
              wordStackLocationMoveDestinations,
              wordStackLocationMoveReady,
              wordStackLocationMoveRemoveDestination, wordStackLocationMove,
              wordStackJoin,
              hdestinationScratch, hdestinationAddressScratch]
          · simp [wordStackParallelLocationMove,
              wordStackParallelLocationMoveAux,
              wordStackLocationMoveDestinations,
              wordStackLocationMoveReady,
              wordStackLocationMoveRemoveDestination, wordStackLocationMove,
              wordStackJoin,
              hsame, Ne.symm hsame, hdestinationScratch,
              hdestinationAddressScratch, hsourceScratch,
              hsourceAddressScratch]
      | stack source =>
          simp [wordStackParallelLocationMove,
            wordStackParallelLocationMoveAux,
            wordStackLocationMoveDestinations,
            wordStackLocationMoveReady,
            wordStackLocationMoveRemoveDestination, wordStackLocationMove,
            wordStackJoin,
            hdestinationScratch, hdestinationAddressScratch, hsourceScratch,
            hsourceAddressScratch]
  | stack destination =>
      cases source with
      | register source =>
          simp [wordStackParallelLocationMove,
            wordStackParallelLocationMoveAux,
            wordStackLocationMoveDestinations,
            wordStackLocationMoveReady,
            wordStackLocationMoveRemoveDestination, wordStackLocationMove,
            wordStackJoin,
            hdestinationScratch, hdestinationAddressScratch, hsourceScratch,
            hsourceAddressScratch]
      | stack source =>
          by_cases hsame : destination = source
          · subst source
            simp [wordStackParallelLocationMove,
              wordStackParallelLocationMoveAux,
              wordStackLocationMoveDestinations,
              wordStackLocationMoveReady,
              wordStackLocationMoveRemoveDestination, wordStackLocationMove,
              wordStackJoin,
              hdestinationScratch, hdestinationAddressScratch]
          · simp [wordStackParallelLocationMove,
              wordStackParallelLocationMoveAux,
              wordStackLocationMoveDestinations,
              wordStackLocationMoveReady,
              wordStackLocationMoveRemoveDestination, wordStackLocationMove,
              wordStackJoin,
              hsame, Ne.symm hsame, hdestinationScratch,
              hdestinationAddressScratch, hsourceScratch,
              hsourceAddressScratch]

theorem evalWordStackMachine_parallelLocationMove_singleton_preserves_value
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source : WordLocation)
    (hdestinationScratch : destination ≠ .register config.scratch)
    (hdestinationAddressScratch :
      destination ≠ .register config.addressScratch)
    (hsourceScratch : source ≠ .register config.scratch)
    (hsourceAddressScratch : source ≠ .register config.addressScratch)
    (heval : (wordStackParallelLocationMove config [(destination, source)]).bind
      (evalWordStackMachine state) = some final) :
    wordStackLocationValue config final destination =
      wordStackLocationValue config state source := by
  rw [wordStackParallelLocationMove_singleton config destination source
    hdestinationScratch hdestinationAddressScratch hsourceScratch
    hsourceAddressScratch] at heval
  exact evalWordStackMachine_locationMove_preserves_value
    config state final destination source heval

theorem evalWordStackMachine_parallelLocationMove_singleton_preserves_other_value
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source other : WordLocation)
    (hdestinationScratch : destination ≠ .register config.scratch)
    (hdestinationAddressScratch :
      destination ≠ .register config.addressScratch)
    (hsourceScratch : source ≠ .register config.scratch)
    (hsourceAddressScratch : source ≠ .register config.addressScratch)
    (hotherDestination : other ≠ destination)
    (hotherScratch : other ≠ .register config.scratch)
    (heval : (wordStackParallelLocationMove config [(destination, source)]).bind
      (evalWordStackMachine state) = some final) :
    wordStackLocationValue config final other =
      wordStackLocationValue config state other := by
  rw [wordStackParallelLocationMove_singleton config destination source
    hdestinationScratch hdestinationAddressScratch hsourceScratch
    hsourceAddressScratch] at heval
  exact evalWordStackMachine_locationMove_preserves_other_value
    config state final destination source other hotherDestination hotherScratch heval

end Flapjack.RiscV
