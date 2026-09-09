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

theorem wordStackMovesFromPhysical_singleton
    (config : WordStackConfig) (destination source : Nat)
    (destinationLocation : WordLocation)
    (hdestination :
      wordStackLocation config destination = some destinationLocation) :
    wordStackMovesFromPhysical (α := Nat) config [destination] source =
      wordStackParallelLocationMove (α := Nat) config
        [(destinationLocation, .register source)] := by
  simp [wordStackMovesFromPhysical, wordStackPhysicalMovesFrom, hdestination]

def wordStackPhysicalMovesFromSpec : List WordLocation → Nat →
    List (WordLocation × WordLocation)
  | [], _ => []
  | location :: locations, source =>
      (location, .register source) ::
        wordStackPhysicalMovesFromSpec locations (source + 2)

theorem wordStackPhysicalMovesFrom_mapM'
    (config : WordStackConfig) (destinations : List Nat) (source : Nat) :
    wordStackPhysicalMovesFrom config destinations source =
      (List.mapM' (wordStackLocation config) destinations).map
        (fun locations => wordStackPhysicalMovesFromSpec locations source) := by
  induction destinations generalizing source with
  | nil =>
      simp [wordStackPhysicalMovesFrom, wordStackPhysicalMovesFromSpec,
        List.mapM']
  | cons destination destinations ih =>
      cases hlocation : wordStackLocation config destination with
      | none =>
          simp [wordStackPhysicalMovesFrom, List.mapM', hlocation]
      | some location =>
          cases hrest : List.mapM' (wordStackLocation config) destinations with
          | none =>
              have htail :
                  wordStackPhysicalMovesFrom config destinations (source + 2) =
                    none := by
                rw [ih (source := source + 2), hrest]
                rfl
              simp [wordStackPhysicalMovesFrom, List.mapM', hlocation, hrest,
                htail]
          | some locations =>
              simp [wordStackPhysicalMovesFrom, wordStackPhysicalMovesFromSpec,
                List.mapM', hlocation, hrest, ih]

theorem wordStackPhysicalMovesFrom_eq_spec
    (config : WordStackConfig) (destinations : List Nat) (source : Nat)
    (locations : List WordLocation)
    (hlookup :
      destinations.mapM (wordStackLocation config) = some locations) :
    wordStackPhysicalMovesFrom config destinations source =
      some (wordStackPhysicalMovesFromSpec locations source) := by
  have hlookup' :
      List.mapM' (wordStackLocation config) destinations = some locations := by
    rw [List.mapM'_eq_mapM]
    exact hlookup
  rw [wordStackPhysicalMovesFrom_mapM', hlookup']
  rfl

theorem evalWordStackMachine_movesFromPhysical_singleton_preserves_value
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source : Nat) (destinationLocation : WordLocation)
    (hdestination :
      wordStackLocation config destination = some destinationLocation)
    (hdestinationScratch :
      destinationLocation ≠ .register config.scratch)
    (hdestinationAddressScratch :
      destinationLocation ≠ .register config.addressScratch)
    (hsourceScratch : WordLocation.register source ≠
      WordLocation.register config.scratch)
    (hsourceAddressScratch : WordLocation.register source ≠
      WordLocation.register config.addressScratch)
    (heval : (wordStackMovesFromPhysical config [destination] source).bind
      (evalWordStackMachine state) = some final) :
    wordStackLocationValue config final destinationLocation =
      wordStackLocationValue config state (.register source) := by
  rw [wordStackMovesFromPhysical_singleton config destination source
    destinationLocation hdestination] at heval
  exact evalWordStackMachine_parallelLocationMove_singleton_preserves_value
    config state final destinationLocation (.register source)
    hdestinationScratch hdestinationAddressScratch hsourceScratch
    hsourceAddressScratch heval

end Flapjack.RiscV
