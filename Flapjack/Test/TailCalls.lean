import Flapjack.RiscV.WordToStack

namespace Flapjack

open RiscV

def tailCallTestConfig : WordStackConfig :=
  { locations := [(6, .register 1)]
    scratch := 31
    stackBase := 0
    abiBase := 1 }

theorem tailCallArgumentMoves :
    wordStackMovesToPhysical tailCallTestConfig [6] tailCallTestConfig.abiBase =
      some (.skip : StackProg Nat) := by
  have hdest :
      wordStackLocationMoveDestinations
          [(WordLocation.register 1, WordLocation.register 1)] =
        [WordLocation.register 1] := by
    rfl
  have hnodup : ([WordLocation.register 1] : List WordLocation).Nodup := by
    decide
  have hremove :
      wordStackLocationMoveRemoveDestination (WordLocation.register 1)
          [(WordLocation.register 1, WordLocation.register 1)] = [] := by
    decide
  have hreserved :
      ([(WordLocation.register 1, WordLocation.register 1)]).any
          (fun move =>
            move.1 = WordLocation.register 31 ||
              move.1 = WordLocation.register 29 ||
              move.2 = WordLocation.register 31 ||
              move.2 = WordLocation.register 29) = false := by
    decide
  have hready :
      (wordStackLocationMoveReady [WordLocation.register 1]
        [(WordLocation.register 1, WordLocation.register 1)]).isNone = false := by
    simp [wordStackLocationMoveReady]
  have hmoves :
      wordStackPhysicalMovesTo tailCallTestConfig [6]
          tailCallTestConfig.abiBase =
        some [(WordLocation.register 1, WordLocation.register 1)] := by
    simp [wordStackPhysicalMovesTo, wordStackPhysicalMovesToIndexed,
      tailCallTestConfig, wordStackLocation, lookupNatInfo]
  rw [wordStackMovesToPhysical, hmoves]
  simp [tailCallTestConfig, hnodup, wordStackLocationMove,
    wordStackLocationMoveReady, wordStackLocationMoveRemoveDestination,
    wordStackLocationMoveDestinations, wordStackParallelLocationMove,
    wordStackParallelLocationMoveAux, wordStackJoin, List.any_nil,
    List.any_cons, List.filter_nil]

theorem tailCallFreeCountZero :
    wordStackCallFreeCount tailCallTestConfig 1 = 0 := by
  simp [wordStackCallFreeCount, wordStackCakeFrameSize, tailCallTestConfig]

example :
    wordToStackProg tailCallTestConfig
        (.call none (some 7) [6] none : WordProg Nat) =
      some (.call none (.label 7) none) := by
  simp [wordToStackProg, tailCallArgumentMoves, wordStackJoin,
    tailCallFreeCountZero, stackFreeIfNonzero]

example :
    wordToStackProgNat tailCallTestConfig
        (.call none (some 7) [6] none : WordProg Nat) =
      some (.call none (.label 7) none) := by
  simp [wordToStackProgNat, tailCallArgumentMoves, wordStackJoin,
    tailCallFreeCountZero, stackFreeIfNonzero]

end Flapjack
