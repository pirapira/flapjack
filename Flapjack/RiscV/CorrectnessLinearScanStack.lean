import Flapjack.RiscV.LinearScanPipeline
import Flapjack.RiscV.CorrectnessStackFunctionEntry

/-!
# Linear-scan allocator-to-StackLang contract

The linear-scan allocator is a complete allocation mode of CakeML's Word
backend, but previously its pipeline stopped at an executable
`wordToStackFunctionWithParameters` call.  This file exposes the same
allocator/entry/body boundary already available for the spill allocator:
successful allocation and lowering retain the renamed program, the location
map, and the generated StackLang program, while the proof interface exposes
the allocator safety and parameter-coverage facts needed by later target
proofs.
-/

namespace Flapjack.RiscV

open Flapjack

def wordAllocateLinearScanFunctionWithEntryToStack [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width)) (colours stackStart : Nat) :
    Option (WordSsaState × List Nat × WordLinearScanState ×
      WordProg (Word width) × StackProg Nat) := do
  let (ssaState, renamedParameters, allocation, renamedProgram) ←
    wordAllocateLinearScanFunctionWithEntry parameters program colours stackStart
  let stackProgram ← wordToStackFunctionWithParameters
    { config with locations := wordLinearScanLocations allocation }
    renamedParameters renamedProgram
  pure (ssaState, renamedParameters, allocation, renamedProgram, stackProgram)

theorem wordAllocateLinearScanFunctionWithEntryToStack_stack_result
    [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width)) (colours stackStart : Nat)
    (ssaState : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordLinearScanState)
    (renamedProgram : WordProg (Word width)) (stackProgram : StackProg Nat)
    (hbridge : wordAllocateLinearScanFunctionWithEntryToStack config parameters
      program colours stackStart =
      some (ssaState, renamedParameters, allocation, renamedProgram,
        stackProgram)) :
    wordToStackFunctionWithParameters
      { config with locations := wordLinearScanLocations allocation }
      renamedParameters renamedProgram = some stackProgram := by
  simp only [wordAllocateLinearScanFunctionWithEntryToStack] at hbridge
  cases halloc : wordAllocateLinearScanFunctionWithEntry parameters program
      colours stackStart with
  | none => simp [halloc] at hbridge
  | some allocationResult =>
      cases allocationResult with
      | mk allocationState allocationRest =>
          cases allocationRest with
          | mk allocationParameters allocationRest =>
              cases allocationRest with
              | mk allocation' allocationProgram =>
                  cases hstack : wordToStackFunctionWithParameters
                      { config with locations := wordLinearScanLocations allocation' }
                      allocationParameters allocationProgram with
                  | none => simp [halloc, hstack] at hbridge
                  | some generatedProgram =>
                      have hresult :
                          allocationState = ssaState ∧
                          allocationParameters = renamedParameters ∧
                          allocation' = allocation ∧
                          allocationProgram = renamedProgram ∧
                          generatedProgram = stackProgram := by
                        simpa [halloc, hstack] using hbridge
                      rcases hresult with
                        ⟨rfl, rfl, rfl, rfl, rfl⟩
                      exact hstack

theorem wordAllocateLinearScanFunctionWithEntryToStack_contract
    [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width)) (colours stackStart : Nat)
    (ssaState : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordLinearScanState)
    (renamedProgram : WordProg (Word width)) (stackProgram : StackProg Nat)
    (body moves : StackProg Nat)
    (machineState middle final : WordStackMachineState width)
    (hbridge : wordAllocateLinearScanFunctionWithEntryToStack config parameters
      program colours stackStart =
      some (ssaState, renamedParameters, allocation, renamedProgram,
        stackProgram))
    (hbody : wordToStackProgWord
      { config with locations := wordLinearScanLocations allocation }
      renamedProgram = some body)
    (hmoves : wordStackMovesFromPhysical
      { config with locations := wordLinearScanLocations allocation }
      renamedParameters 2 = some moves)
    (hentry : evalWordStackMachine machineState moves = some middle)
    (hbodyEval : evalWordStackMachine middle body = some final) :
    wordLinearScanAllocationSafe
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        (wordProgForcedClashes
          (wordSsaRenameFunctionWithEntry parameters program).2.snd)
        allocation = true ∧
      (∀ name, name ∈ renamedParameters →
        ∃ location, lookupNatInfo name allocation.locations = some location) ∧
      wordToStackProgWord
        { config with locations := wordLinearScanLocations allocation }
        renamedProgram = some body ∧
      wordStackMovesFromPhysical
        { config with locations := wordLinearScanLocations allocation }
        renamedParameters 2 = some moves ∧
      stackProgram = wordStackJoin moves body ∧
      evalWordStackMachine machineState stackProgram = some final := by
  have hsafe := wordAllocateLinearScanFunctionWithEntry_safe
    parameters program colours stackStart ssaState renamedParameters allocation
    renamedProgram (by
      simp only [wordAllocateLinearScanFunctionWithEntryToStack] at hbridge
      cases halloc : wordAllocateLinearScanFunctionWithEntry parameters program
          colours stackStart with
      | none => simp [halloc] at hbridge
      | some allocationResult =>
          cases allocationResult with
          | mk allocationState allocationRest =>
              cases allocationRest with
              | mk allocationParameters allocationRest =>
                  cases allocationRest with
                  | mk allocation' allocationProgram =>
                      cases hstack : wordToStackFunctionWithParameters
                          { config with locations := wordLinearScanLocations allocation' }
                          allocationParameters allocationProgram with
                      | none => simp [halloc, hstack] at hbridge
                      | some generatedProgram =>
                          have hresult :
                              allocationState = ssaState ∧
                              allocationParameters = renamedParameters ∧
                              allocation' = allocation ∧
                              allocationProgram = renamedProgram ∧
                              generatedProgram = stackProgram := by
                            simpa [halloc, hstack] using hbridge
                          rcases hresult with
                            ⟨hstate, hparameters, hallocation, hprogram, _⟩
                          simp [hstate, hparameters, hallocation, hprogram])
  have hparams := wordAllocateLinearScanFunctionWithEntry_maps_parameters
    parameters program colours stackStart ssaState renamedParameters allocation
    renamedProgram (by
      simp only [wordAllocateLinearScanFunctionWithEntryToStack] at hbridge
      cases halloc : wordAllocateLinearScanFunctionWithEntry parameters program
          colours stackStart with
      | none => simp [halloc] at hbridge
      | some allocationResult =>
          cases allocationResult with
          | mk allocationState allocationRest =>
              cases allocationRest with
              | mk allocationParameters allocationRest =>
                  cases allocationRest with
                  | mk allocation' allocationProgram =>
                      cases hstack : wordToStackFunctionWithParameters
                          { config with locations := wordLinearScanLocations allocation' }
                          allocationParameters allocationProgram with
                      | none => simp [halloc, hstack] at hbridge
                      | some generatedProgram =>
                          have hresult :
                              allocationState = ssaState ∧
                              allocationParameters = renamedParameters ∧
                              allocation' = allocation ∧
                              allocationProgram = renamedProgram ∧
                              generatedProgram = stackProgram := by
                            simpa [halloc, hstack] using hbridge
                          rcases hresult with
                            ⟨hstate, hparameters, hallocation, hprogram, _⟩
                          simp [hstate, hparameters, hallocation, hprogram])
  have hstack := wordAllocateLinearScanFunctionWithEntryToStack_stack_result
    config parameters program colours stackStart ssaState renamedParameters
    allocation renamedProgram stackProgram hbridge
  have hjoin : stackProgram = wordStackJoin moves body := by
    simp [wordToStackFunctionWithParameters, hbody, hmoves] at hstack
    exact hstack.symm
  have heval := evalWordStackMachine_wordStackJoin machineState middle final
    moves body hentry hbodyEval
  exact ⟨hsafe, hparams, hbody, hmoves, hjoin, by simpa [hjoin] using heval⟩

end Flapjack.RiscV
