import Flapjack.RiscV.CorrectnessColour
import Flapjack.RiscV.StepCorrectness

/-!
# Counted full-SSA return simulation

The allocator/coloring correctness theorem exposes the final machine state as
executeInstructions target code. The step-preserving development also needs
the exact number of instructions consumed by that same artifact. This module
keeps the allocator witness and the return-value simulation visible, then adds
the counted execution equation without unfolding the allocator.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordAllocateGraphFunctionWithEntry_riscv_return_counted_simulation
    [NeZero width]
    (context : WordCallContext width)
    (parameters : List Nat) (program : WordProg (Word width))
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (coloured : WordProg (Word width))
    (halloc : wordAllocateGraphFunctionWithEntry parameters program fixedSources
      colours stackStart =
      some (state, renamedParameters, allocation, coloured))
    (valid : wordColourValid (wordGraphColouringAt allocation.colouring))
    (injective : Function.Injective
      (wordGraphColouringAt allocation.colouring))
    (colourZero : wordGraphColouringAt allocation.colouring 0 = 0)
    (colourNoScratch : ∀ name, name < 31 →
      wordGraphColouringAt allocation.colouring name ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation
      (wordGraphColouringAt allocation.colouring) source target)
    (hprogram : WordVarStraightLine width
      (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    (store : Nat) (values : List Nat)
    (hvalues : ∀ name, name ∈ values → name < 32)
    (code : List (Instruction width))
    (returns : List (Fin 32))
    (hcompile : wordFunctionToRiscVWithCalls context coloured =
      some (code, []))
    (hreturnCompile : wordFunctionToRiscVWithCalls context
      ((.return store (values.map
        (wordGraphColouringAt allocation.colouring))) : WordProg (Word width)) =
      some ([], returns)) :
    ∃ source' returnedValues target',
      evalWordFunction source
          (.seq (wordSsaRenameFunctionWithEntry parameters program).2.snd
            (.return store values)) =
        some (source', returnedValues) ∧
      evalWordFunction target
          (.seq coloured (.return store
            (values.map (wordGraphColouringAt allocation.colouring)))) =
        some (target', returnedValues) ∧
      executeInstructionsCounted target code = (target', code.length) ∧
      WordColourStateRelation (wordGraphColouringAt allocation.colouring)
        source' target' := by
  rcases wordAllocateGraphFunctionWithEntry_riscv_return_simulation
      context parameters program fixedSources colours stackStart state
      renamedParameters allocation coloured halloc valid injective colourZero
      colourNoScratch source target hrelation hprogram store values hvalues code
      returns hcompile hreturnCompile with
    ⟨source', returnedValues, hsource, htarget, hrelation'⟩
  refine ⟨source', returnedValues, executeInstructions target code,
    hsource, htarget, ?_, hrelation'⟩
  exact executeInstructionsCounted_spec target code

end Flapjack.RiscV
