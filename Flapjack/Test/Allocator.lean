import Flapjack.Pipeline

namespace Flapjack

example :
    wordAllocateContext [0, 1, 29, 30] =
      some { vars := [(0, 2), (1, 3), (29, 4), (30, 5)] } := by
  exact wordAllocateContext_examples

example :
    wordAllocateContext [0, 1, 2, 3] =
      some { vars := [(0, 2), (1, 3), (2, 4), (3, 5)] } := by
  exact wordAllocateContext_preserves_small_names

example :
    wordAllocateContextWithClashes [0, 1, 28]
        [(0, 1), (1, 28)] =
      some { vars := [(28, 2), (1, 3), (0, 2)] } := by
  exact wordAllocateContextWithClashes_examples

example :
    wordAllocateVarsWithClashes [0, 1] [(0, 1)] =
      some [(1, 3), (0, 2)] := by
  exact wordAllocateVarsWithClashes_safe_example

example :
    wordInstVars (.arith (.addCarry 1 2 3 4 5)) = [3, 4, 5, 1, 2] := by
  exact wordInstVars_addCarry

example :
    wordAllocateLinearInstructions
      [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      some { vars := [(6, 8), (5, 7), (1, 3), (0, 2), (4, 6), (3, 5), (2, 4)] } := by
  exact wordAllocateLinearInstructions_example

example :
    wordSsaRenameLinear
        { current := [(2, 100), (3, 101), (4, 102)], next := 200 }
        [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      ({ current := [(6, 203), (5, 202), (1, 201), (0, 200),
          (2, 100), (3, 101), (4, 102)], next := 204 },
        [.arith (.addCarry 200 201 100 101 102),
          .arith (.addCarry 202 203 200 201 100)]) := by
  exact wordSsaRenameLinear_addCarry

example (slots : List Nat) (edges : List (Nat × Nat))
    (colouring : NatInfoMap Nat)
    (hcolouring : wordAllocateVarsWithClashes slots edges = some colouring) :
    wordColouringUsesAllocatable slots.eraseDups colouring = true ∧
      wordColouringRespectsClashes edges colouring = true := by
  exact wordAllocateVarsWithClashes_sound slots edges colouring hcolouring

example [OfNat α 1] :
    pipelineWordFunctionsAllocated
      ([] : List (Nat × List Nat × LoopProg α)) = some [] := by
  rfl

end Flapjack
