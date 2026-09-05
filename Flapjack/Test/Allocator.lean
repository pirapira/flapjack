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
