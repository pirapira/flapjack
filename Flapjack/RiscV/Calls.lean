import Flapjack.RiscV.Backend

/-!
RISC-V call-sequence selection for the first Flapjack calling convention.

The convention keeps Word parameter and return registers explicit. `x31` is
reserved as the scratch register for materializing a callee entry address,
`x1` is the link register, and `JALR x0, x1, 0` is the callee return. A later
linker will resolve function labels to entry addresses and validate the
reserved-register condition.
-/

namespace Flapjack.RiscV

def wordRegisterMoves [NeZero width] : List (Nat × Nat) →
    Option (List (Instruction width))
  | [] => some []
  | (destination, source) :: moves => do
      let destination ← registerOfNat destination
      let source ← registerOfNat source
      let moves ← wordRegisterMoves moves
      pure (.addi destination source 0 :: moves)

def wordCallToRiscV [NeZero width]
    (entry : Word width) (parameters : List Nat) (returns : List Nat)
    (arguments : List Nat) (destinations : List Nat) :
    Option (List (Instruction width)) := do
  if parameters.length != arguments.length || returns.length != destinations.length then
    none
  else
    let parameterMoves ← wordRegisterMoves (parameters.zip arguments)
    let resultMoves ← wordRegisterMoves (destinations.zip returns)
    pure (parameterMoves ++ [.addi 31 0 entry, .jalr 1 31 0] ++ resultMoves)

theorem wordCallToRiscV_shape [NeZero width]
    (entry : Word width) :
    wordCallToRiscV entry [2] [10] [6] [4] =
      some [.addi 2 6 0, .addi 31 0 entry, .jalr 1 31 0, .addi 4 10 0] := by
  simp [wordCallToRiscV, wordRegisterMoves, registerOfNat]

end Flapjack.RiscV
