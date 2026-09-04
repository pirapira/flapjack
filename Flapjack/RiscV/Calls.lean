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

structure WordCallContext (width : Nat) [NeZero width] where
  targets : List (Nat × Word width × List Nat × List Nat)

def lookupWordCallTarget [NeZero width] (label : Nat) :
    List (Nat × Word width × List Nat × List Nat) →
      Option (Word width × List Nat × List Nat)
  | [] => none
  | (candidate, entry, parameters, returns) :: targets =>
      if label == candidate then some (entry, parameters, returns)
      else lookupWordCallTarget label targets

def wordFunctionToRiscVWithCalls [NeZero width]
    (context : WordCallContext width) :
    WordProg (Word width) → Option (List (Instruction width) × List (Fin 32))
  | .skip => some ([], [])
  | .assign name value => do
      let instruction ← wordExpToInstruction name value
      pure ([instruction], [])
  | .inst (.arith operation) => do
      let instructions ← wordArithToInstructions operation
      pure (instructions, [])
  | .inst instruction => do
      let instruction ← wordInstToInstruction instruction
      pure ([instruction], [])
  | .store (.var address) value => do
      let value ← registerOfNat value
      let address ← registerOfNat address
      pure ([.storeWord value address], [])
  | .tick => pure ([.addi 0 0 0], [])
  | .call (some (destinations, _)) (some label) arguments none => do
      let (entry, parameters, returns) ← lookupWordCallTarget label context.targets
      let code ← wordCallToRiscV entry parameters returns arguments destinations
      pure (code, [])
  | .ite operator condition rightValue thenBranch elseBranch => do
      let condition ← registerOfNat condition
      let right ← match rightValue with
        | .reg right => registerOfNat right
        | .imm value => if value == 0 then pure 0 else none
      let (thenCode, thenReturns) ← wordFunctionToRiscVWithCalls context thenBranch
      let (elseCode, elseReturns) ← wordFunctionToRiscVWithCalls context elseBranch
      if thenReturns != elseReturns then none
      else
        let falseOffset : Word width := BitVec.ofNat width (8 + 4 * thenCode.length)
        let endOffset : Word width := BitVec.ofNat width (4 + 4 * elseCode.length)
        let branchFalse ← match operator with
          | .equal => pure (.branchNe condition right falseOffset)
          | .notEqual => pure (.branchEq condition right falseOffset)
          | .less => pure (.branchGe condition right falseOffset)
          | .notLess => pure (.branchLt condition right falseOffset)
          | .lower => pure (.branchGeU condition right falseOffset)
          | .notLower => pure (.branchLtU condition right falseOffset)
          | .test => pure (.branchNe condition 0 falseOffset)
          | .notTest => pure (.branchEq condition 0 falseOffset)
        let prelude := match operator with
          | .test | .notTest => [.and condition condition right]
          | _ => []
        pure (prelude ++ [branchFalse] ++ thenCode ++
          [.branchEq 0 0 endOffset] ++ elseCode, thenReturns)
  | .seq first second => do
      let (firstCode, firstReturns) ← wordFunctionToRiscVWithCalls context first
      if !firstReturns.isEmpty then
        pure (firstCode, firstReturns)
      else
        let (secondCode, secondReturns) ← wordFunctionToRiscVWithCalls context second
        pure (firstCode ++ secondCode, secondReturns)
  | .return _ values => do
      let values ← values.mapM registerOfNat
      pure ([], values)
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem wordCallToRiscV_shape [NeZero width]
    (entry : Word width) :
    wordCallToRiscV entry [2] [10] [6] [4] =
      some [.addi 2 6 0, .addi 31 0 entry, .jalr 1 31 0, .addi 4 10 0] := by
  simp [wordCallToRiscV, wordRegisterMoves, registerOfNat]

theorem wordFunctionToRiscVWithCalls_shape [NeZero width] :
    wordFunctionToRiscVWithCalls
      { targets := [(7, BitVec.ofNat width 32, [2], [10])] }
      (.seq
        (.call (some ([4], [])) (some 7) [6] none)
        (.return 0 [4])) =
      some ([.addi 2 6 0, .addi 31 0 (BitVec.ofNat width 32),
        .jalr 1 31 0, .addi 4 10 0], [4]) := by
  simp [wordFunctionToRiscVWithCalls, wordCallToRiscV,
    wordRegisterMoves, lookupWordCallTarget, registerOfNat]

theorem wordFunctionToRiscVWithCalls_addCarry [NeZero width] :
    wordFunctionToRiscVWithCalls
      ({ targets := [] } : WordCallContext width)
      ((.inst (.arith (.addCarry 5 6 2 3 4))) : WordProg (Word width)) =
      some ([.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31], []) := by
  simp [wordFunctionToRiscVWithCalls, wordArithToInstructions, registerOfNat]

end Flapjack.RiscV
