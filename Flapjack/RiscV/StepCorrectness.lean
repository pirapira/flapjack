import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.Ffi

/-!
# RISC-V step-count contracts

The source-side stepped Pancake evaluator records a source-step count, while
the executable RISC-V model consumes one instruction per recursive call.  This
module makes the machine-side count explicit first.  The resulting equations
are deliberately independent of a particular instruction-selection strategy:
they can be composed with the source-to-Word and Word-to-Stack contracts once
those passes expose their cost relation.
-/

namespace Flapjack.RiscV

/-! Count ordinary RISC-V instruction execution.  The state component is the
    same as `executeInstructions`; the second component is the exact number of
    instructions traversed. -/
def executeInstructionsCounted [NeZero width] :
    State width → List (Instruction width) → State width × Nat
  | state, [] => (state, 0)
  | state, instruction :: instructions =>
      let (final, count) := executeInstructionsCounted
        (execute state instruction) instructions
      (final, count + 1)

theorem executeInstructionsCounted_spec [NeZero width]
    (state : State width) (instructions : List (Instruction width)) :
    executeInstructionsCounted state instructions =
      (executeInstructions state instructions, instructions.length) := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction instructions ih =>
      simp only [executeInstructionsCounted, executeInstructions, List.length_cons]
      rw [ih]

/-! The FFI-aware machine evaluator has the same exact count on successful
    execution.  Failed host transitions remain failures, but do not alter the
    count of a successful prefix. -/
def executeInstructionsWithFfiCounted [NeZero width]
    (host : WordFfiHost width) :
    State width → List (Instruction width) → Option (State width × Nat)
  | state, [] => some (state, 0)
  | state, instruction :: instructions => do
      let state ← executeWithFfi host state instruction
      let (final, count) ← executeInstructionsWithFfiCounted host state instructions
      pure (final, count + 1)

theorem executeInstructionsWithFfiCounted_spec [NeZero width]
    (host : WordFfiHost width) (state : State width)
    (instructions : List (Instruction width)) :
    executeInstructionsWithFfiCounted host state instructions =
      (executeInstructionsWithFfi host state instructions).map
        (fun final => (final, instructions.length)) := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction instructions ih =>
      cases hstep : executeWithFfi host state instruction with
      | none =>
          simp [executeInstructionsWithFfiCounted, executeInstructionsWithFfi,
            hstep]
      | some nextState =>
          simp [executeInstructionsWithFfiCounted, executeInstructionsWithFfi,
            hstep, ih]
          cases hrest : executeInstructionsWithFfi host nextState instructions with
          | none => simp
          | some final =>
              cases final with
              | mk finalState => simp

/-! First source-to-machine step relation.  On the straight-line Word
    fragment, successful instruction selection preserves the ordinary Word
    result and the machine executes exactly one step per emitted instruction.
    The theorem is intentionally phrased with the compiler witness exposed so
    later cost theorems can replace `code.length` by their source-step bound. -/
theorem wordProgToRiscV_counted_sound_of_straightLine [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordProgToRiscV program = some code) :
    some (executeInstructionsCounted state code) =
      (evalWordProg state program).map
        (fun final => (final, code.length)) := by
  have hsem := wordProgToRiscV_sound_of_straightLine state program hstraight
    code hcompile
  rw [executeInstructionsCounted_spec]
  rw [hsem]
  rfl

end Flapjack.RiscV
