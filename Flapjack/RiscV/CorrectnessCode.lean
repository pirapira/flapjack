import Flapjack.RiscV.CorrectnessCondition
import Flapjack.RiscV.Lab

/-!
Machine-level control-flow contracts for the branch instructions emitted by
the Word conditional lowering.

The lowering branches to the `else` block when the source condition is false.
This file records that choice independently of code layout; the later
`executeCode` theorem can then use it together with the offset calculation.
-/

namespace Flapjack.RiscV

def riscVBranchFalseInstruction [NeZero width] (operator : Cmp)
    (left right : Fin 32) (offset : Word width) : Instruction width :=
  match operator with
  | .equal => .branchNe left right offset
  | .notEqual => .branchEq left right offset
  | .less => .branchGe left right offset
  | .notLess => .branchLt left right offset
  | .lower => .branchGeU left right offset
  | .notLower => .branchLtU left right offset
  | .test => .branchNe left right offset
  | .notTest => .branchEq left right offset

theorem execute_riscVBranchFalse_pc [NeZero width] (state : State width)
    (operator : Cmp) (left right : Fin 32) (offset : Word width) :
    (execute state (riscVBranchFalseInstruction operator left right offset)).pc =
      if riscVCondition state operator left right then
        nextPc state
      else
        state.pc + offset := by
  cases operator <;>
    simp [riscVBranchFalseInstruction, riscVCondition, execute, nextPc]
  · rfl
  · by_cases h : readRegister state left < readRegister state right
    · have h' : ¬ readRegister state right ≤ readRegister state left :=
        (BitVec.not_le).mpr h
      simp [h, h']
    · have h' : readRegister state right ≤ readRegister state left :=
        (BitVec.not_lt).mp h
      simp [h]
  · by_cases h : signedLess (readRegister state left) (readRegister state right) = true
    · simp [h]
    · have h' : signedLess (readRegister state left) (readRegister state right) = false :=
        eq_false_of_ne_true h
      simp [h]

theorem execute_riscVBranchFalse_pc_of_condition [NeZero width]
    (state : State width) (operator : Cmp) (condition source : Nat)
    (branchLeft right : Fin 32) (prelude : List (Instruction width))
    (offset : Word width) (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition (.reg source) =
      some (branchLeft, right, prelude)) :
    (execute (executeInstructions state prelude)
      (riscVBranchFalseInstruction operator branchLeft right offset)).pc =
        if evalWordCondition state operator condition (.reg source) = some true then
          nextPc (executeInstructions state prelude)
        else
          (executeInstructions state prelude).pc + offset := by
  rw [execute_riscVBranchFalse_pc]
  have hcondition := wordConditionOperands_register_sound state operator condition source hzero
    branchLeft right prelude hoperands
  rw [hcondition]
  simp

/-! Symbolic locations are resolved by LabLang before target-code execution.
    This theorem records the corresponding machine boundary: once the section
    and local label resolve to an absolute instruction position, `locValue`
    materializes that position in the requested register. -/

theorem labCompileAsm_locValue_execute [NeZero width]
    (context : WordFfiContext)
    (state : State width) (sectionId : Nat) (labels : List (Nat × Nat))
    (position destination : Nat) (target : LabRef) (register : Fin 32)
    (targetPosition : Nat)
    (hregister : registerOfNat destination = some register)
    (htarget : labResolveRef sectionId labels target = some targetPosition) :
    (labCompileAsm context sectionId labels position
      (.locValue destination target)).bind
        (fun code => executeInstructions state code) =
      some (execute state
        (.addi register 0 (BitVec.ofNat width targetPosition))) := by
  simp [labCompileAsm, hregister, htarget, executeInstructions]

theorem labCompileAsm_linkValue_execute [NeZero width]
    (context : WordFfiContext)
    (state : State width) (sectionId : Nat) (labels : List (Nat × Nat))
    (position : Nat) (target : LabRef) (targetPosition : Nat)
    (htarget : labResolveRef sectionId labels target = some targetPosition) :
    (labCompileAsm context sectionId labels position
      (.linkValue target)).bind
        (fun code => executeInstructions state code) =
      some (execute state
        (.addi 1 0 (BitVec.ofNat width targetPosition))) := by
  simp [labCompileAsm, htarget, executeInstructions]

/-! A cross-section jump is not merely assembled correctly: its resolved
    offset must take the machine to the target section.  This is the smallest
    executable contract for the label collection and flattening boundary. -/

theorem compileLabProgram_cross_section_jump_execute :
    (compileLabProgram (width := 64) { services := [] }
      [⟨1, [.labAsm (.jump ⟨2, 0⟩) [] 0]⟩,
       ⟨2, [.label 2 0 0, .asm (.const 1 7) [] 0]⟩]).bind
        (fun code =>
          (executeCodeUntil 10 (0 : Word 64) (BitVec.ofNat 64 8) code
            (zeroState 64)).map (fun state => readRegister state 1)) =
      some (BitVec.ofNat 64 7) := by
  decide

/-! Compose continuation materialization, a cross-section call jump, the
    callee return instruction, and the caller continuation into one executable
    trace.  The final jump skips the already-returned callee section and gives
    the runner a concrete return PC. -/

theorem compileLabProgram_call_return_execute :
    (compileLabProgram (width := 64) { services := [] }
      [⟨1, [
          .labAsm (.linkValue ⟨1, 0⟩) [] 0,
          .labAsm (.jump ⟨2, 0⟩) [] 0,
          .label 1 0 0,
          .asm (.const 1 28) [] 0,
          .asm (.const 2 9) [] 0,
          .labAsm (.jump ⟨3, 0⟩) [] 0]⟩,
       ⟨2, [
          .label 2 0 0,
          .asm (.const 2 7) [] 0,
          .labAsm .return [] 0]⟩,
       ⟨3, [.label 3 0 0]⟩]).bind
        (fun code =>
          (executeCodeUntil 20 (0 : Word 64) (BitVec.ofNat 64 28) code
            (zeroState 64)).map (fun state => readRegister state 2)) =
      some (BitVec.ofNat 64 9) := by
  decide

end Flapjack.RiscV
