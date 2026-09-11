import Flapjack.RiscV.CorrectnessColour
import Flapjack.RiscV.CorrectnessConditional

/-!
# Conditional colouring at the branch-aware RISC-V boundary

Straight-line colouring relates registers by a colouring function, while the
conditional layout deliberately omits the PC from its body relation: the
source body starts at the caller PC and the linked machine body starts after
the conditional branch.  This file connects those two contracts without
requiring the coloured register function to equal the source register
function.
-/

namespace Flapjack.RiscV

structure WordColourDataRelation (colour : Nat → Nat) [NeZero width]
    (source target : State width) : Prop where
  memory : source.memory = target.memory
  privilege : source.privilege = target.privilege
  mode : source.mode = target.mode
  register : ∀ (name : Nat) (hname : name < 32)
      (hcolour : colour name < 32),
    readRegister source ⟨name, hname⟩ =
      readRegister target ⟨colour name, hcolour⟩

theorem WordColourStateRelation.toData
    (colour : Nat → Nat) [NeZero width]
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target) :
    WordColourDataRelation colour source target := by
  constructor
  · exact hrelation.memory
  · exact hrelation.privilege
  · exact hrelation.mode
  · exact hrelation.register

theorem wordColourDataRelation_execute_branchEq_zero [NeZero width]
    (colour : Nat → Nat) (source target : State width)
    (offset : Word width)
    (hrelation : WordColourDataRelation colour source target) :
    WordColourDataRelation colour source (execute target (.branchEq 0 0 offset)) := by
  constructor
  · simpa [execute] using hrelation.memory
  · simpa [execute] using hrelation.privilege
  · simpa [execute] using hrelation.mode
  · intro name hname hcolour
    simpa [execute, readRegister] using hrelation.register name hname hcolour

/-! Source/machine conditional simulation specialized to the coloured data
    relation.  The branch runner itself is shared with the uncoloured
    conditional correctness development. -/

theorem evalWordFunction_ite_executeCodeUntil_of_coloured_data_relation
    [NeZero width]
    (colour : Nat → Nat)
    (state : State width) (operator : Cmp) (condition source : Nat)
    (thenBranch elseBranch : WordProg (Word width))
    (branchLeft right : Fin 32)
    (thenCode elseCode : List (Instruction width))
    (returns : List (Word width))
    (hpc : state.pc = 0)
    (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition
        (.reg source : WordRegImm (Word width)) =
      some (branchLeft, right, []))
    (hthen : ∃ thenState,
      evalWordFunction state thenBranch = some (thenState, returns) ∧
      WordColourDataRelation colour thenState
        (executeInstructions
          (execute state (riscVBranchFalseInstruction operator branchLeft right
            (BitVec.ofNat width (8 + 4 * thenCode.length)))) thenCode))
    (helse : ∃ elseState,
      evalWordFunction state elseBranch = some (elseState, returns) ∧
      WordColourDataRelation colour elseState
        (executeInstructions
          (execute state (riscVBranchFalseInstruction operator branchLeft right
            (BitVec.ofNat width (8 + 4 * thenCode.length)))) elseCode))
    (hthenNonbranching : ∀ instruction ∈ thenCode, instruction.isBranch = false)
    (helseNonbranching : ∀ instruction ∈ elseCode, instruction.isBranch = false)
    (hbound : (thenCode.length + elseCode.length + 2) * 4 < 2 ^ width) :
    ∃ sourceState machineState,
      evalWordFunction state
          (.ite operator condition (.reg source) thenBranch elseBranch) =
        some (sourceState, returns) ∧
      executeCodeUntil (thenCode.length + elseCode.length + 3) 0
          (BitVec.ofNat width ((thenCode.length + elseCode.length + 2) * 4))
          (riscVBranchFalseInstruction operator branchLeft right
              (BitVec.ofNat width (8 + 4 * thenCode.length)) ::
            thenCode ++
            [.branchEq 0 0 (BitVec.ofNat width (4 + 4 * elseCode.length))] ++
            elseCode) state = some machineState ∧
      WordColourDataRelation colour sourceState machineState := by
  rcases hthen with ⟨thenState, hthenEval, hthenRelation⟩
  rcases helse with ⟨elseState, helseEval, helseRelation⟩
  have hcondition := wordConditionOperands_register_sound state operator condition source
    hzero branchLeft right [] hoperands
  have hcondition' :
      evalWordCondition state operator condition (.reg source) =
        riscVCondition state operator branchLeft right := by
    simpa [executeInstructions] using hcondition
  have hrun := executeCodeUntil_conditional_of_nonbranching state operator branchLeft right
    thenCode elseCode hpc hthenNonbranching helseNonbranching hbound
  by_cases hchoose : riscVCondition state operator branchLeft right
  · have hsourceChoose :
        evalWordCondition state operator condition (.reg source) = some true := by
      rw [hcondition']
      simp [hchoose]
    have hsourceEval :
        evalWordFunction state
            (.ite operator condition (.reg source) thenBranch elseBranch) =
          some (thenState, returns) := by
      simp only [evalWordFunction, hsourceChoose]
      exact hthenEval
    rw [if_pos hchoose] at hrun
    let machineThen := executeInstructions
      (execute state (riscVBranchFalseInstruction operator branchLeft right
        (BitVec.ofNat width (8 + 4 * thenCode.length)))) thenCode
    let jump : Instruction width :=
      .branchEq 0 0 (BitVec.ofNat width (4 + 4 * elseCode.length))
    have hjumpData := wordColourDataRelation_execute_branchEq_zero
      colour thenState machineThen
      (BitVec.ofNat width (4 + 4 * elseCode.length))
      hthenRelation
    refine ⟨thenState, execute machineThen jump, hsourceEval, ?_, hjumpData⟩
    simpa [machineThen, jump, List.cons_append, List.append_assoc] using hrun
  · have hsourceChoose :
        evalWordCondition state operator condition (.reg source) = some false := by
      rw [hcondition']
      simp [hchoose]
    have hsourceEval :
        evalWordFunction state
            (.ite operator condition (.reg source) thenBranch elseBranch) =
          some (elseState, returns) := by
      simp only [evalWordFunction, hsourceChoose]
      exact helseEval
    rw [if_neg hchoose] at hrun
    refine ⟨elseState,
      executeInstructions
        (execute state (riscVBranchFalseInstruction operator branchLeft right
          (BitVec.ofNat width (8 + 4 * thenCode.length)))) elseCode,
      hsourceEval, ?_, helseRelation⟩
    simpa [List.cons_append, List.append_assoc] using hrun

end Flapjack.RiscV
