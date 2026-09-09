import Flapjack.RiscV.CorrectnessCode
import Flapjack.RiscV.StepCorrectness

/-!
Machine-level control-flow correctness for the smallest conditional layout
emitted by the Word backend.  The general lowering uses the same layout:
branch over the then block, execute an unconditional jump over the else block,
then stop at the first byte after the conditional.
-/

namespace Flapjack.RiscV

def advancesPc [NeZero width] (instruction : Instruction width) : Prop :=
  ∀ state : State width, (execute state instruction).pc = nextPc state

theorem executeCode_conditional_single
    [NeZero width] (state : State width) (operator : Cmp) (left right : Fin 32)
    (thenInstruction elseInstruction : Instruction width)
    (hpc : state.pc = 0)
    (hwidth : 5 ≤ width)
    (hthen : advancesPc thenInstruction)
    (helse : advancesPc elseInstruction) :
    executeCode 5 0
        [ riscVBranchFalseInstruction operator left right (BitVec.ofNat width 12)
        , thenInstruction
        , .branchEq 0 0 (BitVec.ofNat width 8)
        , elseInstruction ] state =
      if riscVCondition state operator left right then
        some (execute
          (execute
            (execute state
              (riscVBranchFalseInstruction operator left right (BitVec.ofNat width 12)))
            thenInstruction)
          (.branchEq 0 0 (BitVec.ofNat width 8)))
      else
        some (execute
          (execute state
            (riscVBranchFalseInstruction operator left right (BitVec.ofNat width 12)))
          elseInstruction) := by
  let branch := riscVBranchFalseInstruction operator left right (BitVec.ofNat width 12)
  let jump : Instruction width := .branchEq 0 0 (BitVec.ofNat width 8)
  have hbranch := execute_riscVBranchFalse_pc state operator left right
    (BitVec.ofNat width 12)
  have hpow : 2 ^ 5 ≤ 2 ^ width :=
    Nat.pow_le_pow_right (by decide) hwidth
  have hbound4 : 4 < 2 ^ width := by omega
  have hbound8 : 8 < 2 ^ width := by omega
  have hbound12 : 12 < 2 ^ width := by omega
  have hbound16 : 16 < 2 ^ width := by omega
  by_cases hcondition : riscVCondition state operator left right
  · have hbranchPc : (execute state branch).pc = 4 := by
      simpa [branch, hcondition, hpc, nextPc] using hbranch
    have hthenPc : (execute (execute state branch) thenInstruction).pc = 8 := by
      rw [hthen]
      simp only [nextPc, hbranchPc]
      change BitVec.ofNat width 4 + BitVec.ofNat width 4 = BitVec.ofNat width 8
      rw [show (8 : Nat) = 4 + 4 by omega, BitVec.ofNat_add]
    have hjumpPc :
        (execute (execute (execute state branch) thenInstruction) jump).pc = 16 := by
      change (execute (execute (execute state branch) thenInstruction)
        (.branchEq 0 0 (BitVec.ofNat width 8))).pc = 16
      rw [execute_branchEq_pc, hthenPc]
      simp
      change BitVec.ofNat width 8 + BitVec.ofNat width 8 = BitVec.ofNat width 16
      rw [show (16 : Nat) = 8 + 8 by omega, BitVec.ofNat_add]
    have hstep1 :
        executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state =
          executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) := by
      simp [executeCode, hpc]
    have hstep2 :
        executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) =
          executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) thenInstruction) := by
      simp [executeCode, hbranchPc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound4]
    have hstep3 :
        executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) thenInstruction) =
          executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute (execute state branch) thenInstruction) jump) := by
      simp [executeCode, hthenPc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound8]
    have hstep4 :
        executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute (execute state branch) thenInstruction) jump) =
          some (execute (execute (execute state branch) thenInstruction) jump) := by
      simp [executeCode, hjumpPc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound16]
    change executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state = _
    rw [hstep1, hstep2, hstep3, hstep4]
    simp [hcondition, branch, jump]
  · have hbranchPc : (execute state branch).pc = 12 := by
      simpa [branch, hcondition, hpc, nextPc] using hbranch
    have helsePc : (execute (execute state branch) elseInstruction).pc = 16 := by
      rw [helse]
      simp only [nextPc, hbranchPc]
      change BitVec.ofNat width 12 + BitVec.ofNat width 4 = BitVec.ofNat width 16
      rw [show (16 : Nat) = 12 + 4 by omega, BitVec.ofNat_add]
    have hstep1 :
        executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state =
          executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) := by
      simp [executeCode, hpc]
    have hstep2 :
        executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) =
          executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) := by
      simp [executeCode, hbranchPc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound12]
    have hstep3 :
        executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) =
          executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) := by
      simp [executeCode, helsePc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound16]
    change executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state = _
    rw [hstep1, hstep2, hstep3]
    have hend :
        executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) =
          some (execute (execute state branch) elseInstruction) := by
      simp [executeCode, helsePc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound16]
    rw [hend]
    simp [hcondition, branch]

theorem executeCodeUntil_conditional_of_nonbranching [NeZero width]
    (state : State width) (operator : Cmp) (left right : Fin 32)
    (thenCode elseCode : List (Instruction width))
    (hpc : state.pc = 0)
    (hzero : ∀ instruction ∈ thenCode, instruction.isBranch = false)
    (hone : ∀ instruction ∈ elseCode, instruction.isBranch = false)
    (hbound : (thenCode.length + elseCode.length + 2) * 4 < 2 ^ width) :
    executeCodeUntil (thenCode.length + elseCode.length + 3) 0
        (BitVec.ofNat width ((thenCode.length + elseCode.length + 2) * 4))
        (riscVBranchFalseInstruction operator left right
            (BitVec.ofNat width (8 + 4 * thenCode.length)) ::
          thenCode ++
          [.branchEq 0 0 (BitVec.ofNat width (4 + 4 * elseCode.length))] ++
          elseCode) state =
      if riscVCondition state operator left right then
        some (executeInstructions
          (executeInstructions
            (execute state (riscVBranchFalseInstruction operator left right
              (BitVec.ofNat width (8 + 4 * thenCode.length)))) thenCode)
          [.branchEq 0 0 (BitVec.ofNat width (4 + 4 * elseCode.length))])
      else
        some (executeInstructions
          (execute state (riscVBranchFalseInstruction operator left right
            (BitVec.ofNat width (8 + 4 * thenCode.length)))) elseCode) := by
  let branch := riscVBranchFalseInstruction operator left right
    (BitVec.ofNat width (8 + 4 * thenCode.length))
  let jump : Instruction width :=
    .branchEq 0 0 (BitVec.ofNat width (4 + 4 * elseCode.length))
  let code := branch :: thenCode ++ [jump] ++ elseCode
  let returnOffset := (thenCode.length + elseCode.length + 2) * 4
  have hreturnBound : returnOffset < 2 ^ width := by
    simpa [returnOffset] using hbound
  have hbranch := execute_riscVBranchFalse_pc state operator left right
    (BitVec.ofNat width (8 + 4 * thenCode.length))
  have hnotEnd : state.pc ≠ BitVec.ofNat width returnOffset := by
    intro heq
    rw [hpc] at heq
    have heqNat := congrArg BitVec.toNat heq
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hreturnBound] at heqNat
  have hbranchStep :
      executeCodeUntil (code.length + 1) 0 (BitVec.ofNat width returnOffset)
          code state =
        executeCodeUntil code.length 0 (BitVec.ofNat width returnOffset)
          code (execute state branch) := by
    rw [executeCodeUntil]
    rw [if_neg hnotEnd]
    simp [code, branch, hpc]
  by_cases hcondition : riscVCondition state operator left right
  · have hbranchPcTrue : (execute state branch).pc = 4 := by
      simpa [branch, hcondition, hpc, nextPc] using hbranch
    have hthenPc :
        (executeInstructions (execute state branch) thenCode).pc =
          BitVec.ofNat width ((1 + thenCode.length) * 4) := by
      have hpc' := executeInstructions_pc_of_nonbranching
        (execute state branch) thenCode hzero
      calc
        (executeInstructions (execute state branch) thenCode).pc =
            (execute state branch).pc + BitVec.ofNat width (thenCode.length * 4) := hpc'
        _ = BitVec.ofNat width 4 + BitVec.ofNat width (thenCode.length * 4) := by
          simpa using congrArg (fun pc => pc + BitVec.ofNat width (thenCode.length * 4))
            hbranchPcTrue
        _ = BitVec.ofNat width (4 + thenCode.length * 4) := by
          rw [← BitVec.ofNat_add]
        _ = BitVec.ofNat width ((1 + thenCode.length) * 4) := by
          congr 1
          omega
    have hthenBeforeEnd :
        (1 + thenCode.length) * 4 < returnOffset := by
      simp [returnOffset]
      omega
    have hthenFactor := executeCodeUntil_after_nonbranching
      (execute state branch) [branch] thenCode (jump :: elseCode)
      (elseCode.length + 2) returnOffset
      (by simpa using hbranchPcTrue) hzero hthenBeforeEnd hreturnBound
    have hjumpPc :
        (execute (executeInstructions (execute state branch) thenCode) jump).pc =
          BitVec.ofNat width returnOffset := by
      rw [execute_branchEq_pc, hthenPc]
      simp
      change BitVec.ofNat width ((1 + thenCode.length) * 4) +
        BitVec.ofNat width (4 + 4 * elseCode.length) =
          BitVec.ofNat width returnOffset
      rw [← BitVec.ofNat_add]
      congr 1
      simp [returnOffset]
      omega
    have hjumpRun :
        executeCodeUntil (elseCode.length + 2) 0
            (BitVec.ofNat width returnOffset) code
            (executeInstructions (execute state branch) thenCode) =
          some (execute (executeInstructions (execute state branch) thenCode) jump) := by
      have hthenBound : (1 + thenCode.length) * 4 < 2 ^ width := by omega
      have hnotReturn :
          (executeInstructions (execute state branch) thenCode).pc ≠
            BitVec.ofNat width returnOffset := by
        intro heq
        rw [hthenPc] at heq
        have heqNat := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hthenBound,
          Nat.mod_eq_of_lt hreturnBound] at heqNat
        omega
      rw [executeCodeUntil]
      rw [if_neg hnotReturn]
      rw [hthenPc]
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hthenBound]
      have hlookup : code[1 + thenCode.length]? = some jump := by
        simp only [code, List.cons_append, List.append_assoc]
        rw [show 1 + thenCode.length = thenCode.length + 1 by omega]
        rw [List.getElem?_cons_succ]
        rw [List.getElem?_append_right (by omega)]
        simp
      rw [hlookup]
      simp [executeCodeUntil, hjumpPc]
    have hrun :
        executeCodeUntil (code.length + 1) 0 (BitVec.ofNat width returnOffset)
            code state =
          some (executeInstructions
            (executeInstructions (execute state branch) thenCode) [jump]) := by
      rw [hbranchStep]
      have hthenFactor' :
          executeCodeUntil code.length 0 (BitVec.ofNat width returnOffset)
              code (execute state branch) =
            executeCodeUntil (elseCode.length + 2) 0
              (BitVec.ofNat width returnOffset) code
              (executeInstructions (execute state branch) thenCode) := by
        have hlen : code.length = thenCode.length + (elseCode.length + 2) := by
          simp [code]
          omega
        rw [hlen]
        simpa [code, List.cons_append, List.append_assoc] using hthenFactor
      rw [hthenFactor', hjumpRun]
      rfl
    have hlen : code.length + 1 = thenCode.length + elseCode.length + 3 := by
      simp [code]
      omega
    rw [hlen] at hrun
    simpa [code, branch, jump, returnOffset, List.cons_append,
      List.append_assoc, hcondition] using hrun
  · have hbranchPcFalse :
        (execute state branch).pc = BitVec.ofNat width (8 + 4 * thenCode.length) := by
      simpa [branch, hcondition, hpc] using hbranch
    have hfalsePc :
        (execute state branch).pc =
          BitVec.ofNat width (([branch] ++ thenCode ++ [jump]).length * 4) := by
      calc
        (execute state branch).pc = BitVec.ofNat width (8 + 4 * thenCode.length) :=
          hbranchPcFalse
        _ = BitVec.ofNat width (([branch] ++ thenCode ++ [jump]).length * 4) := by
          congr 1
          simp
          omega
    have hfalseBound :
        (([branch] ++ thenCode ++ [jump]).length + elseCode.length) * 4 <
          2 ^ width := by
      simp [List.length_append]
      omega
    have hfalseRun := executeCodeUntil_suffix_of_nonbranching_fuel
      (execute state branch)
      ([branch] ++ thenCode ++ [jump]) elseCode []
      (thenCode.length + 1)
      hfalsePc hone hfalseBound
    have hrun :
        executeCodeUntil (code.length + 1) 0 (BitVec.ofNat width returnOffset)
            code state =
          some (executeInstructions (execute state branch) elseCode) := by
      rw [hbranchStep]
      have hfalseRun' :
          executeCodeUntil (elseCode.length + 1 + (thenCode.length + 1)) 0
              (BitVec.ofNat width returnOffset)
              (([branch] ++ thenCode ++ [jump]) ++ elseCode)
              (execute state branch) =
            some (executeInstructions (execute state branch) elseCode) := by
        have hreturnEq :
            (([branch] ++ thenCode ++ [jump]).length + elseCode.length) * 4 =
              returnOffset := by
          simp [returnOffset, List.length_append, List.length_cons,
            Nat.add_assoc, Nat.add_comm]
          omega
        rw [hreturnEq] at hfalseRun
        simpa [List.append_assoc] using hfalseRun
      rw [show executeCodeUntil code.length 0 (BitVec.ofNat width returnOffset)
          code (execute state branch) =
          executeCodeUntil (elseCode.length + 1 + (thenCode.length + 1)) 0
            (BitVec.ofNat width returnOffset)
            (([branch] ++ thenCode ++ [jump]) ++ elseCode)
            (execute state branch) by
          simp [code, List.length_append, List.length_cons, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]]
      rw [hfalseRun']
    have hlen : code.length + 1 = thenCode.length + elseCode.length + 3 := by
      simp [code]
      omega
    rw [hlen] at hrun
    simpa [code, branch, jump, returnOffset, List.cons_append,
      List.append_assoc, hcondition] using hrun

theorem wordFunctionToRiscVWithCalls_ite_shape [NeZero width]
    (context : WordCallContext width) (operator : Cmp) (condition : Nat)
    (rightValue : WordRegImm (Word width))
    (thenBranch elseBranch : WordProg (Word width))
    (branchLeft right : Fin 32) (prelude : List (Instruction width))
    (thenCode elseCode : List (Instruction width))
    (thenReturns elseReturns : List (Fin 32))
    (hoperands : wordConditionOperands operator condition rightValue =
      some (branchLeft, right, prelude))
    (hthen : wordFunctionToRiscVWithCalls context thenBranch =
      some (thenCode, thenReturns))
    (helse : wordFunctionToRiscVWithCalls context elseBranch =
      some (elseCode, elseReturns))
    (hreturns : thenReturns = elseReturns) :
    wordFunctionToRiscVWithCalls context
        (.ite operator condition rightValue thenBranch elseBranch) =
      some (prelude ++
        [riscVBranchFalseInstruction operator branchLeft right
          (BitVec.ofNat width (8 + 4 * thenCode.length))] ++
        thenCode ++
        [.branchEq 0 0 (BitVec.ofNat width (4 + 4 * elseCode.length))] ++
      elseCode, thenReturns) := by
  simp only [wordFunctionToRiscVWithCalls]
  rw [hoperands, hthen, helse]
  cases operator <;> simp [hreturns, riscVBranchFalseInstruction]

/-! A source/machine conditional contract.  The branch-body hypotheses are
    deliberately expressed as data relations: source evaluation starts with
    the caller PC, while the linked machine body starts after the branch
    instruction.  This lets later straight-line, coloured, call-aware, and
    FFI body theorems instantiate the same control-flow composition without
    pretending that those PCs are equal. -/

structure StateDataRelation (source target : State width) : Prop where
  registers : source.registers = target.registers
  memory : source.memory = target.memory
  privilege : source.privilege = target.privilege
  mode : source.mode = target.mode

theorem StateDataRelation.trans {source middle target : State width}
    (hfirst : StateDataRelation source middle)
    (hsecond : StateDataRelation middle target) :
    StateDataRelation source target := by
  constructor
  · exact hfirst.registers.trans hsecond.registers
  · exact hfirst.memory.trans hsecond.memory
  · exact hfirst.privilege.trans hsecond.privilege
  · exact hfirst.mode.trans hsecond.mode

theorem stateDataRelation_execute_branchEq_zero [NeZero width]
    (state : State width) (offset : Word width) :
    StateDataRelation state (execute state (.branchEq 0 0 offset)) := by
  constructor <;> rfl

theorem evalWordFunction_ite_executeCodeUntil_of_nonbranching [NeZero width]
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
      StateDataRelation thenState
        (executeInstructions
          (execute state (riscVBranchFalseInstruction operator branchLeft right
            (BitVec.ofNat width (8 + 4 * thenCode.length)))) thenCode))
    (helse : ∃ elseState,
      evalWordFunction state elseBranch = some (elseState, returns) ∧
      StateDataRelation elseState
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
      StateDataRelation sourceState machineState := by
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
    have hjumpData := stateDataRelation_execute_branchEq_zero
      (executeInstructions
        (execute state (riscVBranchFalseInstruction operator branchLeft right
          (BitVec.ofNat width (8 + 4 * thenCode.length)))) thenCode)
      (BitVec.ofNat width (4 + 4 * elseCode.length))
    refine ⟨thenState,
      executeInstructions
        (executeInstructions
          (execute state (riscVBranchFalseInstruction operator branchLeft right
            (BitVec.ofNat width (8 + 4 * thenCode.length)))) thenCode)
        [.branchEq 0 0 (BitVec.ofNat width (4 + 4 * elseCode.length))],
      hsourceEval, ?_, hthenRelation.trans hjumpData⟩
    simpa [List.cons_append, List.append_assoc] using hrun
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

/-! The previous theorem is now connected to the actual call-aware compiler
    result.  This boundary keeps the compiler witnesses, source return values,
    and machine execution result explicit, so callers can instantiate it with
    a separately proved body simulation. -/

theorem wordFunctionToRiscVWithCalls_ite_source_machine_of_nonbranching
    [NeZero width]
    (context : WordCallContext width) (state : State width)
    (operator : Cmp) (condition source : Nat)
    (thenBranch elseBranch : WordProg (Word width))
    (branchLeft right : Fin 32)
    (thenCode elseCode : List (Instruction width))
    (returnRegisters : List (Fin 32)) (returnValues : List (Word width))
    (hpc : state.pc = 0)
    (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition
        (.reg source : WordRegImm (Word width)) =
      some (branchLeft, right, []))
    (hthenCompile : wordFunctionToRiscVWithCalls context thenBranch =
      some (thenCode, returnRegisters))
    (helseCompile : wordFunctionToRiscVWithCalls context elseBranch =
      some (elseCode, returnRegisters))
    (hthen : ∃ thenState,
      evalWordFunction state thenBranch = some (thenState, returnValues) ∧
      StateDataRelation thenState
        (executeInstructions
          (execute state (riscVBranchFalseInstruction operator branchLeft right
            (BitVec.ofNat width (8 + 4 * thenCode.length)))) thenCode))
    (helse : ∃ elseState,
      evalWordFunction state elseBranch = some (elseState, returnValues) ∧
      StateDataRelation elseState
        (executeInstructions
          (execute state (riscVBranchFalseInstruction operator branchLeft right
            (BitVec.ofNat width (8 + 4 * thenCode.length)))) elseCode))
    (hthenNonbranching : ∀ instruction ∈ thenCode, instruction.isBranch = false)
    (helseNonbranching : ∀ instruction ∈ elseCode, instruction.isBranch = false)
    (hbound : (thenCode.length + elseCode.length + 2) * 4 < 2 ^ width) :
    ∃ sourceState machineState,
      evalWordFunction state
          (.ite operator condition (.reg source) thenBranch elseBranch) =
        some (sourceState, returnValues) ∧
      wordFunctionToRiscVWithCalls context
          (.ite operator condition (.reg source) thenBranch elseBranch) =
        some (riscVBranchFalseInstruction operator branchLeft right
              (BitVec.ofNat width (8 + 4 * thenCode.length)) ::
            thenCode ++
            [.branchEq 0 0 (BitVec.ofNat width (4 + 4 * elseCode.length))] ++
            elseCode, returnRegisters) ∧
      executeCodeUntil (thenCode.length + elseCode.length + 3) 0
          (BitVec.ofNat width ((thenCode.length + elseCode.length + 2) * 4))
          (riscVBranchFalseInstruction operator branchLeft right
              (BitVec.ofNat width (8 + 4 * thenCode.length)) ::
            thenCode ++
            [.branchEq 0 0 (BitVec.ofNat width (4 + 4 * elseCode.length))] ++
            elseCode) state = some machineState ∧
      StateDataRelation sourceState machineState := by
  have hshape := wordFunctionToRiscVWithCalls_ite_shape
    (context := context) (operator := operator) (condition := condition)
    (rightValue := (.reg source : WordRegImm (Word width)))
    (thenBranch := thenBranch) (elseBranch := elseBranch)
    (branchLeft := branchLeft) (right := right) (prelude := [])
    (thenCode := thenCode) (elseCode := elseCode)
    (thenReturns := returnRegisters) (elseReturns := returnRegisters)
    hoperands hthenCompile helseCompile rfl
  have hsimulation := evalWordFunction_ite_executeCodeUntil_of_nonbranching
    (state := state) (operator := operator) (condition := condition)
    (source := source) (thenBranch := thenBranch) (elseBranch := elseBranch)
    (branchLeft := branchLeft) (right := right) (thenCode := thenCode)
    (elseCode := elseCode) (returns := returnValues)
    hpc hzero hoperands hthen helse hthenNonbranching helseNonbranching hbound
  rcases hsimulation with ⟨sourceState, machineState, hsource, hmachine, hdata⟩
  refine ⟨sourceState, machineState, hsource, ?_, hmachine, hdata⟩
  simpa [List.cons_append, List.append_assoc] using hshape

theorem wordFunctionToRiscV_ite_assign [NeZero width] :
    wordFunctionToRiscV
        ((.ite .equal 1 (.reg 2)
          (.assign 3 (.const (1 : Word width)))
          (.assign 3 (.const (2 : Word width)))) : WordProg (Word width)) =
      some ([.branchNe 1 2 (BitVec.ofNat width 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2], []) := by
  simp [wordFunctionToRiscV, wordConditionOperands, wordExpToInstructions,
    wordExpToInstruction, registerOfNat]

theorem executeCode_ite_assign [NeZero width] (state : State width) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) (hwidth : 5 ≤ width) :
    (executeCode 5 0
      [.branchNe 1 2 (BitVec.ofNat width 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] state).map
      (fun state => readRegister state 3) =
      if readRegister state 1 == readRegister state 2 then
        some (1 : Word width)
      else
        some (2 : Word width) := by
  have hzero' : state.registers 0 = 0 := by
    simpa [ZeroRegister, readRegister] using hzero
  have hthen : advancesPc (.addi 3 0 (1 : Word width)) := by
    intro state
    simp [execute, writeRegister, nextPc]
  have helse : advancesPc (.addi 3 0 (2 : Word width)) := by
    intro state
    simp [execute, writeRegister, nextPc]
  have hrun := executeCode_conditional_single state .equal 1 2
    (.addi 3 0 (1 : Word width)) (.addi 3 0 (2 : Word width)) hpc
    hwidth hthen helse
  by_cases hcondition : readRegister state 1 = readRegister state 2
  · have hrisc : riscVCondition state .equal 1 2 = true := by
      simp [riscVCondition, hcondition]
    have hcondition' : state.registers 1 = state.registers 2 := by
      simpa [readRegister] using hcondition
    rw [if_pos hrisc] at hrun
    simp only [riscVBranchFalseInstruction] at hrun
    rw [hrun]
    simp [execute, writeRegister, readRegister, nextPc, hzero']
    intro hne
    exact (hne hcondition').elim
  · have hrisc : ¬riscVCondition state .equal 1 2 = true := by
      simp [riscVCondition, hcondition]
    have hcondition' : ¬state.registers 1 = state.registers 2 := by
      intro heq
      apply hcondition
      simpa [readRegister] using heq
    rw [if_neg hrisc] at hrun
    simp only [riscVBranchFalseInstruction] at hrun
    rw [hrun]
    simp [execute, writeRegister, readRegister, nextPc, hzero']
    intro heq
    exact (hcondition' heq).elim

theorem evalWordFunction_ite_assign_riscV_register [NeZero width]
    (state : State width) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) (hwidth : 5 ≤ width) :
    (evalWordFunction state
      ((.ite .equal 1 (.reg 2)
        (.assign 3 (.const (1 : Word width)))
        (.assign 3 (.const (2 : Word width)))) : WordProg (Word width))).map
      (fun result => readRegister result.1 3) =
      (executeCode 5 0
        [.branchNe 1 2 (BitVec.ofNat width 12), .addi 3 0 1,
          .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] state).map
        (fun finalState => readRegister finalState 3) := by
  have hzero' : state.registers 0 = 0 := by
    simpa [ZeroRegister, readRegister] using hzero
  rw [executeCode_ite_assign state hpc hzero hwidth]
  by_cases hcondition : state.registers 1 = state.registers 2
  · simp [evalWordFunction, evalWordCondition, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, executeInstructions, execute,
      writeRegister, readRegister, nextPc, hzero', hcondition]
  · simp [evalWordFunction, evalWordCondition, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, executeInstructions, execute,
      writeRegister, readRegister, nextPc, hzero', hcondition]

end Flapjack.RiscV
