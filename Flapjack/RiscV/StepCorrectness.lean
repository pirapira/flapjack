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

/-! Count the instructions traversed by the fuel-bounded code runner.  A
    successful return-address check costs zero additional instructions; every
    fetched instruction contributes one to the count. -/
def executeCodeUntilWithFfiCounted [NeZero width]
    (host : WordFfiHost width) :
    Nat → Word width → Word width → List (Instruction width) → State width →
      Option (State width × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, start, returnAddress, code, state =>
      if state.pc = returnAddress then
        some (state, 0)
      else
        let byteOffset := (state.pc - start).toNat
        if byteOffset % 4 ≠ 0 then none
        else
          let index := byteOffset / 4
          match code[index]? with
          | none => none
          | some instruction => do
              let nextState ← executeWithFfi host state instruction
              let (final, count) ← executeCodeUntilWithFfiCounted host fuel
                start returnAddress code nextState
              pure (final, count + 1)

theorem executeCodeUntilWithFfiCounted_fst [NeZero width]
    (host : WordFfiHost width) (fuel : Nat) (start returnAddress : Word width)
    (code : List (Instruction width)) (state : State width) :
    (executeCodeUntilWithFfiCounted host fuel start returnAddress code state).map
        Prod.fst =
      executeCodeUntilWithFfi host fuel start returnAddress code state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases hpc : state.pc = returnAddress
      · simp [executeCodeUntilWithFfiCounted, executeCodeUntilWithFfi, hpc]
      · let byteOffset := (state.pc - start).toNat
        have hbyteOffset :
            (state.pc - start).toNat =
              (2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width := by
          rfl
        by_cases halign : byteOffset % 4 = 0
        · let index := byteOffset / 4
          have halign' :
              ((2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width) % 4 = 0 := by
            simpa [byteOffset, hbyteOffset] using halign
          cases hcode : code[index]? with
          | none =>
              have hcode' :
                  code[((2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width) / 4]? = none := by
                simpa [index, byteOffset, hbyteOffset] using hcode
              simp [executeCodeUntilWithFfiCounted, executeCodeUntilWithFfi,
                hpc, hbyteOffset, halign', hcode']
          | some instruction =>
              have hcode' :
                  code[((2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width) / 4]? =
                    some instruction := by
                simpa [index, byteOffset, hbyteOffset] using hcode
              cases hstep : executeWithFfi host state instruction with
              | none =>
                  have hstep' : executeWithFfi host state instruction = none := hstep
                  simp [executeCodeUntilWithFfiCounted, executeCodeUntilWithFfi,
                    hpc, hbyteOffset, halign', hcode', hstep']
              | some nextState =>
                  cases hcount : executeCodeUntilWithFfiCounted host fuel start
                      returnAddress code nextState with
                  | none =>
                      simp [executeCodeUntilWithFfiCounted,
                        executeCodeUntilWithFfi, hpc, hbyteOffset, halign', hcode',
                        hstep]
                      rw [← ih nextState, hcount]
                      rfl
                  | some result =>
                      cases result with
                      | mk final count =>
                          simp [executeCodeUntilWithFfiCounted,
                            executeCodeUntilWithFfi, hpc, hbyteOffset, halign', hcode',
                            hstep]
                          rw [← ih nextState, hcount]
                          rfl
        · have halign' :
              ((2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width) % 4 ≠ 0 := by
            simpa [byteOffset, hbyteOffset] using halign
          simp [executeCodeUntilWithFfiCounted, executeCodeUntilWithFfi,
            hpc, hbyteOffset, halign']

theorem executeCodeUntilWithFfiCounted_count_le_fuel [NeZero width]
    (host : WordFfiHost width) (fuel : Nat) (start returnAddress : Word width)
    (code : List (Instruction width)) (state : State width) :
    ∀ final count,
      executeCodeUntilWithFfiCounted host fuel start returnAddress code state =
        some (final, count) → count ≤ fuel := by
  induction fuel generalizing state with
  | zero =>
      intro final count h
      simp [executeCodeUntilWithFfiCounted] at h
  | succ fuel ih =>
      intro final count h
      by_cases hpc : state.pc = returnAddress
      · simp [executeCodeUntilWithFfiCounted, hpc] at h
        omega
      · let byteOffset := (state.pc - start).toNat
        have hbyteOffset :
            (state.pc - start).toNat =
              (2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width := by
          rfl
        by_cases halign : byteOffset % 4 = 0
        · let index := byteOffset / 4
          have halign' :
              ((2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width) % 4 = 0 := by
            simpa [byteOffset, hbyteOffset] using halign
          cases hcode : code[index]? with
          | none =>
              have hcode' :
                  code[((2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width) / 4]? = none := by
                simpa [index, byteOffset, hbyteOffset] using hcode
              simp [executeCodeUntilWithFfiCounted, hpc, hbyteOffset, halign', hcode'] at h
          | some instruction =>
              have hcode' :
                  code[((2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width) / 4]? =
                    some instruction := by
                simpa [index, byteOffset, hbyteOffset] using hcode
              cases hstep : executeWithFfi host state instruction with
              | none =>
                  simp [executeCodeUntilWithFfiCounted, hpc, hbyteOffset, halign',
                    hcode', hstep] at h
              | some nextState =>
                  cases hcount : executeCodeUntilWithFfiCounted host fuel start
                      returnAddress code nextState with
                  | none =>
                      simp [executeCodeUntilWithFfiCounted, hpc, hbyteOffset, halign',
                        hcode', hstep, hcount] at h
                  | some result =>
                      cases result with
                      | mk final' count' =>
                          have hbound := ih nextState final' count' hcount
                          simp [executeCodeUntilWithFfiCounted, hpc, hbyteOffset,
                            halign', hcode', hstep, hcount] at h
                          omega
        · have halign' :
              ((2 ^ width - start.toNat + state.pc.toNat) % 2 ^ width) % 4 ≠ 0 := by
            simpa [byteOffset, hbyteOffset] using halign
          simp [executeCodeUntilWithFfiCounted, hpc, hbyteOffset, halign'] at h

theorem executeInstructions_tailCall_pc [NeZero width]
    (state : State width) (entry : Word width)
    (moves : List (Instruction width)) (hzero : ZeroRegister state) :
    (executeInstructions state
      (moves ++ [.addi 31 0 entry, .jalr 0 31 0])).pc =
      jalrTarget entry 0 := by
  have hzeroMoves : ZeroRegister (executeInstructions state moves) := by
    induction moves generalizing state with
    | nil => exact hzero
    | cons instruction moves ih =>
        exact ih (execute state instruction)
          (execute_zeroRegister_preserved state instruction hzero)
  have hzeroMoves' :
      (executeInstructions state moves).registers 0 = 0 := by
    simpa [ZeroRegister, readRegister] using hzeroMoves
  rw [executeInstructions_append]
  simp [executeInstructions, execute, writeRegister, readRegister,
    nextPc, jalrTarget, hzeroMoves']

theorem wordTailCallToRiscV_execute_pc [NeZero width]
    (state : State width) (entry : Word width)
    (parameters arguments : List Nat) (code : List (Instruction width))
    (hzero : ZeroRegister state)
    (hcompile : wordTailCallToRiscV entry parameters arguments = some code) :
    (executeInstructions state code).pc = jalrTarget entry 0 := by
  cases hmove : wordRegisterMoves (width := width) (parameters.zip arguments) with
  | none =>
      simp [wordTailCallToRiscV, hmove] at hcompile
  | some moves =>
      simp [wordTailCallToRiscV, hmove] at hcompile
      rcases hcompile with ⟨_, hcode⟩
      subst code
      exact executeInstructions_tailCall_pc state entry moves hzero

theorem executeInstructions_stackCall_pc [NeZero width]
    (state : State width) (entry : Word width)
    (moves : List (Instruction width)) (hzero : ZeroRegister state) :
    (executeInstructions state
      (moves ++
        [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
         .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])).pc =
      jalrTarget entry 0 := by
  have hzeroMoves : ZeroRegister (executeInstructions state moves) := by
    induction moves generalizing state with
    | nil => exact hzero
    | cons instruction moves ih =>
        exact ih (execute state instruction)
          (execute_zeroRegister_preserved state instruction hzero)
  have hzeroMoves' :
      (executeInstructions state moves).registers 0 = 0 := by
    simpa [ZeroRegister, readRegister] using hzeroMoves
  rw [executeInstructions_append]
  simp only [executeInstructions]
  rw [execute_jalr_pc]
  simp [execute, writeRegister, readRegister,
    nextPc, writeWordValue_registers, jalrTarget, hzeroMoves']

theorem wordCallToRiscVWithStack_prefix_shape [NeZero width]
    (entry : Word width) (parameters returns arguments destinations : List Nat)
    (code : List (Instruction width))
    (hcompile :
      wordCallToRiscVWithStack entry parameters returns arguments destinations =
        some code) :
    ∃ parameterMoves resultMoves,
      code =
        parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0] ++
          resultMoves := by
  cases hmove : wordRegisterMoves (width := width)
      (parameters.zip arguments) with
  | none =>
      simp [wordCallToRiscVWithStack, hmove] at hcompile
  | some parameterMoves =>
      cases hresult : wordRegisterMoves (width := width)
          (destinations.zip returns) with
      | none =>
          simp [wordCallToRiscVWithStack, hmove, hresult] at hcompile
      | some resultMoves =>
          simp [wordCallToRiscVWithStack, hmove, hresult] at hcompile
          exact ⟨parameterMoves,
            resultMoves ++ [.loadWord 1 30,
              .addi 30 30 (BitVec.ofNat width (width / 8))],
            by simpa [List.cons_append] using hcompile.2.symm⟩

theorem wordCallToRiscVWithStack_prefix_execute_pc [NeZero width]
    (state : State width) (entry : Word width)
    (parameters returns arguments destinations : List Nat)
    (code : List (Instruction width)) (hzero : ZeroRegister state)
    (hcompile :
      wordCallToRiscVWithStack entry parameters returns arguments destinations =
        some code) :
    ∃ parameterMoves resultMoves,
      (executeInstructions state
        (parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])).pc =
        jalrTarget entry 0 ∧
      code =
        parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0] ++
          resultMoves := by
  rcases wordCallToRiscVWithStack_prefix_shape entry parameters returns arguments
    destinations code hcompile with ⟨parameterMoves, resultMoves, hcode⟩
  refine ⟨parameterMoves, resultMoves,
    executeInstructions_stackCall_pc state entry parameterMoves hzero, hcode⟩

theorem executeInstructions_stackCall_restore_link_sp [NeZero width]
    (state : State width) (stackAddress savedLink : Word width)
    (hstack : readRegister state 30 = stackAddress)
    (hsaved : readWordValue state stackAddress = savedLink) :
    let final := executeInstructions state
      [.loadWord 1 30, .addi 30 30 (BitVec.ofNat width (width / 8))]
    readRegister final 1 = savedLink ∧
      readRegister final 30 =
        stackAddress + BitVec.ofNat width (width / 8) ∧
      final.pc = state.pc + BitVec.ofNat width 8 := by
  have hstack' : state.registers 30 = stackAddress := by
    simpa [readRegister] using hstack
  dsimp
  simp [executeInstructions, execute, writeRegister, readRegister,
    nextPc, hstack', hsaved]
  rw [show (8 : Nat) = 4 + 4 by omega, BitVec.ofNat_add]
  rw [BitVec.add_assoc]

theorem executeInstructions_pc_fold_of_nonbranching [NeZero width]
    (state : State width) (code : List (Instruction width))
    (hcode : ∀ instruction ∈ code, instruction.isBranch = false) :
    (executeInstructions state code).pc =
      code.foldl (fun pc _ => pc + 4) state.pc := by
  induction code generalizing state with
  | nil => rfl
  | cons instruction code ih =>
      have hnotBranch : instruction.isBranch = false :=
        hcode instruction (by simp)
      have htail : ∀ nextInstruction ∈ code, nextInstruction.isBranch = false := by
        intro nextInstruction hnext
        exact hcode nextInstruction (by simp [hnext])
      simp only [executeInstructions, List.foldl]
      rw [ih (execute state instruction) htail]
      rw [execute_pc_advance state instruction hnotBranch]

theorem executeInstructions_pc_of_nonbranching [NeZero width]
    (state : State width) (code : List (Instruction width))
    (hcode : ∀ instruction ∈ code, instruction.isBranch = false) :
    (executeInstructions state code).pc =
      state.pc + BitVec.ofNat width (code.length * 4) := by
  induction code generalizing state with
  | nil => simp [executeInstructions]
  | cons instruction code ih =>
      have hnotBranch : instruction.isBranch = false :=
        hcode instruction (by simp)
      have htail : ∀ nextInstruction ∈ code, nextInstruction.isBranch = false := by
        intro nextInstruction hnext
        exact hcode nextInstruction (by simp [hnext])
      simp only [executeInstructions, List.length_cons]
      rw [ih (execute state instruction) htail]
      rw [execute_pc_advance state instruction hnotBranch]
      simp only [Nat.succ_mul, BitVec.ofNat_add]
      rw [BitVec.add_assoc]
      congr 1
      exact BitVec.add_comm _ _

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

theorem wordFunctionToRiscV_counted_sound_of_straightLine [NeZero width]
    (context : WordCallContext width) (state : State width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordFunctionToRiscVWithCalls context program =
      some (code, [])) :
    evalWordFunction state program =
      some ((executeInstructionsCounted state code).1, []) := by
  have hsound := wordFunctionToRiscVWithCalls_sound_of_straightLine
    context state program hstraight code hcompile
  rw [executeInstructionsCounted_spec]
  exact hsound

end Flapjack.RiscV
