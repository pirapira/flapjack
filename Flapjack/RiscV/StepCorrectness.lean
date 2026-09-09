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

/-! The tail-call PC theorem also has a value-transfer form for the smallest
    ABI case.  Keeping the source and destination names explicit makes the
    no-clobber conditions visible to callers composing this with callee
    execution. -/

theorem wordTailCallToRiscV_execute_single_parameter [NeZero width]
    (state : State width) (entry : Word width)
    (parameter argument : Nat) (code : List (Instruction width))
    (hzero : ZeroRegister state)
    (hparameter : parameter < 32) (hargument : argument < 32)
    (hparameterNonzero : parameter ≠ 0)
    (hparameterNoScratch : parameter ≠ 31)
    (hcompile : wordTailCallToRiscV entry [parameter] [argument] = some code) :
    readRegister (executeInstructions state code) ⟨parameter, hparameter⟩ =
        readRegister state ⟨argument, hargument⟩ ∧
      (executeInstructions state code).pc = jalrTarget entry 0 := by
  have hshape : wordTailCallToRiscV entry [parameter] [argument] = some
      ([.addi ⟨parameter, hparameter⟩ ⟨argument, hargument⟩ 0,
        .addi 31 0 entry, .jalr 0 31 0] : List (Instruction width)) := by
    simp [wordTailCallToRiscV, wordRegisterMoves, registerOfNat,
      hparameter, hargument]
  have hcode :
      ([.addi ⟨parameter, hparameter⟩ ⟨argument, hargument⟩ 0,
        .addi 31 0 entry, .jalr 0 31 0] : List (Instruction width)) = code := by
    exact Option.some.inj (hshape.symm.trans hcompile)
  have hparameterNoScratch' :
      (⟨parameter, hparameter⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hparameterNoScratch
    exact congrArg Fin.val heq
  subst code
  constructor
  · simp [executeInstructions, execute, writeRegister, readRegister,
      nextPc, hparameterNonzero, hparameterNoScratch']
  · exact executeInstructions_tailCall_pc state entry
      [.addi ⟨parameter, hparameter⟩ ⟨argument, hargument⟩ 0] hzero

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

theorem executeCode_suffix_of_nonbranching [NeZero width]
    (state : State width) (prelude suffix : List (Instruction width))
    (hpc : state.pc = BitVec.ofNat width (prelude.length * 4))
    (hsuffix : ∀ instruction ∈ suffix, instruction.isBranch = false)
    (hbound : (prelude.length + suffix.length) * 4 < 2 ^ width) :
    executeCode (suffix.length + 1) 0 (prelude ++ suffix) state =
      some (executeInstructions state suffix) := by
  induction suffix generalizing prelude state with
  | nil =>
      have hprefixBound : prelude.length * 4 < 2 ^ width := by omega
      simp [executeCode, executeInstructions, hpc,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hprefixBound]
  | cons instruction suffix ih =>
      have hnotBranch : instruction.isBranch = false :=
        hsuffix instruction (by simp)
      have htail : ∀ nextInstruction ∈ suffix, nextInstruction.isBranch = false := by
        intro nextInstruction hnext
        exact hsuffix nextInstruction (by simp [hnext])
      have hnextPc : (execute state instruction).pc =
          BitVec.ofNat width ((prelude.length + 1) * 4) := by
        calc
          (execute state instruction).pc = state.pc + 4 :=
            execute_pc_advance state instruction hnotBranch
          _ = BitVec.ofNat width (prelude.length * 4) + 4 := by rw [hpc]
          _ = BitVec.ofNat width (prelude.length * 4) + BitVec.ofNat width 4 := by rfl
          _ = BitVec.ofNat width (prelude.length * 4 + 4) := by
            rw [← BitVec.ofNat_add]
          _ = BitVec.ofNat width ((prelude.length + 1) * 4) := by
            congr 1
            omega
      have htailBound : (prelude.length + 1 + suffix.length) * 4 < 2 ^ width := by
        simp only [List.length_cons] at hbound
        omega
      have htailBound' : ((prelude ++ [instruction]).length + suffix.length) * 4 <
          2 ^ width := by
        simpa [List.length_append] using htailBound
      have hrest := ih (prelude := prelude ++ [instruction])
        (state := execute state instruction) (by simpa using hnextPc)
        htail htailBound'
      have hpreludeBound : prelude.length * 4 < 2 ^ width := by omega
      have hstep :
          executeCode ((instruction :: suffix).length + 1) 0
              (prelude ++ instruction :: suffix) state =
            executeCode (suffix.length + 1) 0
              (prelude ++ [instruction] ++ suffix) (execute state instruction) := by
        simp [executeCode, hpc, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hpreludeBound]
      rw [hstep, hrest]
      simp [executeInstructions]

theorem executeCode_of_nonbranching [NeZero width]
    (state : State width) (code : List (Instruction width))
    (hpc : state.pc = 0)
    (hcode : ∀ instruction ∈ code, instruction.isBranch = false)
    (hbound : code.length * 4 < 2 ^ width) :
    executeCode (code.length + 1) 0 code state =
      some (executeInstructions state code) := by
  apply executeCode_suffix_of_nonbranching state [] code
  · simpa using hpc
  · exact hcode
  · simpa using hbound

theorem executeCodeUntil_suffix_of_nonbranching_fuel [NeZero width]
    (state : State width) (prelude suffix tail : List (Instruction width))
    (extra : Nat)
    (hpc : state.pc = BitVec.ofNat width (prelude.length * 4))
    (hsuffix : ∀ instruction ∈ suffix, instruction.isBranch = false)
    (hbound : (prelude.length + suffix.length + tail.length) * 4 < 2 ^ width) :
    executeCodeUntil (suffix.length + 1 + extra) 0
        (BitVec.ofNat width ((prelude.length + suffix.length) * 4))
        (prelude ++ suffix ++ tail) state =
      some (executeInstructions state suffix) := by
  induction suffix generalizing prelude state tail with
  | nil =>
      have hprefixBound : prelude.length * 4 < 2 ^ width := by omega
      cases extra <;> simp [executeCodeUntil, executeInstructions, hpc]
  | cons instruction suffix ih =>
      have hnotBranch : instruction.isBranch = false :=
        hsuffix instruction (by simp)
      have htail : ∀ nextInstruction ∈ suffix, nextInstruction.isBranch = false := by
        intro nextInstruction hnext
        exact hsuffix nextInstruction (by simp [hnext])
      have hpreludeBound : prelude.length * 4 < 2 ^ width := by omega
      have hnotReturn : state.pc ≠
          BitVec.ofNat width ((prelude.length + (instruction :: suffix).length) * 4) := by
        intro heq
        rw [hpc] at heq
        have heqNat := congrArg BitVec.toNat heq
        have hreturnBound :
            (prelude.length + (instruction :: suffix).length) * 4 < 2 ^ width := by
          have hbound' := hbound
          simp only [List.length_cons] at hbound'
          have hle :
              (prelude.length + (instruction :: suffix).length) * 4 ≤
                (prelude.length + (instruction :: suffix).length + tail.length) * 4 := by
            omega
          apply Nat.lt_of_le_of_lt hle
          simpa [Nat.add_assoc] using hbound'
        have hreturnBound' :
            (prelude.length + (suffix.length + 1)) * 4 < 2 ^ width := by
          simpa [List.length_cons] using hreturnBound
        simp only [List.length_cons, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hpreludeBound, Nat.mod_eq_of_lt hreturnBound'] at heqNat
        omega
      have hnextPc : (execute state instruction).pc =
          BitVec.ofNat width ((prelude.length + 1) * 4) := by
        calc
          (execute state instruction).pc = state.pc + 4 :=
            execute_pc_advance state instruction hnotBranch
          _ = BitVec.ofNat width (prelude.length * 4) + 4 := by rw [hpc]
          _ = BitVec.ofNat width (prelude.length * 4) + BitVec.ofNat width 4 := by rfl
          _ = BitVec.ofNat width (prelude.length * 4 + 4) := by
            rw [← BitVec.ofNat_add]
          _ = BitVec.ofNat width ((prelude.length + 1) * 4) := by
            congr 1
            omega
      have htailBound :
          ((prelude ++ [instruction]).length + suffix.length + tail.length) * 4 <
            2 ^ width := by
        simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hbound
      have hrest := ih (prelude := prelude ++ [instruction])
        (state := execute state instruction) (tail := tail)
        (by simpa [List.length_append] using hnextPc) htail htailBound
      have hstep :
          executeCodeUntil ((instruction :: suffix).length + 1 + extra) 0
              (BitVec.ofNat width
                ((prelude.length + (instruction :: suffix).length) * 4))
              (prelude ++ (instruction :: suffix) ++ tail) state =
            executeCodeUntil (suffix.length + 1 + extra) 0
              (BitVec.ofNat width
                (((prelude ++ [instruction]).length + suffix.length) * 4))
              ((prelude ++ [instruction]) ++ suffix ++ tail)
                (execute state instruction) := by
        cases extra <;> simp only [Nat.add_zero, Nat.add_succ]
        all_goals
          rw [executeCodeUntil]
          rw [hpc]
          have hnotReturnPc := hnotReturn
          rw [hpc] at hnotReturnPc
          rw [if_neg hnotReturnPc]
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpreludeBound,
            Nat.add_comm, Nat.add_left_comm]
          rw [List.getElem?_append_right (by omega)]
          simp
          congr 1
          simp [Nat.add_assoc]
      rw [hstep, hrest]
      simp [executeInstructions]

theorem executeCodeUntil_suffix_of_nonbranching [NeZero width]
    (state : State width) (prelude suffix tail : List (Instruction width))
    (hpc : state.pc = BitVec.ofNat width (prelude.length * 4))
    (hsuffix : ∀ instruction ∈ suffix, instruction.isBranch = false)
    (hbound : (prelude.length + suffix.length + tail.length) * 4 < 2 ^ width) :
    executeCodeUntil (suffix.length + 1) 0
        (BitVec.ofNat width ((prelude.length + suffix.length) * 4))
        (prelude ++ suffix ++ tail) state =
      some (executeInstructions state suffix) := by
  exact executeCodeUntil_suffix_of_nonbranching_fuel state prelude suffix tail 0
    hpc hsuffix hbound

theorem executeCodeUntil_after_nonbranching [NeZero width]
    (state : State width) (prelude suffix tail : List (Instruction width))
    (fuel returnOffset : Nat)
    (hpc : state.pc = BitVec.ofNat width (prelude.length * 4))
    (hsuffix : ∀ instruction ∈ suffix, instruction.isBranch = false)
    (hreturn : (prelude.length + suffix.length) * 4 < returnOffset)
    (hreturnBound : returnOffset < 2 ^ width) :
    executeCodeUntil (suffix.length + fuel) 0 (BitVec.ofNat width returnOffset)
        (prelude ++ suffix ++ tail) state =
      executeCodeUntil fuel 0 (BitVec.ofNat width returnOffset)
        (prelude ++ suffix ++ tail) (executeInstructions state suffix) := by
  induction suffix generalizing prelude state tail with
  | nil =>
      simp [executeInstructions]
  | cons instruction suffix ih =>
      have hnotBranch : instruction.isBranch = false :=
        hsuffix instruction (by simp)
      have htail : ∀ nextInstruction ∈ suffix, nextInstruction.isBranch = false := by
        intro nextInstruction hnext
        exact hsuffix nextInstruction (by simp [hnext])
      have hpreludeBound : prelude.length * 4 < 2 ^ width := by omega
      have hnotReturn : state.pc ≠ BitVec.ofNat width returnOffset := by
        intro heq
        rw [hpc] at heq
        have heqNat := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpreludeBound,
          Nat.mod_eq_of_lt hreturnBound] at heqNat
        omega
      have hnextPc : (execute state instruction).pc =
          BitVec.ofNat width ((prelude.length + 1) * 4) := by
        calc
          (execute state instruction).pc = state.pc + 4 :=
            execute_pc_advance state instruction hnotBranch
          _ = BitVec.ofNat width (prelude.length * 4) + 4 := by rw [hpc]
          _ = BitVec.ofNat width (prelude.length * 4) + BitVec.ofNat width 4 := by rfl
          _ = BitVec.ofNat width (prelude.length * 4 + 4) := by
            rw [← BitVec.ofNat_add]
          _ = BitVec.ofNat width ((prelude.length + 1) * 4) := by
            congr 1
            omega
      have hreturnTail :
          ((prelude ++ [instruction]).length + suffix.length) * 4 < returnOffset := by
        simpa [List.length_append, List.length_cons, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hreturn
      have hrest := ih (prelude := prelude ++ [instruction])
        (state := execute state instruction) (tail := tail)
        (by simpa [List.length_append] using hnextPc) htail hreturnTail
      have hstep :
          executeCodeUntil ((instruction :: suffix).length + fuel) 0
              (BitVec.ofNat width returnOffset)
              (prelude ++ (instruction :: suffix) ++ tail) state =
            executeCodeUntil (suffix.length + fuel) 0
              (BitVec.ofNat width returnOffset)
              ((prelude ++ [instruction]) ++ suffix ++ tail)
                (execute state instruction) := by
        cases fuel <;> simp only [List.length_cons, Nat.add_zero, Nat.add_succ]
        all_goals
          rw [executeCodeUntil]
          rw [hpc]
          have hnotReturnPc := hnotReturn
          rw [hpc] at hnotReturnPc
          rw [if_neg hnotReturnPc]
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpreludeBound,
            Nat.add_comm, Nat.add_left_comm]
          rw [List.getElem?_append_right (by omega)]
          simp
      rw [hstep, hrest]
      simp [executeInstructions]

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
