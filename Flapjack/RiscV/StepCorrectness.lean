import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.Ffi
import Flapjack.RiscV.ParallelMoveCorrectness

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

/-! A counted code runner agrees with sequential counted execution on a
    suffix whose successful instruction transitions advance the program
    counter by one instruction.  Ordinary non-branching instructions satisfy
    this hypothesis by `execute_pc_advance`; an ECALL supplies it through the
    host-transition contract.  Keeping that condition explicit is important:
    the host is allowed to choose the post-ECALL state, including its PC. -/
theorem executeCodeUntilWithFfiCounted_suffix
    [NeZero width] (host : WordFfiHost width)
    (state : State width) (prelude suffix tail : List (Instruction width))
    (hpc : state.pc = BitVec.ofNat width (prelude.length * 4))
    (hadvance : ∀ (current : State width) (instruction : Instruction width),
      instruction ∈ suffix → ∀ next,
        executeWithFfi host current instruction = some next →
          next.pc = current.pc + 4)
    (hbound : (prelude.length + suffix.length + tail.length) * 4 < 2 ^ width) :
    executeCodeUntilWithFfiCounted host (suffix.length + 1) 0
        (BitVec.ofNat width ((prelude.length + suffix.length) * 4))
        (prelude ++ suffix ++ tail) state =
      executeInstructionsWithFfiCounted host state suffix := by
  have hmap_bind : ∀ (result : Option (State width × Nat)),
      result.map (fun pair => (pair.1, pair.2 + 1)) =
        result.bind (fun pair => some (pair.1, pair.2 + 1)) := by
    intro result
    cases result <;> rfl
  induction suffix generalizing prelude state tail with
  | nil =>
      simp [executeCodeUntilWithFfiCounted, executeInstructionsWithFfiCounted,
        hpc]
  | cons instruction suffix ih =>
      have htail : ∀ (nextInstruction : Instruction width),
          nextInstruction ∈ suffix → ∀ current next,
            executeWithFfi host current nextInstruction = some next →
              next.pc = current.pc + 4 := by
        intro nextInstruction hnext current next hstep
        exact hadvance current nextInstruction (by simp [hnext]) next hstep
      have htail' : ∀ (current : State width) (nextInstruction : Instruction width),
          nextInstruction ∈ suffix → ∀ next,
            executeWithFfi host current nextInstruction = some next →
              next.pc = current.pc + 4 := by
        intro current nextInstruction hnext next hstep
        exact htail nextInstruction hnext current next hstep
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
      have htailBound :
          ((prelude ++ [instruction]).length + suffix.length + tail.length) * 4 <
            2 ^ width := by
        simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hbound
      cases hstep : executeWithFfi host state instruction with
      | none =>
          have hnotReturnPc' :
              BitVec.ofNat width (prelude.length * 4) ≠
                BitVec.ofNat width ((prelude.length + (suffix.length + 1)) * 4) := by
            simpa [hpc, List.length_cons] using hnotReturn
          simp only [executeCodeUntilWithFfiCounted,
            executeInstructionsWithFfiCounted]
          simp [hpc, hnotReturnPc', BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hpreludeBound, hstep]
      | some nextState =>
          have hnextPc : nextState.pc =
              BitVec.ofNat width ((prelude.length + 1) * 4) := by
            calc
              nextState.pc = state.pc + 4 :=
                hadvance state instruction (by simp) nextState hstep
              _ = BitVec.ofNat width (prelude.length * 4) + 4 := by rw [hpc]
              _ = BitVec.ofNat width (prelude.length * 4) +
                  BitVec.ofNat width 4 := by rfl
              _ = BitVec.ofNat width (prelude.length * 4 + 4) := by
                rw [← BitVec.ofNat_add]
              _ = BitVec.ofNat width ((prelude.length + 1) * 4) := by
                congr 1
                omega
          have hnextPc' : nextState.pc =
              BitVec.ofNat width ((prelude ++ [instruction]).length * 4) := by
            simpa [List.length_append] using hnextPc
          have hrest := ih (prelude := prelude ++ [instruction])
            (state := nextState) (tail := tail) hnextPc' htail' htailBound
          have hstepCode :
              executeCodeUntilWithFfiCounted host
                  ((instruction :: suffix).length + 1) 0 (BitVec.ofNat width
                    ((prelude.length + (instruction :: suffix).length) * 4))
                  (prelude ++ (instruction :: suffix) ++ tail) state =
                (executeCodeUntilWithFfiCounted host (suffix.length + 1) 0
                  (BitVec.ofNat width
                    (((prelude ++ [instruction]).length + suffix.length) * 4))
                  ((prelude ++ [instruction]) ++ suffix ++ tail) nextState).map
                    (fun result => (result.1, result.2 + 1)) := by
            have hnotReturnPc :
                BitVec.ofNat width (prelude.length * 4) ≠
                  BitVec.ofNat width
                    ((prelude.length + (instruction :: suffix).length) * 4) := by
              simpa [hpc] using hnotReturn
            rw [executeCodeUntilWithFfiCounted]
            rw [hpc]
            rw [if_neg hnotReturnPc]
            simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpreludeBound,
              Nat.add_comm, Nat.add_left_comm]
            rw [List.getElem?_append_right (by omega)]
            simp [hstep]
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using (hmap_bind _).symm
          rw [hstepCode, hrest]
          rw [executeInstructionsWithFfiCounted]
          simp [hstep]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            List.append_assoc] using hmap_bind _

/-! A counted non-branching prefix can be factored out even when the
    remaining runner has additional fuel.  The return address is kept beyond
    the prefix, so this lemma is the counted counterpart of
    `executeCodeUntil_after_nonbranching`. -/
theorem executeCodeUntilWithFfiCounted_after_nonbranching
    [NeZero width] (host : WordFfiHost width)
    (state : State width) (prelude suffix tail : List (Instruction width))
    (fuel : Nat) (returnAddress : Word width)
    (hpc : state.pc = BitVec.ofNat width (prelude.length * 4))
    (hadvance : ∀ (current : State width) (instruction : Instruction width),
      instruction ∈ suffix → ∀ next,
        executeWithFfi host current instruction = some next →
          next.pc = current.pc + 4)
    (hreturn : (prelude.length + suffix.length) * 4 < returnAddress.toNat)
    (hreturnBound : returnAddress.toNat < 2 ^ width) :
    executeCodeUntilWithFfiCounted host (suffix.length + fuel) 0 returnAddress
        (prelude ++ suffix ++ tail) state =
      (executeInstructionsWithFfiCounted host state suffix).bind
        (fun result =>
          (executeCodeUntilWithFfiCounted host fuel 0 returnAddress
            (prelude ++ suffix ++ tail) result.1).map
            (fun final => (final.1, final.2 + suffix.length))) := by
  induction suffix generalizing prelude state tail fuel with
  | nil =>
      simp [executeInstructionsWithFfiCounted]
  | cons instruction suffix ih =>
      have htail : ∀ (nextInstruction : Instruction width),
          nextInstruction ∈ suffix → ∀ current next,
            executeWithFfi host current nextInstruction = some next →
              next.pc = current.pc + 4 := by
        intro nextInstruction hnext current next hstep
        exact hadvance current nextInstruction (by simp [hnext]) next hstep
      have htail' : ∀ (current : State width) (nextInstruction : Instruction width),
          nextInstruction ∈ suffix → ∀ next,
            executeWithFfi host current nextInstruction = some next →
              next.pc = current.pc + 4 := by
        intro current nextInstruction hnext next hstep
        exact htail nextInstruction hnext current next hstep
      have hpreludeBound : prelude.length * 4 < 2 ^ width := by
        have hle : prelude.length * 4 ≤
            (prelude.length + (instruction :: suffix).length) * 4 := by
          simp only [List.length_cons]
          omega
        exact Nat.lt_of_le_of_lt hle (by
          have hreturnNat := hreturn
          simp only [List.length_cons] at hreturnNat
          omega)
      have hnotReturn : state.pc ≠ returnAddress := by
        intro heq
        rw [hpc] at heq
        have heqNat := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpreludeBound] at heqNat
        exact (by omega : ¬ (prelude.length * 4 = returnAddress.toNat)) heqNat
      have htailBound :
          ((prelude ++ [instruction]).length + suffix.length) * 4 <
            returnAddress.toNat := by
        simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hreturn
      cases hstep : executeWithFfi host state instruction with
      | none =>
          have hnotReturnPc :
              BitVec.ofNat width (prelude.length * 4) ≠ returnAddress := by
            simpa [hpc] using hnotReturn
          simp only [List.length_cons, Nat.succ_add]
          rw [executeCodeUntilWithFfiCounted]
          rw [hpc]
          rw [if_neg hnotReturnPc]
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpreludeBound]
          simp [hstep, executeInstructionsWithFfiCounted]
      | some nextState =>
          have hnextPc : nextState.pc =
              BitVec.ofNat width ((prelude.length + 1) * 4) := by
            calc
              nextState.pc = state.pc + 4 :=
                hadvance state instruction (by simp) nextState hstep
              _ = BitVec.ofNat width (prelude.length * 4) + 4 := by rw [hpc]
              _ = BitVec.ofNat width (prelude.length * 4) +
                  BitVec.ofNat width 4 := by rfl
              _ = BitVec.ofNat width (prelude.length * 4 + 4) := by
                rw [← BitVec.ofNat_add]
              _ = BitVec.ofNat width ((prelude.length + 1) * 4) := by
                congr 1
                omega
          have hnextPc' : nextState.pc =
              BitVec.ofNat width ((prelude ++ [instruction]).length * 4) := by
            simpa [List.length_append] using hnextPc
          have hrest := ih (prelude := prelude ++ [instruction])
            (state := nextState) (tail := tail) fuel hnextPc' htail' htailBound
          have hstepCode :
              executeCodeUntilWithFfiCounted host
                  ((instruction :: suffix).length + fuel) 0 returnAddress
                  (prelude ++ (instruction :: suffix) ++ tail) state =
                (executeCodeUntilWithFfiCounted host
                  (suffix.length + fuel) 0 returnAddress
                  ((prelude ++ [instruction]) ++ suffix ++ tail) nextState).map
                    (fun result => (result.1, result.2 + 1)) := by
            have hnotReturnPc :
                BitVec.ofNat width (prelude.length * 4) ≠ returnAddress := by
              simpa [hpc] using hnotReturn
            simp only [List.length_cons, Nat.succ_add]
            rw [executeCodeUntilWithFfiCounted]
            rw [hpc]
            rw [if_neg hnotReturnPc]
            simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpreludeBound]
            rw [hstep]
            have hmap_bind (result : Option (State width × Nat)) :
                result.bind (fun value => some (value.1, value.2 + 1)) =
                  result.map (fun value => (value.1, value.2 + 1)) := by
              cases result <;> rfl
            simpa using (hmap_bind
              (executeCodeUntilWithFfiCounted host (suffix.length + fuel)
                (0 : Word width) returnAddress
                (prelude ++ instruction :: (suffix ++ tail)) nextState))
          rw [hstepCode, hrest]
          simp only [List.append_assoc]
          cases hsequence : executeInstructionsWithFfiCounted host nextState suffix with
          | none =>
              simp [executeInstructionsWithFfiCounted, hstep, hsequence]
          | some sequence =>
              cases sequence with
              | mk intermediate sequenceCount =>
                  have hmap_count (runner : Option (State width × Nat)) :
                      (runner.map (fun result => (result.1, result.2 + suffix.length))).map
                          (fun result => (result.1, result.2 + 1)) =
                        runner.map
                          (fun result => (result.1, result.2 + (suffix.length + 1))) := by
                    cases runner with
                    | none => rfl
                    | some result =>
                        cases result
                        simp [Nat.add_assoc]
                  simpa [executeInstructionsWithFfiCounted, hstep, hsequence,
                    List.append_assoc] using hmap_count
                    (executeCodeUntilWithFfiCounted host fuel (0 : Word width)
                      returnAddress (prelude ++ instruction :: (suffix ++ tail))
                      intermediate)

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

theorem executeInstructions_tailCall_read_register [NeZero width]
    (state : State width) (entry : Word width)
    (moves : List (Instruction width)) (register : Fin 32)
    (hregisterNoScratch : register ≠ 31) :
    readRegister (executeInstructions state
      (moves ++ [.addi 31 0 entry, .jalr 0 31 0])) register =
      readRegister (executeInstructions state moves) register := by
  rw [executeInstructions_append]
  simp [executeInstructions, execute, writeRegister, readRegister,
    nextPc, hregisterNoScratch]

theorem wordRegisterMoves_shape [NeZero width]
    (moves : List (Nat × Nat)) (code : List (Instruction width))
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hcompile : wordRegisterMoves (width := width) moves = some code) :
    code = moves.flatMap (wordMoveInstructionList (width := width)) := by
  induction moves generalizing code with
  | nil =>
      simp [wordRegisterMoves] at hcompile ⊢
      exact hcompile
  | cons head tail ih =>
      have hhead := hvalid head (by simp)
      have htail : ∀ move, move ∈ tail →
          move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31 := by
        intro move hmove
        exact hvalid move (by simp [hmove])
      cases htailCode : wordRegisterMoves (width := width) tail with
      | none =>
          simp [wordRegisterMoves, htailCode] at hcompile
      | some tailCode =>
          have htailShape := ih (code := tailCode) htail htailCode
          have hheadDestination : registerOfNat head.1 =
              some ⟨head.1, hhead.1⟩ := by
            simp [registerOfNat, hhead.1]
          have hheadSource : registerOfNat head.2 =
              some ⟨head.2, hhead.2.1⟩ := by
            simp [registerOfNat, hhead.2.1]
          have hcode :
              (.addi ⟨head.1, hhead.1⟩ ⟨head.2, hhead.2.1⟩ 0
                :: tailCode : List (Instruction width)) = code := by
            simpa [wordRegisterMoves, htailCode, hheadDestination,
              hheadSource] using hcompile
          subst code
          simp [wordMoveInstructionList, wordExpToInstructions,
            wordExpToInstruction, registerOfNat, hhead.1, hhead.2.1,
            htailShape]

theorem wordTailCallToRiscV_execute_moves_transfer [NeZero width]
    (state : State width) (entry : Word width)
    (parameters arguments : List Nat) (code : List (Instruction width))
    (hzero : ZeroRegister state)
    (hvalid : ∀ move, move ∈ parameters.zip arguments →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hdestNonzero : ∀ move, move ∈ parameters.zip arguments → move.1 ≠ 0)
    (hdestinations : ((parameters.zip arguments).map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ parameters.zip arguments →
      move.2 ∉ (parameters.zip arguments).map Prod.fst)
    (hcompile : wordTailCallToRiscV entry parameters arguments = some code) :
    (∀ move (hmove : move ∈ parameters.zip arguments),
      readRegister (executeInstructions state code)
          ⟨move.1, (hvalid move hmove).1⟩ =
        readRegister state ⟨move.2, (hvalid move hmove).2.1⟩) ∧
      (executeInstructions state code).pc = jalrTarget entry 0 := by
  cases hmove : wordRegisterMoves (width := width)
      (parameters.zip arguments) with
  | none =>
      simp [wordTailCallToRiscV, hmove] at hcompile
  | some moves =>
      have hcompile' : parameters.length = arguments.length ∧
          moves ++ [.addi 31 0 entry, .jalr 0 31 0] = code := by
        simpa [wordTailCallToRiscV, hmove] using hcompile
      have hcode :
          moves ++ [.addi 31 0 entry, .jalr 0 31 0] = code := by
        exact hcompile'.2
      have hmoveShape := wordRegisterMoves_shape
        (parameters.zip arguments) moves hvalid hmove
      subst code
      have hsourcePreserved := executeWordMoves_preserves_sources state
        (parameters.zip arguments) hdestinations hnoSource hvalid hdestNonzero
      constructor
      · intro move hmove'
        have hdestination := hvalid move hmove'
        have hregisterNoScratch :
            (⟨move.1, hdestination.1⟩ : Fin 32) ≠ 31 := by
          intro heq
          apply hdestination.2.2.1
          exact congrArg Fin.val heq
        rw [hmoveShape]
        rw [executeInstructions_tailCall_read_register
          (hregisterNoScratch := hregisterNoScratch)]
        exact hsourcePreserved move hmove'
      · simpa [hmoveShape] using
          executeInstructions_tailCall_pc state entry moves hzero

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

theorem executeInstructions_stackCall_prologue_effects [NeZero width]
    (state : State width) (entry : Word width)
    (moves : List (Instruction width)) (hzero : ZeroRegister state) :
    let moved := executeInstructions state moves
    let final := executeInstructions state
      (moves ++
        [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
         .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])
    readRegister final 1 = moved.pc + BitVec.ofNat width 16 ∧
      readRegister final 30 =
        readRegister moved 30 - BitVec.ofNat width (width / 8) ∧
      final.pc = jalrTarget entry 0 := by
  have hzeroMoves : ZeroRegister (executeInstructions state moves) := by
    induction moves generalizing state with
    | nil => exact hzero
    | cons instruction moves ih =>
        exact ih (execute state instruction)
          (execute_zeroRegister_preserved state instruction hzero)
  have hzeroMoves' :
      (executeInstructions state moves).registers 0 = 0 := by
    simpa [ZeroRegister, readRegister] using hzeroMoves
  dsimp
  rw [executeInstructions_append]
  simp [executeInstructions, execute, writeRegister, readRegister,
    nextPc, writeWordValue_registers, jalrTarget, hzeroMoves']
  rw [writeWordValue_pc]
  constructor
  · change (executeInstructions state moves).pc + 4 + 4 + 4 + 4 =
      (executeInstructions state moves).pc + BitVec.ofNat width 16
    calc
      (executeInstructions state moves).pc + 4 + 4 + 4 + 4 =
          (executeInstructions state moves).pc +
            ((4 : BitVec width) + 4 + (4 + 4)) := by ac_rfl
      _ = (executeInstructions state moves).pc +
          (BitVec.ofNat width 8 + BitVec.ofNat width 8) := by
        change (executeInstructions state moves).pc +
            (BitVec.ofNat width 4 + BitVec.ofNat width 4 +
              (BitVec.ofNat width 4 + BitVec.ofNat width 4)) =
          (executeInstructions state moves).pc +
            (BitVec.ofNat width 8 + BitVec.ofNat width 8)
        rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
      _ = (executeInstructions state moves).pc +
          BitVec.ofNat width 16 := by
        rw [show (16 : Nat) = 8 + 8 by omega, BitVec.ofNat_add]
  · simp [BitVec.sub_eq_add_neg]

theorem executeInstructions_stackCall_read_register [NeZero width]
    (state : State width) (entry : Word width)
    (moves : List (Instruction width)) (register : Fin 32)
    (hregisterNoStack : register ≠ 30)
    (hregisterNoScratch : register ≠ 31)
    (hregisterNoLink : register ≠ 1) :
    readRegister (executeInstructions state
      (moves ++
        [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
         .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])) register =
      readRegister (executeInstructions state moves) register := by
  rw [executeInstructions_append]
  simp [executeInstructions, execute, writeRegister, readRegister,
    nextPc, writeWordValue_registers, hregisterNoStack,
    hregisterNoScratch, hregisterNoLink]

theorem wordCallToRiscVWithStack_prefix_execute_parameter_transfer [NeZero width]
    (state : State width) (entry : Word width)
    (parameters returns arguments destinations : List Nat)
    (code : List (Instruction width)) (hzero : ZeroRegister state)
    (hvalid : ∀ move, move ∈ parameters.zip arguments →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hdestNonzero : ∀ move, move ∈ parameters.zip arguments → move.1 ≠ 0)
    (hdestinations : ((parameters.zip arguments).map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ parameters.zip arguments →
      move.2 ∉ (parameters.zip arguments).map Prod.fst)
    (hparameterNoStack : ∀ move, move ∈ parameters.zip arguments →
      move.1 ≠ 30)
    (hparameterNoLink : ∀ move, move ∈ parameters.zip arguments →
      move.1 ≠ 1)
    (hcompile :
      wordCallToRiscVWithStack entry parameters returns arguments destinations =
        some code) :
    ∃ parameterMoves resultMoves,
      wordRegisterMoves (width := width) (parameters.zip arguments) =
        some parameterMoves ∧
      (∀ move (hmove : move ∈ parameters.zip arguments),
        readRegister (executeInstructions state
          (parameterMoves ++
            [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
             .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0]))
            ⟨move.1, (hvalid move hmove).1⟩ =
          readRegister state ⟨move.2, (hvalid move hmove).2.1⟩) ∧
      (executeInstructions state
        (parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])).pc =
        jalrTarget entry 0 ∧
      code = parameterMoves ++
        [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
         .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0] ++ resultMoves := by
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
          have hmoveShape := wordRegisterMoves_shape
            (parameters.zip arguments) parameterMoves hvalid hmove
          have hsourcePreserved := executeWordMoves_preserves_sources state
            (parameters.zip arguments) hdestinations hnoSource hvalid hdestNonzero
          refine ⟨parameterMoves,
            resultMoves ++ [.loadWord 1 30,
              .addi 30 30 (BitVec.ofNat width (width / 8))], by simp, ?_, ?_, ?_⟩
          · intro move hmove'
            have hdestination := hvalid move hmove'
            have hregisterNoStack :
                (⟨move.1, hdestination.1⟩ : Fin 32) ≠ 30 := by
              intro heq
              apply hparameterNoStack move hmove'
              exact congrArg Fin.val heq
            have hregisterNoScratch :
                (⟨move.1, hdestination.1⟩ : Fin 32) ≠ 31 := by
              intro heq
              apply hdestination.2.2.1
              exact congrArg Fin.val heq
            have hregisterNoLink :
                (⟨move.1, hdestination.1⟩ : Fin 32) ≠ 1 := by
              intro heq
              apply hparameterNoLink move hmove'
              exact congrArg Fin.val heq
            rw [hmoveShape]
            rw [executeInstructions_stackCall_read_register
              (hregisterNoStack := hregisterNoStack)
              (hregisterNoScratch := hregisterNoScratch)
              (hregisterNoLink := hregisterNoLink)]
            exact hsourcePreserved move hmove'
          · exact executeInstructions_stackCall_pc state entry parameterMoves hzero
          · simpa [List.cons_append] using hcompile.2.symm

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

theorem executeWordMoves_preserve_memory [NeZero width]
    (state : State width) (moves : List (Nat × Nat))
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31) :
    (executeInstructions state
      (moves.flatMap (wordMoveInstructionList (width := width)))).memory =
        state.memory := by
  induction moves generalizing state with
  | nil => rfl
  | cons head tail ih =>
      have hhead := hvalid head (by simp)
      have htail : ∀ move, move ∈ tail →
          move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31 := by
        intro move hmove
        exact hvalid move (by simp [hmove])
      rw [List.flatMap_cons, executeInstructions_append]
      rw [ih (state := executeInstructions state
        (wordMoveInstructionList (width := width) head)) htail]
      simp [wordMoveInstructionList, wordExpToInstructions,
        wordExpToInstruction, registerOfNat, hhead.1, hhead.2.1,
        execute, writeRegister, readRegister]
      split <;> rfl

theorem executeWordMoves_stackCall_restore_link_sp [NeZero width]
    (state : State width) (stackAddress savedLink : Word width)
    (moves : List (Nat × Nat))
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hdestNonzero : ∀ move, move ∈ moves → move.1 ≠ 0)
    (hnotLink : ∀ move, move ∈ moves → move.1 ≠ 1)
    (hnotStack : ∀ move, move ∈ moves → move.1 ≠ 30)
    (hstack : readRegister state 30 = stackAddress)
    (hsaved : readWordValue state stackAddress = savedLink) :
    let moved := executeInstructions state
      (moves.flatMap (wordMoveInstructionList (width := width)))
    let final := executeInstructions state
      (moves.flatMap (wordMoveInstructionList (width := width)) ++
        [.loadWord 1 30, .addi 30 30 (BitVec.ofNat width (width / 8))])
    readRegister final 1 = savedLink ∧
      readRegister final 30 =
        stackAddress + BitVec.ofNat width (width / 8) ∧
      final.pc = moved.pc + BitVec.ofNat width 8 := by
  have hlink := executeWordMoves_preserve_read state moves 1
    hvalid hdestNonzero (fun move hmove => hnotLink move hmove) (by decide)
  have hstackMove := executeWordMoves_preserve_read state moves 30
    hvalid hdestNonzero (fun move hmove => hnotStack move hmove) (by decide)
  have hstack' :
      readRegister
        (executeInstructions state
          (moves.flatMap (wordMoveInstructionList (width := width)))) 30 =
        stackAddress := by
    calc
      readRegister
          (executeInstructions state
            (moves.flatMap (wordMoveInstructionList (width := width)))) 30 =
          readRegister state 30 := by simpa using hstackMove
      _ = stackAddress := hstack
  have hmemory := executeWordMoves_preserve_memory state moves hvalid
  have hsaved' :
      readWordValue
        (executeInstructions state
          (moves.flatMap (wordMoveInstructionList (width := width))))
        stackAddress = savedLink := by
    simpa [readWordValue, readByte, hmemory] using hsaved
  have hrestore := executeInstructions_stackCall_restore_link_sp
    (executeInstructions state
      (moves.flatMap (wordMoveInstructionList (width := width))))
    stackAddress savedLink hstack' hsaved'
  dsimp
  rw [executeInstructions_append]
  simpa [hlink] using hrestore

theorem wordRegisterMoves_execute_stackCall_restore_link_sp [NeZero width]
    (state : State width) (stackAddress savedLink : Word width)
    (moves : List (Nat × Nat)) (code : List (Instruction width))
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hdestNonzero : ∀ move, move ∈ moves → move.1 ≠ 0)
    (hnotLink : ∀ move, move ∈ moves → move.1 ≠ 1)
    (hnotStack : ∀ move, move ∈ moves → move.1 ≠ 30)
    (hstack : readRegister state 30 = stackAddress)
    (hsaved : readWordValue state stackAddress = savedLink)
    (hcompile : wordRegisterMoves (width := width) moves = some code) :
    let final := executeInstructions state
      (code ++ [.loadWord 1 30,
        .addi 30 30 (BitVec.ofNat width (width / 8))])
    readRegister final 1 = savedLink ∧
      readRegister final 30 =
        stackAddress + BitVec.ofNat width (width / 8) ∧
      final.pc =
        (executeInstructions state code).pc + BitVec.ofNat width 8 := by
  have hshape := wordRegisterMoves_shape moves code hvalid hcompile
  subst code
  simpa using executeWordMoves_stackCall_restore_link_sp state stackAddress savedLink
    moves hvalid hdestNonzero hnotLink hnotStack hstack hsaved

theorem wordCallToRiscVWithStack_full_return_contract [NeZero width]
    (returnState : State width) (stackAddress savedLink entry : Word width)
    (parameters returns arguments destinations : List Nat)
    (code : List (Instruction width))
    (hvalid : ∀ move, move ∈ destinations.zip returns →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hdestNonzero : ∀ move, move ∈ destinations.zip returns → move.1 ≠ 0)
    (hnotLink : ∀ move, move ∈ destinations.zip returns → move.1 ≠ 1)
    (hnotStack : ∀ move, move ∈ destinations.zip returns → move.1 ≠ 30)
    (hstack : readRegister returnState 30 = stackAddress)
    (hsaved : readWordValue returnState stackAddress = savedLink)
    (hcompile : wordCallToRiscVWithStack entry parameters returns arguments destinations =
      some code) :
    ∃ parameterMoves resultMoves,
      code = parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0] ++
          resultMoves ++
          [.loadWord 1 30, .addi 30 30 (BitVec.ofNat width (width / 8))] ∧
      let final := executeInstructions returnState
        (resultMoves ++
          [.loadWord 1 30, .addi 30 30 (BitVec.ofNat width (width / 8))])
      readRegister final 1 = savedLink ∧
        readRegister final 30 =
          stackAddress + BitVec.ofNat width (width / 8) ∧
        final.pc = (executeInstructions returnState resultMoves).pc +
          BitVec.ofNat width 8 := by
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
          have hreturn := wordRegisterMoves_execute_stackCall_restore_link_sp
            returnState stackAddress savedLink (destinations.zip returns)
            resultMoves hvalid hdestNonzero hnotLink hnotStack hstack hsaved hresult
          refine ⟨parameterMoves, resultMoves, ?_, hreturn.1, hreturn.2.1,
            hreturn.2.2⟩
          simpa [List.cons_append, List.append_assoc] using hcompile.2.symm

theorem executeInstructions_stackCall_restore_read_register [NeZero width]
    (state : State width) (register : Fin 32)
    (hregisterNoLink : register ≠ 1)
    (hregisterNoStack : register ≠ 30) :
    readRegister (executeInstructions state
      [.loadWord 1 30, .addi 30 30 (BitVec.ofNat width (width / 8))]) register =
      readRegister state register := by
  simp [executeInstructions, execute, writeRegister, readRegister, nextPc,
    hregisterNoLink, hregisterNoStack]

theorem wordRegisterMoves_execute_stackCall_result_transfer [NeZero width]
    (state : State width) (moves : List (Nat × Nat))
    (code : List (Instruction width))
    (hvalid : ∀ move, move ∈ moves →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hdestNonzero : ∀ move, move ∈ moves → move.1 ≠ 0)
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ moves →
      move.2 ∉ moves.map Prod.fst)
    (hnotLink : ∀ move, move ∈ moves → move.1 ≠ 1)
    (hnotStack : ∀ move, move ∈ moves → move.1 ≠ 30)
    (hcompile : wordRegisterMoves (width := width) moves = some code) :
    ∀ move (hmove : move ∈ moves),
      readRegister (executeInstructions state
        (code ++
          [.loadWord 1 30, .addi 30 30 (BitVec.ofNat width (width / 8))]))
        ⟨move.1, (hvalid move hmove).1⟩ =
      readRegister state ⟨move.2, (hvalid move hmove).2.1⟩ := by
  have hshape := wordRegisterMoves_shape moves code hvalid hcompile
  have hsourcePreserved := executeWordMoves_preserves_sources state moves
    hdestinations hnoSource hvalid hdestNonzero
  subst code
  intro move hmove
  have hdestination := hvalid move hmove
  have hregisterNoLink :
      (⟨move.1, hdestination.1⟩ : Fin 32) ≠ 1 := by
    intro heq
    apply hnotLink move hmove
    exact congrArg Fin.val heq
  have hregisterNoStack :
      (⟨move.1, hdestination.1⟩ : Fin 32) ≠ 30 := by
    intro heq
    apply hnotStack move hmove
    exact congrArg Fin.val heq
  rw [executeInstructions_append]
  rw [executeInstructions_stackCall_restore_read_register
    (hregisterNoLink := hregisterNoLink)
    (hregisterNoStack := hregisterNoStack)]
  exact hsourcePreserved move hmove

theorem wordCallToRiscVWithStack_full_result_contract [NeZero width]
    (state : State width) (entry : Word width)
    (parameters returns arguments destinations : List Nat)
    (code : List (Instruction width))
    (hvalid : ∀ move, move ∈ destinations.zip returns →
      move.1 < 32 ∧ move.2 < 32 ∧ move.1 ≠ 31 ∧ move.2 ≠ 31)
    (hdestNonzero : ∀ move, move ∈ destinations.zip returns → move.1 ≠ 0)
    (hdestinations : ((destinations.zip returns).map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ destinations.zip returns →
      move.2 ∉ (destinations.zip returns).map Prod.fst)
    (hnotLink : ∀ move, move ∈ destinations.zip returns → move.1 ≠ 1)
    (hnotStack : ∀ move, move ∈ destinations.zip returns → move.1 ≠ 30)
    (hcompile :
      wordCallToRiscVWithStack entry parameters returns arguments destinations =
        some code) :
    ∃ parameterMoves resultMoves,
      code = parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat width (width / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0] ++
          resultMoves ++
          [.loadWord 1 30, .addi 30 30 (BitVec.ofNat width (width / 8))] ∧
      ∀ move (hmove : move ∈ destinations.zip returns),
        readRegister (executeInstructions state
          (resultMoves ++
            [.loadWord 1 30, .addi 30 30 (BitVec.ofNat width (width / 8))]))
          ⟨move.1, (hvalid move hmove).1⟩ =
        readRegister state ⟨move.2, (hvalid move hmove).2.1⟩ := by
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
          have hreturn := wordRegisterMoves_execute_stackCall_result_transfer
            state (destinations.zip returns) resultMoves hvalid hdestNonzero
            hdestinations hnoSource hnotLink hnotStack hresult
          refine ⟨parameterMoves, resultMoves, ?_, hreturn⟩
          simpa [List.cons_append, List.append_assoc] using hcompile.2.symm

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
