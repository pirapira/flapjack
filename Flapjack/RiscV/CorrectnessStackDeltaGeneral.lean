import Flapjack.RiscV.CorrectnessStack

/-!
# Arbitrary-size StackRemove frame deltas

The StackRemove pass splits large frame deltas into 255-word chunks.  This
theorem lifts the one-chunk evaluator contract to that recursive lowering.
-/

namespace Flapjack.RiscV

theorem stackRemoveJoin_eq_seq_of_ne_skip {α} {first second : StackProg α}
    (hfirst : first ≠ .skip) (hsecond : second ≠ .skip) :
    stackRemoveJoin first second = .seq first second := by
  cases first <;> cases second <;> simp only [stackRemoveJoin] <;>
    try contradiction

theorem stackRemoveStackAlloc_ne_skip
    (config : StackRemoveConfig) :
    ∀ words, words ≠ 0 →
      (stackRemoveStackAlloc config words : StackProg Nat) ≠ .skip := by
  intro words
  induction words using Nat.strongRecOn with
  | ind words ih =>
      intro hwords
      by_cases hsmall : words ≤ 255
      · rw [stackRemoveStackAlloc, stackRemoveStackDelta]
        rw [if_neg hwords, if_pos hsmall]
        simp [stackRemoveJoin]
      · have htail : words - 255 ≠ 0 := by omega
        have htail' := ih (words - 255) (by omega) htail
        have hfirst' :
            (stackRemoveStackDelta config .sub 255 : StackProg Nat) ≠ .skip := by
          rw [stackRemoveStackDelta]
          rw [if_neg (by decide), if_pos (by decide)]
          simp [stackRemoveJoin]
        have htailDelta :
            (stackRemoveStackDelta config .sub (words - 255) : StackProg Nat) ≠ .skip := by
          change stackRemoveStackAlloc config (words - 255) ≠ .skip
          exact htail'
        rw [stackRemoveStackAlloc, stackRemoveStackDelta]
        rw [if_neg hwords, if_neg hsmall]
        rw [stackRemoveJoin_eq_seq_of_ne_skip hfirst' htailDelta]
        intro hjoin
        cases hjoin

theorem evalStackRemoveStackAlloc_all [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (words : Nat)
    (hscratch : config.scratch ≠ config.stackPointer) :
    (evalWordStackMachine state
      (stackRemoveStackAlloc config words)).map
        (fun final => final.registers config.stackPointer) =
      some (state.registers config.stackPointer -
        BitVec.ofNat width (config.bytesInWord * words)) := by
  induction words using Nat.strongRecOn generalizing state with
  | ind words ih =>
      by_cases hsmall : words ≤ 255
      · exact evalStackRemoveStackAlloc_small config state words hsmall hscratch
      · have htail : words - 255 < words := by omega
        let afterChunk :=
          wordStackMachineWriteRegister
            (wordStackMachineWriteRegister state config.scratch
              (BitVec.ofNat width (config.bytesInWord * 255)))
            config.stackPointer
            (state.registers config.stackPointer -
              BitVec.ofNat width (config.bytesInWord * 255))
        have htailEval := ih (words - 255) htail afterChunk
        have hwordsNonzero : words ≠ 0 := by omega
        have hdelta :
            (stackRemoveStackAlloc config words : StackProg Nat) =
              stackRemoveJoin
                (stackRemoveStackAlloc config 255 : StackProg Nat)
                (stackRemoveStackAlloc config (words - 255) : StackProg Nat) := by
          change stackRemoveStackDelta config .sub words =
            stackRemoveJoin
              (stackRemoveStackDelta config .sub 255)
              (stackRemoveStackDelta config .sub (words - 255))
          rw [stackRemoveStackDelta]
          rw [if_neg hwordsNonzero, if_neg hsmall]
        have hfirstNe :
            (stackRemoveStackAlloc config 255 : StackProg Nat) ≠ .skip :=
          stackRemoveStackAlloc_ne_skip config 255 (by decide)
        have htailNe :
            (stackRemoveStackAlloc config (words - 255) : StackProg Nat) ≠ .skip :=
          stackRemoveStackAlloc_ne_skip config (words - 255) (by omega)
        have hjoin :
            stackRemoveJoin
                (stackRemoveStackAlloc config 255 : StackProg Nat)
                (stackRemoveStackAlloc config (words - 255) : StackProg Nat) =
              .seq
                (stackRemoveStackAlloc config 255)
                (stackRemoveStackAlloc config (words - 255)) :=
          stackRemoveJoin_eq_seq_of_ne_skip hfirstNe htailNe
        have hfirst :
            evalWordStackMachine state
                (stackRemoveStackAlloc config 255) =
              some afterChunk := by
          simp [stackRemoveStackAlloc, stackRemoveStackDelta,
            stackRemoveJoin, evalWordStackMachine, wordStackMachineBinOp,
            wordStackMachineWriteRegister, afterChunk, Ne.symm hscratch]
        rw [hdelta]
        rw [hjoin]
        simp only [evalWordStackMachine]
        rw [hfirst]
        have hwordsNat :
            config.bytesInWord * 255 + config.bytesInWord * (words - 255) =
              config.bytesInWord * words := by
          rw [← Nat.mul_add]
          rw [show 255 + (words - 255) = words by omega]
        have hbits :
            state.registers config.stackPointer -
                BitVec.ofNat width (config.bytesInWord * 255) -
                BitVec.ofNat width (config.bytesInWord * (words - 255)) =
              state.registers config.stackPointer -
                BitVec.ofNat width (config.bytesInWord * words) := by
          rw [BitVec.sub_sub]
          rw [← BitVec.ofNat_add, hwordsNat]
        have hafter :
            afterChunk.registers config.stackPointer =
              state.registers config.stackPointer -
                BitVec.ofNat width (config.bytesInWord * 255) := by
          simp [afterChunk, wordStackMachineWriteRegister]
        rw [hafter, hbits] at htailEval
        exact htailEval

theorem stackRemoveStackFree_ne_skip
    (config : StackRemoveConfig) :
    ∀ words, words ≠ 0 →
      (stackRemoveStackFree config words : StackProg Nat) ≠ .skip := by
  intro words
  induction words using Nat.strongRecOn with
  | ind words ih =>
      intro hwords
      by_cases hsmall : words ≤ 255
      · rw [stackRemoveStackFree, stackRemoveStackDelta]
        rw [if_neg hwords, if_pos hsmall]
        simp [stackRemoveJoin]
      · have htail : words - 255 ≠ 0 := by omega
        have htail' := ih (words - 255) (by omega) htail
        have hfirst' :
            (stackRemoveStackDelta config .add 255 : StackProg Nat) ≠ .skip := by
          rw [stackRemoveStackDelta]
          rw [if_neg (by decide), if_pos (by decide)]
          simp [stackRemoveJoin]
        have htailDelta :
            (stackRemoveStackDelta config .add (words - 255) : StackProg Nat) ≠ .skip := by
          change stackRemoveStackFree config (words - 255) ≠ .skip
          exact htail'
        rw [stackRemoveStackFree, stackRemoveStackDelta]
        rw [if_neg hwords, if_neg hsmall]
        rw [stackRemoveJoin_eq_seq_of_ne_skip hfirst' htailDelta]
        intro hjoin
        cases hjoin

theorem evalStackRemoveStackFree_all [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (words : Nat)
    (hscratch : config.scratch ≠ config.stackPointer) :
    (evalWordStackMachine state
      (stackRemoveStackFree config words)).map
        (fun final => final.registers config.stackPointer) =
      some (state.registers config.stackPointer +
        BitVec.ofNat width (config.bytesInWord * words)) := by
  induction words using Nat.strongRecOn generalizing state with
  | ind words ih =>
      by_cases hsmall : words ≤ 255
      · exact evalStackRemoveStackFree_small config state words hsmall hscratch
      · have htail : words - 255 < words := by omega
        let afterChunk :=
          wordStackMachineWriteRegister
            (wordStackMachineWriteRegister state config.scratch
              (BitVec.ofNat width (config.bytesInWord * 255)))
            config.stackPointer
            (state.registers config.stackPointer +
              BitVec.ofNat width (config.bytesInWord * 255))
        have htailEval := ih (words - 255) htail afterChunk
        have hwordsNonzero : words ≠ 0 := by omega
        have hdelta :
            (stackRemoveStackFree config words : StackProg Nat) =
              stackRemoveJoin
                (stackRemoveStackFree config 255 : StackProg Nat)
                (stackRemoveStackFree config (words - 255) : StackProg Nat) := by
          change stackRemoveStackDelta config .add words =
            stackRemoveJoin
              (stackRemoveStackDelta config .add 255)
              (stackRemoveStackDelta config .add (words - 255))
          rw [stackRemoveStackDelta]
          rw [if_neg hwordsNonzero, if_neg hsmall]
        have hfirstNe :
            (stackRemoveStackFree config 255 : StackProg Nat) ≠ .skip :=
          stackRemoveStackFree_ne_skip config 255 (by decide)
        have htailNe :
            (stackRemoveStackFree config (words - 255) : StackProg Nat) ≠ .skip :=
          stackRemoveStackFree_ne_skip config (words - 255) (by omega)
        have hjoin :
            stackRemoveJoin
                (stackRemoveStackFree config 255 : StackProg Nat)
                (stackRemoveStackFree config (words - 255) : StackProg Nat) =
              .seq
                (stackRemoveStackFree config 255)
                (stackRemoveStackFree config (words - 255)) :=
          stackRemoveJoin_eq_seq_of_ne_skip hfirstNe htailNe
        have hfirst :
            evalWordStackMachine state
                (stackRemoveStackFree config 255) =
              some afterChunk := by
          simp [stackRemoveStackFree, stackRemoveStackDelta,
            stackRemoveJoin, evalWordStackMachine, wordStackMachineBinOp,
            wordStackMachineWriteRegister, afterChunk, Ne.symm hscratch]
        rw [hdelta]
        rw [hjoin]
        simp only [evalWordStackMachine]
        rw [hfirst]
        have hwordsNat :
            config.bytesInWord * 255 + config.bytesInWord * (words - 255) =
              config.bytesInWord * words := by
          rw [← Nat.mul_add]
          rw [show 255 + (words - 255) = words by omega]
        have hbits :
            state.registers config.stackPointer +
                BitVec.ofNat width (config.bytesInWord * 255) +
                BitVec.ofNat width (config.bytesInWord * (words - 255)) =
              state.registers config.stackPointer +
                BitVec.ofNat width (config.bytesInWord * words) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, hwordsNat]
        have hafter :
            afterChunk.registers config.stackPointer =
              state.registers config.stackPointer +
                BitVec.ofNat width (config.bytesInWord * 255) := by
          simp [afterChunk, wordStackMachineWriteRegister]
        rw [hafter, hbits] at htailEval
        exact htailEval

end Flapjack.RiscV
