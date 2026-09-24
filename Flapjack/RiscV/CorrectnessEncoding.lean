import Flapjack.RiscV.Encoding

/-!
Correctness properties for the concrete RISC-V artifact boundary.

The encoder emits one four-byte little-endian word per typed instruction.
These lemmas make that representation-preservation fact available to the
later source-to-machine correctness theorem without unfolding instruction
encodings at each use site.
-/
namespace Flapjack.RiscV

/-! HOL `riscv_targetProof$word_extract_6` states that when a 64-bit word is
    below 64, its low six-bit slice equals its 6-bit truncation (`w2w`).  HOL
    unsigned `<+` is the `toNat` bound here, slicing `(5 >< 0)` is extraction
    from bit 0 with length 6, and `w2w` retains the low six bits. -/
@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "word_extract_6"]
theorem wordExtract6OfLt64 (word : BitVec 64) (_hword : word.toNat < 64) :
    BitVec.extractLsb' 0 6 word = BitVec.setWidth 6 word := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth]

/-! Cake's `riscv_encoding` target contract: every encoded instruction is a
    nonempty four-byte artifact.

    HOL's `riscv_encoder_correct` (`riscv_targetProofScript.sml:512`) is much
    stronger: it proves `encoder_correct riscv_target`, whose premise is a HOL
    `asm_step` related to a target machine state and whose conclusion gives a
    target-state simulation under interference, byte-preservation, and code-PC
    invariants (`asmPropsScript.sml:117-130`). The current Lean `Model.execute`
    consumes an already-decoded `Instruction`; it has no encoded-byte fetch /
    decode step or corresponding HOL `target_state_rel`. Thus the byte-length
    lemmas below are untagged support, not ports of `riscv_encoder_correct`.
    Add the tag only after the production encoded bytes are connected to a
    faithful target-state step theorem. -/

theorem encodeInstructionBytes_mod_four [NeZero width]
    (instruction : Instruction width) :
    (encodeInstructionBytes instruction).length % 4 = 0 := by
  simp [encodeInstructionBytes_length]

theorem encodeInstructionBytes_ne_nil [NeZero width]
    (instruction : Instruction width) :
    encodeInstructionBytes instruction ≠ [] := by
  simp [encodeInstructionBytes, encodeWordBytes]

theorem encodeInstructions_mod_four [NeZero width]
    (instructions : List (Instruction width)) :
    (encodeInstructions instructions).length % 4 = 0 := by
  simp [encodeInstructions_length]

theorem encodeInstructions_ne_nil [NeZero width]
    {instructions : List (Instruction width)}
    (h : instructions ≠ []) :
    encodeInstructions instructions ≠ [] := by
  cases instructions with
  | nil => contradiction
  | cons instruction instructions =>
      simp [encodeInstructions, encodeInstructionBytes, encodeWordBytes]

@[simp] theorem encodeLinkedSections_length [NeZero width]
    (sections : List (Nat × Word width × List (Instruction width))) :
    (encodeLinkedSections sections).length = sections.length := by
  induction sections with
  | nil => rfl
  | cons sourceSection sections induction =>
      cases sourceSection with
      | mk label rest =>
        cases rest with
        | mk address instructions =>
          simp [encodeLinkedSections, induction]

theorem encodeLinkedSections_labels_addresses [NeZero width]
    (sections : List (Nat × Word width × List (Instruction width))) :
    (encodeLinkedSections sections).map (fun encodedSection =>
      (encodedSection.label, encodedSection.address)) =
      sections.map (fun sourceSection => (sourceSection.1, sourceSection.2.1)) := by
  induction sections with
  | nil => rfl
  | cons sourceSection sections induction =>
      cases sourceSection with
      | mk label rest =>
        cases rest with
        | mk address instructions =>
          simp [encodeLinkedSections, induction]

theorem encodeLinkedSections_byte_lengths [NeZero width]
    (sections : List (Nat × Word width × List (Instruction width))) :
    (encodeLinkedSections sections).map
        (fun encodedSection => encodedSection.bytes.length) =
      sections.map (fun sourceSection => 4 * sourceSection.2.2.length) := by
  induction sections with
  | nil => rfl
  | cons sourceSection sections induction =>
      cases sourceSection with
      | mk label rest =>
        cases rest with
        | mk address instructions =>
          simp [encodeLinkedSections, encodeInstructions_length, induction]

end Flapjack.RiscV
