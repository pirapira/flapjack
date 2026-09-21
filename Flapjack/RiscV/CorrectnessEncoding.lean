import Flapjack.RiscV.Encoding

/-!
Correctness properties for the concrete RISC-V artifact boundary.

The encoder emits one four-byte little-endian word per typed instruction.
These lemmas make that representation-preservation fact available to the
later source-to-machine correctness theorem without unfolding instruction
encodings at each use site.
-/
namespace Flapjack.RiscV

/-! Cake's `riscv_encoding` target contract: every encoded instruction is a
    nonempty four-byte artifact. -/

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
