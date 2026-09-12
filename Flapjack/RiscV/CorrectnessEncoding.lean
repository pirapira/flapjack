import Flapjack.RiscV.Encoding

/-!
Correctness properties for the concrete RISC-V artifact boundary.

The encoder emits one four-byte little-endian word per typed instruction.
These lemmas make that representation-preservation fact available to the
later source-to-machine correctness theorem without unfolding instruction
encodings at each use site.
-/

namespace Flapjack.RiscV

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
