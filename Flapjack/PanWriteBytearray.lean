import Flapjack.PanValues

/-!
# Pancake `mem_store_byte` and `write_bytearray`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:300-314`.

`write_bytearray` deliberately writes the tail first and then the current
byte.  On a failed byte store the source definition returns the memory passed
to that invocation, rather than an option-valued failure.  Keeping those two
details explicit avoids silently replacing the Pancake behavior with the
alternative commented-out definition at lines 318-323.
-/

namespace Flapjack

def panSemMemStoreByte [BEq α] [Add α] [OfNat α 1]
    (model : PanMemoryModel α) (memory : α → Option (PanValue α))
    (domain : α → Bool) (bytesInWord address byte : α) (bigEndian : Bool) :
    Option (α → Option (PanValue α)) :=
  let alignedAddress := model.byteAlign bytesInWord address
  match memory alignedAddress with
  | some (.word value) =>
      if domain alignedAddress then
        some (updatePanValueMemory memory alignedAddress
          (.word (model.setByte bytesInWord address byte value bigEndian)))
      else none
  | _ => none

def panSemWriteBytearray [BEq α] [Add α] [OfNat α 1]
    (model : PanMemoryModel α) (address : α) :
    List α → (α → Option (PanValue α)) → (α → Bool) → α → Bool →
      (α → Option (PanValue α))
  | [], memory, _, _, _ => memory
  | byte :: rest, memory, domain, bytesInWord, bigEndian =>
      let tailMemory := panSemWriteBytearray model (address + 1) rest
        memory domain bytesInWord bigEndian
      match panSemMemStoreByte model tailMemory domain bytesInWord address byte bigEndian with
      | some updatedMemory => updatedMemory
      | none => memory
  termination_by bytes => sizeOf bytes
  decreasing_by simp_wf

@[simp] theorem panSemWriteBytearray_nil [BEq α] [Add α] [OfNat α 1]
    (model : PanMemoryModel α) (address : α)
    (memory : α → Option (PanValue α)) (domain : α → Bool)
    (bytesInWord : α) (bigEndian : Bool) :
    panSemWriteBytearray model address [] memory domain bytesInWord bigEndian = memory := by
  simp [panSemWriteBytearray]

end Flapjack
