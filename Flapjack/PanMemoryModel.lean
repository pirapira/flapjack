import Flapjack.Language

/-!
Common executable operations for the Pancake word-cell memory model.

CakeML stores one machine word at each aligned cell.  Byte and 32-bit
operations address bytes within that cell, while ordinary word operations use
the address directly.  This interface keeps those rules independent of the
particular word implementation and makes endianness explicit.  The RISC-V
adapter supplies the concrete instance used by the target proofs.
-/

namespace Flapjack

structure PanMemoryModel (α : Type u) where
  /-- Align a byte address to the containing word cell. -/
  byteAlign : α → α → α
  /-- Extract one byte from a word value at a byte address. -/
  getByte : α → α → α → Bool → α
  /-- Replace one byte in a word value at a byte address. -/
  setByte : α → α → α → α → Bool → α
  /-- Check alignment in bytes. -/
  aligned : Nat → α → Bool
  /-- Decode a byte list using the source endianness convention. -/
  wordOfBytes : Bool → List α → α

abbrev PanWordMemory (α : Type u) := α → Option α
abbrev PanWordMemoryDomain (α : Type u) := α → Bool

def panModelReadWord
    (domain : PanWordMemoryDomain α) (memory : PanWordMemory α)
    (address : α) : Option α :=
  if domain address then memory address else none

def panModelUpdateMemory [BEq α] (memory : PanWordMemory α)
    (address value : α) : PanWordMemory α :=
  fun current => if current == address then some value else memory current

def panModelReadByte [Add α] [OfNat α 1]
    (model : PanMemoryModel α)
    (domain : PanWordMemoryDomain α) (memory : PanWordMemory α)
    (bytesInWord address : α) (bigEndian : Bool) : Option α :=
  let alignedAddress := model.byteAlign bytesInWord address
  if domain alignedAddress then do
    let value ← memory alignedAddress
    pure (model.getByte bytesInWord address value bigEndian)
  else none

def panModelRead32 [Add α] [OfNat α 1] [OfNat α 2] [OfNat α 3]
    (model : PanMemoryModel α)
    (domain : PanWordMemoryDomain α) (memory : PanWordMemory α)
    (bytesInWord address : α) (bigEndian : Bool) : Option α :=
  if model.aligned 4 address then
    let alignedAddress := model.byteAlign bytesInWord address
    if domain alignedAddress then do
      let value ← memory alignedAddress
      pure (model.wordOfBytes bigEndian
        [model.getByte bytesInWord address value bigEndian,
         model.getByte bytesInWord (address + 1) value bigEndian,
         model.getByte bytesInWord (address + 2) value bigEndian,
         model.getByte bytesInWord (address + 3) value bigEndian])
    else none
  else none

def panModelStoreByte [BEq α] [Add α] [OfNat α 1]
    (model : PanMemoryModel α)
    (domain : PanWordMemoryDomain α) (memory : PanWordMemory α)
    (bytesInWord address byte : α) (bigEndian : Bool) :
    Option (PanWordMemory α) :=
  let alignedAddress := model.byteAlign bytesInWord address
  if domain alignedAddress then do
    let value ← memory alignedAddress
    pure (panModelUpdateMemory memory alignedAddress
      (model.setByte bytesInWord address byte value bigEndian))
  else none

def panModelStore32 [BEq α] [Add α] [OfNat α 0] [OfNat α 1]
    [OfNat α 2] [OfNat α 3]
    (model : PanMemoryModel α)
    (domain : PanWordMemoryDomain α) (memory : PanWordMemory α)
    (bytesInWord address value : α) (bigEndian : Bool) :
    Option (PanWordMemory α) :=
  if model.aligned 4 address then
    let alignedAddress := model.byteAlign bytesInWord address
    if domain alignedAddress then do
      let cell ← memory alignedAddress
      let cell0 := model.setByte bytesInWord address
        (model.getByte bytesInWord 0 value bigEndian) cell bigEndian
      let cell1 := model.setByte bytesInWord (address + 1)
        (model.getByte bytesInWord 1 value bigEndian) cell0 bigEndian
      let cell2 := model.setByte bytesInWord (address + 2)
        (model.getByte bytesInWord 2 value bigEndian) cell1 bigEndian
      let cell3 := model.setByte bytesInWord (address + 3)
        (model.getByte bytesInWord 3 value bigEndian) cell2 bigEndian
      pure (panModelUpdateMemory memory alignedAddress cell3)
    else none
  else none

def panModelStoreWord [BEq α]
    (domain : PanWordMemoryDomain α) (memory : PanWordMemory α)
    (address value : α) : Option (PanWordMemory α) :=
  if domain address then some (panModelUpdateMemory memory address value) else none

end Flapjack
