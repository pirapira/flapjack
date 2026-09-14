import Flapjack.PanValueFfiSemantics

/-!
# Pancake `panSem.write_bytearray`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:309-316`.

The active source definition recurses on the tail first, stores the current
byte with `mem_store_byte`, and falls back to the original memory on failure.
This boundary uses the same `PanValueMemoryAccess.storeByte` contract.
-/

namespace Flapjack

def panSemWriteBytearray [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord address : α) :
    List UInt8 → (α → Option (PanValue α))
  | [] => memory
  | byte :: bytes =>
      let tailMemory := panSemWriteBytearray access context memory bytesInWord
        (address + 1) bytes
      match access.storeByte access.domain tailMemory bytesInWord address
          (context.byteToWord byte) with
      | some updatedMemory => updatedMemory
      | none => memory
termination_by bytes => sizeOf bytes

end Flapjack
