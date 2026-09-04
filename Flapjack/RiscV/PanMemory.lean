import Flapjack.PanMemory
import Flapjack.RiscV.Model

/-!
RISC-V byte-addressed operations for CakeML-style flat memory.

CakeML's Pancake memory stores one machine word per aligned cell, while
loadByte and load32 address individual bytes within that cell.  The
RISC-V backend uses little-endian memory, so this adapter makes that
representation explicit over PanFlatMemory (Word width).
-/

namespace Flapjack.RiscV

def panRiscVByteAlign [NeZero width]
    (bytesInWord address : Word width) : Word width :=
  let bytes := bytesInWord.toNat
  if bytes = 0 then address
  else BitVec.ofNat width ((address.toNat / bytes) * bytes)

def panRiscVByteIndex [NeZero width]
    (bytesInWord address : Word width) : Nat :=
  let bytes := bytesInWord.toNat
  if bytes = 0 then 0 else address.toNat % bytes

def panRiscVGetByte [NeZero width]
    (bytesInWord address value : Word width) : Word width :=
  let offset := 256 ^ panRiscVByteIndex bytesInWord address
  BitVec.ofNat width ((value.toNat / offset) % 256)

def panRiscVSetByte [NeZero width]
    (bytesInWord address byte value : Word width) : Word width :=
  let offset := 256 ^ panRiscVByteIndex bytesInWord address
  let block := offset * 256
  let low := value.toNat % offset
  let high := value.toNat / block
  BitVec.ofNat width
    (low + (byte.toNat % 256) * offset + high * block)

def panRiscVReadByte [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address : Word width) : Option (Word width) :=
  let alignedAddress := panRiscVByteAlign bytesInWord address
  if domain alignedAddress then
    (memory alignedAddress).map
      (panRiscVGetByte bytesInWord address)
  else none

def panRiscVRead32 [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address : Word width) : Option (Word width) :=
  if aligned address 4 then do
    let byte0 ← panRiscVReadByte domain memory bytesInWord address
    let byte1 ← panRiscVReadByte domain memory bytesInWord
      (byteAddress address 1)
    let byte2 ← panRiscVReadByte domain memory bytesInWord
      (byteAddress address 2)
    let byte3 ← panRiscVReadByte domain memory bytesInWord
      (byteAddress address 3)
    pure (BitVec.ofNat width
      (byte0.toNat + 256 * byte1.toNat +
        256 ^ 2 * byte2.toNat + 256 ^ 3 * byte3.toNat))
  else none

def panRiscVStoreByte [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address byte : Word width) :
    Option (PanFlatMemory (Word width)) :=
  let alignedAddress := panRiscVByteAlign bytesInWord address
  if domain alignedAddress then do
    let value ← memory alignedAddress
    pure (updatePanValueMap memory alignedAddress
      (panRiscVSetByte bytesInWord address byte value))
  else none

def panRiscVStore32 [NeZero width]
    (domain : PanMemoryDomain (Word width))
    (memory : PanFlatMemory (Word width))
    (bytesInWord address value : Word width) :
    Option (PanFlatMemory (Word width)) :=
  if aligned address 4 then do
    let byte0 := BitVec.ofNat width (value.toNat % 256)
    let byte1 := BitVec.ofNat width (value.toNat / 256 % 256)
    let byte2 := BitVec.ofNat width (value.toNat / 256 ^ 2 % 256)
    let byte3 := BitVec.ofNat width (value.toNat / 256 ^ 3 % 256)
    let memory ← panRiscVStoreByte domain memory bytesInWord address byte0
    let memory ← panRiscVStoreByte domain memory bytesInWord
      (byteAddress address 1) byte1
    let memory ← panRiscVStoreByte domain memory bytesInWord
      (byteAddress address 2) byte2
    panRiscVStoreByte domain memory bytesInWord
      (byteAddress address 3) byte3
  else none

end Flapjack.RiscV
