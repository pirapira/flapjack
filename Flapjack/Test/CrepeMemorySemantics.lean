import Flapjack.CrepeSemantics
import Flapjack.RiscV.PanMemory

/-!
Focused executable checks for the canonical Crepe word-cell memory boundary.

The checked operations correspond to `mem_load`, `mem_store`,
`mem_load_32`, `mem_store_32`, `mem_load_byte`, and `mem_store_byte` in
`cakeml/pancake/semantics/crepSemScript.sml` and `panSemScript.sml`.
-/

namespace Flapjack

def checkedMemoryDomain : PanWordMemoryDomain (RiscV.Word 64) :=
  fun address => address == BitVec.ofNat 64 8

def checkedMemory : PanWordMemory (RiscV.Word 64) :=
  fun address =>
    if address == BitVec.ofNat 64 8 then
      some (BitVec.ofNat 64 0x0807060504030201)
    else none

def checkedMemoryState : CrepMemoryState (RiscV.Word 64) :=
  { memory := checkedMemory
    memaddrs := checkedMemoryDomain
    bytesInWord := BitVec.ofNat 64 8
    bigEndian := false
    model := RiscV.panRiscVMemoryModel }

def checkedWordLoad : Option (RiscV.Word 64) :=
  crepMemLoad checkedMemoryState (BitVec.ofNat 64 8)

def checkedWordLoadOutsideDomain : Option (RiscV.Word 64) :=
  crepMemLoad checkedMemoryState (BitVec.ofNat 64 16)

def checkedWordStore : Option (CrepMemoryState (RiscV.Word 64)) :=
  crepMemStore checkedMemoryState (BitVec.ofNat 64 8)
    (BitVec.ofNat 64 0xaa)

def checkedWordStoreOutsideDomain : Option (CrepMemoryState (RiscV.Word 64)) :=
  crepMemStore checkedMemoryState (BitVec.ofNat 64 16)
    (BitVec.ofNat 64 0xaa)

def checkedByteLoad : Option (RiscV.Word 64) :=
  crepMemLoadByte checkedMemoryState (BitVec.ofNat 64 9)

def checkedByteLoadUnaligned : Option (RiscV.Word 64) :=
  crepMemLoad32 checkedMemoryState (BitVec.ofNat 64 9)

def checkedByteStore : Option (CrepMemoryState (RiscV.Word 64)) :=
  crepMemStoreByte checkedMemoryState (BitVec.ofNat 64 9)
    (BitVec.ofNat 64 0xaa)

def checkedWord32Store : Option (CrepMemoryState (RiscV.Word 64)) :=
  crepMemStore32 checkedMemoryState (BitVec.ofNat 64 8)
    (BitVec.ofNat 64 0x11223344)

#guard checkedWordLoad = some (BitVec.ofNat 64 0x0807060504030201)
#guard checkedWordLoadOutsideDomain = none
#guard checkedWordStoreOutsideDomain = none
#guard checkedByteLoad = some (BitVec.ofNat 64 2)
#guard checkedByteLoadUnaligned = none
#guard checkedByteStore.isSome
#guard checkedWord32Store.isSome

theorem checkedWordLoad_outside_domain :
    checkedWordLoadOutsideDomain = none := by
  simp [checkedWordLoadOutsideDomain, crepMemLoad, panModelReadWord,
    checkedMemoryState, checkedMemoryDomain]

theorem checkedWordStore_outside_domain :
    checkedWordStoreOutsideDomain = none := by
  simp [checkedWordStoreOutsideDomain, crepMemStore, panModelStoreWord,
    checkedMemoryState, checkedMemoryDomain]

end Flapjack
