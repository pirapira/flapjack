import Flapjack.RiscV.PanMemory

namespace Flapjack

open RiscV

def riscvFlatTestDomain : PanMemoryDomain (RiscV.Word 64) :=
  fun address => address == 8

def riscvFlatTestMemory : PanFlatMemory (RiscV.Word 64) :=
  fun address =>
    if address == 8 then some (BitVec.ofNat 64 67305985) else none

def riscvFlatZeroMemory : PanFlatMemory (RiscV.Word 64) :=
  fun address => if address == 8 then some 0 else none

example :
    panRiscVReadByte riscvFlatTestDomain riscvFlatTestMemory
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 9) =
      some (BitVec.ofNat 64 2) := by
  native_decide

example :
    panRiscVRead32 riscvFlatTestDomain riscvFlatTestMemory
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) =
      some (BitVec.ofNat 64 67305985) := by
  native_decide

example :
    (do
      let memory ← panRiscVStore32 riscvFlatTestDomain riscvFlatZeroMemory
        (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) (BitVec.ofNat 64 67305985)
      panRiscVRead32 riscvFlatTestDomain memory
        (BitVec.ofNat 64 8) (BitVec.ofNat 64 8)) =
      some (BitVec.ofNat 64 67305985) := by
  native_decide

example :
    panRiscVRead32 riscvFlatTestDomain riscvFlatTestMemory
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 2) = none := by
  native_decide

example :
    panRiscVRead16 riscvFlatTestDomain riscvFlatTestMemory
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) =
      some (BitVec.ofNat 64 513) := by
  native_decide

example :
    (do
      let memory ← panRiscVStore16 riscvFlatTestDomain riscvFlatZeroMemory
        (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) (BitVec.ofNat 64 48879)
      panRiscVRead16 riscvFlatTestDomain memory
        (BitVec.ofNat 64 8) (BitVec.ofNat 64 8)) =
      some (BitVec.ofNat 64 48879) := by
  native_decide

example :
    evalPanRiscVFlatResult [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      riscvFlatTestDomain riscvFlatZeroMemory
      (.seq (.store32 (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 67305985)))
        (.return (.load32 (.const (BitVec.ofNat 64 8))))) =
      some [.word (BitVec.ofNat 64 67305985)] := by
  simp [evalPanRiscVFlatResult, evalPanRiscVFlatProg, evalPanRiscVFlatExp,
    panRiscVStore32, panRiscVStoreByte, panRiscVRead32, panRiscVReadByte,
    panRiscVGetByte, panRiscVSetByte, panRiscVByteAlign, panRiscVByteIndex,
    riscvFlatTestDomain, riscvFlatZeroMemory, updatePanValueMap, byteAddress,
    aligned]

example :
    evalPanRiscVFlatResult [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      riscvFlatTestDomain riscvFlatZeroMemory
      (.seq (.storeByte (.const (BitVec.ofNat 64 9))
          (.const (BitVec.ofNat 64 7)))
        (.return (.loadByte (.const (BitVec.ofNat 64 9))))) =
    some [.word (BitVec.ofNat 64 7)] := by
  simp [evalPanRiscVFlatResult, evalPanRiscVFlatProg, evalPanRiscVFlatExp,
    panRiscVStoreByte, panRiscVReadByte, panRiscVGetByte, panRiscVSetByte,
    panRiscVByteAlign, panRiscVByteIndex, riscvFlatTestDomain,
    riscvFlatZeroMemory, updatePanValueMap, byteAddress, aligned]

example :
    evalPanRiscVFlatResult [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      riscvFlatTestDomain riscvFlatTestMemory
      (.seq (.shMemLoad .op16 .local "x" (.const (BitVec.ofNat 64 8)))
        (.return (.var .local "x"))) =
      some [.word (BitVec.ofNat 64 513)] := by
  simp [evalPanRiscVFlatResult, evalPanRiscVFlatProg,
    evalPanRiscVFlatExp, panRiscVReadShared, panRiscVRead16,
    panRiscVReadByte, panRiscVGetByte, panRiscVByteAlign,
    panRiscVByteIndex, riscvFlatTestDomain, riscvFlatTestMemory,
    updatePanValueMap, byteAddress, aligned]

example :
    evalPanRiscVFlatResult [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      riscvFlatTestDomain riscvFlatZeroMemory
      (.seq (.shMemStore .op16 (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 48879)))
        (.seq (.shMemLoad .op16 .local "x" (.const (BitVec.ofNat 64 8)))
          (.return (.var .local "x")))) =
      some [.word (BitVec.ofNat 64 48879)] := by
  simp [evalPanRiscVFlatResult, evalPanRiscVFlatProg,
    evalPanRiscVFlatExp, panRiscVReadShared, panRiscVRead16,
    panRiscVReadByte, panRiscVGetByte, panRiscVByteAlign,
    panRiscVByteIndex, panRiscVStoreShared, panRiscVStore16,
    panRiscVStoreByte, panRiscVSetByte, riscvFlatTestDomain,
    riscvFlatZeroMemory, updatePanValueMap, byteAddress, aligned]

end Flapjack
