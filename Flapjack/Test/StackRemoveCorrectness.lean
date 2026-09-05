import Flapjack.RiscV.CorrectnessStack

namespace Flapjack.RiscV

def stackGetCorrectnessConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def stackGetCorrectnessState : WordStackMachineState 64 :=
  { registers := fun register =>
      if register = 10 then BitVec.ofNat 64 100
      else if register = 6 then BitVec.ofNat 64 55 else 0
    stack := fun _ => 0
    stores := fun store =>
      if store = .heapLength then BitVec.ofNat 64 77 else 0
    memory := fun address =>
      if address = BitVec.ofNat 64 103 then BitVec.ofNat 64 77 else 0
    sharedMemory := fun _ => 0 }

example :
    (evalWordStackMachine stackGetCorrectnessState
      (stackRemoveGet stackGetCorrectnessConfig 4 .heapLength)).map
        (fun final => final.registers 4) =
      some (BitVec.ofNat 64 77) := by
  apply evalStackRemoveGet
  · simp
  · simp [stackGetCorrectnessConfig]
  · simp [stackGetCorrectnessState, stackGetCorrectnessConfig,
      stackStorePosition]

example :
    (evalWordStackMachine stackGetCorrectnessState
      (stackRemoveSet stackGetCorrectnessConfig .heapLength 6)).map
        (fun final =>
          final.memory
            (stackGetCorrectnessState.registers 10 +
              BitVec.ofNat 64 (stackStorePosition .heapLength))) =
      some (BitVec.ofNat 64 55) := by
  simpa [stackGetCorrectnessConfig, stackGetCorrectnessState,
    stackStorePosition] using
    (evalStackRemoveSet (width := 64) stackGetCorrectnessConfig
      stackGetCorrectnessState 6 .heapLength (by simp)
      (by simp [stackGetCorrectnessConfig])
      (by simp [stackGetCorrectnessConfig]))

example :
    (evalWordStackMachine stackGetCorrectnessState
      (stackRemoveGet stackGetCorrectnessConfig 4 .currHeap)).map
        (fun final => final.registers 4) =
      some (BitVec.ofNat 64 0) := by
  simpa [stackGetCorrectnessConfig, stackGetCorrectnessState] using
    (evalStackRemoveGetCurrHeap (width := 64) stackGetCorrectnessConfig
      stackGetCorrectnessState 4)

example :
    (evalWordStackMachine stackGetCorrectnessState
      (stackRemoveSet stackGetCorrectnessConfig .currHeap 6)).map
        (fun final => final.registers 12) =
      some (BitVec.ofNat 64 55) := by
  simpa [stackGetCorrectnessConfig, stackGetCorrectnessState] using
    (evalStackRemoveSetCurrHeap (width := 64) stackGetCorrectnessConfig
      stackGetCorrectnessState 6)

example :
    (evalWordStackMachine stackGetCorrectnessState
      (stackRemoveStackAlloc stackGetCorrectnessConfig 2)).map
        (fun final => final.registers 20) =
      some (BitVec.ofNat 64 0 - BitVec.ofNat 64 16) := by
  simpa [stackGetCorrectnessConfig, stackGetCorrectnessState] using
    (evalStackRemoveStackAlloc_small (width := 64)
      stackGetCorrectnessConfig stackGetCorrectnessState 2 (by omega)
      (by simp [stackGetCorrectnessConfig]))

end Flapjack.RiscV
