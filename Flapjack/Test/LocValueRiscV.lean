import Flapjack.RiscV.Lab

/-! End-to-end LocValue regression: a StackLang code label is resolved by the
    multi-section Lab linker and materialized as an absolute RISC-V pointer. -/

namespace Flapjack.RiscV

def locValueStackRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def locValueLabProgram : LabProgram (Word 64) :=
  List.map (fun (sectionId, program) =>
    labSectionNatToWord
      (labProgramToEntrySection sectionId 0 0
        (stackRemoveComplete locValueStackRemoveConfig program)))
    [(1, (.locValue 5 0 2 : StackProg Nat)), (2, (.skip : StackProg Nat))]

example :
    compileStackProgramNatListToRiscV (width := 64) { services := [] }
      locValueStackRemoveConfig 0 0
      [(1, (.locValue 5 0 2 : StackProg Nat)),
       (2, (.skip : StackProg Nat))] =
      some [.addi 5 0 (BitVec.ofNat 64 4)] := by
  decide +kernel

end Flapjack.RiscV
