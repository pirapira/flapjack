import Flapjack.RiscV.CorrectnessStackRiscV

/-! Concrete smoke test for the StackLang-to-RISC-V register relation. -/

namespace Flapjack.RiscV

def stackRiscVTestSource : WordStackMachineState 64 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

theorem stackRiscVTestRelation :
    WordStackRegisterRelation stackRiscVTestSource (zeroState 64) := by
  intro register hregister
  simp [stackRiscVTestSource, zeroState]

def stackRiscVWordConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5), (2, .register 6)]
    scratch := 31
    stackBase := 21 }

def stackRiscVRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

example :
      wordToStackProgNat stackRiscVWordConfig
      (.assign 0 (.op .add [.var 1, .var 2]) : WordProg Nat) =
      some (.arith .add 4 5 6) := by
  simp [wordToStackProgNat, wordStackCompileExpNat,
    wordStackCompileBinaryNat, wordStackAtomNat, wordStackWritePhysicalNat,
    wordStackReadRegister, wordStackLocation, lookupNatInfo,
    stackRiscVWordConfig, wordStackJoin]

example :
    compileWordProgramNatToRiscV (width := 64) { services := [] }
      stackRiscVWordConfig stackRiscVRemoveConfig 2 3
      (.assign 0 (.op .add [.var 1, .var 2]) : WordProg Nat) =
      some [.add 4 5 6] := by
  decide +kernel

example :
    ∃ final,
      WordStackRegisterRelation
        (wordStackMachineWriteRegister stackRiscVTestSource 4
          (stackRiscVTestSource.registers 5 + stackRiscVTestSource.registers 6))
        final ∧
      (compileWordProgramNatToRiscV (width := 64) { services := [] }
        stackRiscVWordConfig stackRiscVRemoveConfig 2 3
        (.assign 0 (.op .add [.var 1, .var 2]) : WordProg Nat)).bind
          (fun code => some (executeInstructions (zeroState 64) code)) =
        some (execute (zeroState 64) (.add 4 5 6)) := by
  refine ⟨execute (zeroState 64) (.add 4 5 6), ?_, ?_⟩
  · exact wordStackRegisterRelation_executeAdd stackRiscVTestSource
      (zeroState 64) 4 5 6 stackRiscVTestRelation (by omega) (by omega)
      (by omega) (by omega)
  rw [show compileWordProgramNatToRiscV (width := 64) { services := [] }
      stackRiscVWordConfig stackRiscVRemoveConfig 2 3
      (.assign 0 (.op .add [.var 1, .var 2]) : WordProg Nat) =
      some [.add 4 5 6] by decide +kernel]
  rfl

example :
    (labCompilePlain (.const 5 7 : LabPlain (Word 64))).bind
        (fun code =>
          some (WordStackRegisterRelation
            (wordStackMachineWriteRegister stackRiscVTestSource 5
              (BitVec.ofNat 64 7))
            (executeInstructions (zeroState 64) code))) =
      some (WordStackRegisterRelation
        (wordStackMachineWriteRegister stackRiscVTestSource 5
          (BitVec.ofNat 64 7))
        (execute (zeroState 64) (.addi 5 0 (BitVec.ofNat 64 7)))) := by
  exact labCompilePlain_const_register_simulation stackRiscVTestSource
    (zeroState 64) 5 7 stackRiscVTestRelation (by omega) (by omega)
    (by simp [stackRiscVTestSource])

example :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister stackRiscVTestSource 5
        (stackRiscVTestSource.registers 2 + stackRiscVTestSource.registers 3))
      (executeInstructions (zeroState 64)
        [.add 5 2 3]) := by
  apply labCompilePlain_add_register_simulation stackRiscVTestSource
    (zeroState 64) 5 2 3 stackRiscVTestRelation (by omega) (by omega)
    (by omega) (by omega) [.add 5 2 3]
  exact labCompilePlain_add 5 2 3 (by omega) (by omega) (by omega)

example :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister stackRiscVTestSource 5
        (stackRiscVTestSource.registers 2 - stackRiscVTestSource.registers 3))
      (executeInstructions (zeroState 64)
        [.sub 5 2 3]) := by
  apply labCompilePlain_sub_register_simulation stackRiscVTestSource
    (zeroState 64) 5 2 3 stackRiscVTestRelation (by omega) (by omega)
    (by omega) (by omega) [.sub 5 2 3]
  exact labCompilePlain_sub 5 2 3 (by omega) (by omega) (by omega)

example :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister stackRiscVTestSource 5
        (stackRiscVTestSource.registers 2 &&& stackRiscVTestSource.registers 3))
      (executeInstructions (zeroState 64)
        [.and 5 2 3]) := by
  apply labCompilePlain_and_register_simulation stackRiscVTestSource
    (zeroState 64) 5 2 3 stackRiscVTestRelation (by omega) (by omega)
    (by omega) (by omega) [.and 5 2 3]
  exact labCompilePlain_and 5 2 3 (by omega) (by omega) (by omega)

example :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister stackRiscVTestSource 5
        (stackRiscVTestSource.registers 2 ||| stackRiscVTestSource.registers 3))
      (executeInstructions (zeroState 64)
        [.or 5 2 3]) := by
  apply labCompilePlain_or_register_simulation stackRiscVTestSource
    (zeroState 64) 5 2 3 stackRiscVTestRelation (by omega) (by omega)
    (by omega) (by omega) [.or 5 2 3]
  exact labCompilePlain_or 5 2 3 (by omega) (by omega) (by omega)

example :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister stackRiscVTestSource 5
        (stackRiscVTestSource.registers 2 ^^^ stackRiscVTestSource.registers 3))
      (executeInstructions (zeroState 64)
        [.xor 5 2 3]) := by
  apply labCompilePlain_xor_register_simulation stackRiscVTestSource
    (zeroState 64) 5 2 3 stackRiscVTestRelation (by omega) (by omega)
    (by omega) (by omega) [.xor 5 2 3]
  exact labCompilePlain_xor 5 2 3 (by omega) (by omega) (by omega)

end Flapjack.RiscV
