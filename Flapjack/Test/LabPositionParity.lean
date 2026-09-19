import Flapjack.RiscV.Lab

namespace Flapjack.RiscV

/-! CakeML's `lab_to_target` indexes CallFFI targets from the original
    `ffi_names` order while the exported prefix emits those blocks reversed.
    These two-service guards exercise the position base and prefix ordering;
    the one-service case cannot distinguish the two conventions. -/

example :
    labFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "first" 64 =
      some (0 - BitVec.ofNat 64 128) := by
  decide

example :
    labFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "second" 64 =
      some (0 - BitVec.ofNat 64 112) := by
  decide

example :
    labFfiStubPrefix (width := 64)
      { services := [("first", 7), ("second", 8)] } =
      labFfiServiceStub 8 ++ labFfiServiceStub 7 ++
        List.replicate 8 (.jal 0 0) := by
  rfl

example :
    labCompileAsmWithHalt (width := 64) { services := [] } [] 64 999 .halt =
      some [.jal 0 (0 - BitVec.ofNat 64 80)] := by
  rfl

example :
    labCompileAsmWithHalt (width := 64) { services := [] } [] 64 999 .install =
      some [.jal 0 (0 - BitVec.ofNat 64 96)] := by
  rfl

example :
    labCompileAsmProgramWithFfiBaseAndHalt (width := 64)
      { services := [("first", 7), ("second", 8)] } [] 96 64 999
      (.callFfi "first") =
      /- Cake addresses the exported FFI block from the linked absolute
         position; `ffiBase` is retained only for the legacy API shape. -/
      some [.jal 0 (0 - BitVec.ofNat 64 160)] := by
  decide

/-! Cake can retain a LabAsm length of 5 after `add_nop`: its one-instruction
    body is followed by one complete encoded Skip even though the logical line
    length is not instruction-aligned. -/
def storedLengthFiveOracle : Bool :=
    labPadStoredInstructions (width := 64)
      [.ori 10 0 (BitVec.ofNat 64 1)] 5 ==
    [.ori 10 0 (BitVec.ofNat 64 1)]

#guard storedLengthFiveOracle

/-! Cake's `pad_section` applies each nonzero retained label length to the
    most recent prior LabAsm, appending one complete encoded Skip. -/
def twoStoredLabelPadsOracle : Bool :=
  labCompileProgramLinesWithStoredLengths (width := 64) { services := [] } []
      1000 1000 2000
      [.asm (.const 1 1) [] 4,
       .label 0 1 1,
       .asm (.const 2 2) [] 4,
       .label 0 2 1] ==
    some [.ori 1 0 (BitVec.ofNat 64 1), .addi 0 0 0,
      .ori 2 0 (BitVec.ofNat 64 2), .addi 0 0 0]

#guard twoStoredLabelPadsOracle

/-! A leading retained label has no preceding Asm/LabAsm, so Cake's
    `pad_section` leaves the section physically unchanged.  Consecutive
    retained labels still apply `add_nop` to that same nearest predecessor. -/
def leadingStoredLabelNoPadOracle : Bool :=
    labCompileProgramLinesWithStoredLengths (width := 64) { services := [] } []
      1000 1000 2000
      [.label 0 1 1,
       .asm (.const 1 1) [] 4] ==
    some [.ori 1 0 (BitVec.ofNat 64 1)]

#guard leadingStoredLabelNoPadOracle

def consecutiveStoredLabelPadsOracle : Bool :=
    labCompileProgramLinesWithStoredLengths (width := 64) { services := [] } []
      1000 1000 2000
      [.asm (.const 1 1) [] 4,
       .label 0 1 1,
       .label 0 2 1] ==
    some [.ori 1 0 (BitVec.ofNat 64 1), .addi 0 0 0, .addi 0 0 0]

#guard consecutiveStoredLabelPadsOracle


example :
    labLinkedFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "first" 96 =
      some (0 - BitVec.ofNat 64 80) := by
  decide

example :
    labLinkedFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "second" 96 =
      some (0 - BitVec.ofNat 64 96) := by
  decide

/-! Cake's `riscv_ast` materializes ordinary immediate comparisons, including
    zero, in the encoder temporary before emitting the branch. -/
example :
    labWordConditionOperands (width := 64) .notEqual 10 (.imm 0) =
      some (10, 31, [.ori 31 0 (BitVec.ofNat 64 0)]) := by
  decide

end Flapjack.RiscV
