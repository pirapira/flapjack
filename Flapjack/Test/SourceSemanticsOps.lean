import Flapjack.RiscV.PanMemory
import Flapjack.Semantics

/-! RISC-V regressions for the complete source shift operation. -/

namespace Flapjack

abbrev ShiftWord := RiscV.Word 8

def shiftWord (value : Nat) : ShiftWord := BitVec.ofNat 8 value

#guard evalPanShiftFull .lsl (shiftWord 1) (shiftWord 2) = some (shiftWord 4)
#guard evalPanShiftFull .lsr (shiftWord 8) (shiftWord 1) = some (shiftWord 4)
#guard evalPanShiftFull .asr (shiftWord 0x80) (shiftWord 1) = some (shiftWord 0xc0)
#guard evalPanShiftFull .ror (shiftWord 0x81) (shiftWord 1) = some (shiftWord 0xc0)

def evalRiscVAsr : Option (PanValue ShiftWord) :=
  RiscV.evalPanRiscVFlatExp [] (fun _ => none) (fun _ => none)
    (fun _ => false) (fun _ => none)
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    (.shift .asr (.const (shiftWord 0x80)) (.const (shiftWord 1)))

def evalRiscVRor : Option (PanValue ShiftWord) :=
  RiscV.evalPanRiscVFlatExp [] (fun _ => none) (fun _ => none)
    (fun _ => false) (fun _ => none)
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    (.shift .ror (.const (shiftWord 0x81)) (.const (shiftWord 1)))

#guard match evalRiscVAsr with
  | some (.word value) => value == shiftWord 0xc0
  | _ => false
#guard match evalRiscVRor with
  | some (.word value) => value == shiftWord 0xc0
  | _ => false

#guard RiscV.panRiscVWordOp (width := 8) .add [] == some (shiftWord 0)
#guard RiscV.panRiscVWordOp (width := 8) .add [shiftWord 1, shiftWord 2, shiftWord 3] ==
  some (shiftWord 6)
 #guard RiscV.panRiscVWordOp (width := 8) .and [] == some (shiftWord 0xff)
#guard RiscV.panRiscVWordOp (width := 8) .xor [shiftWord 0xf0, shiftWord 0x0f, shiftWord 0x03] ==
  some (shiftWord 0xfc)
#guard RiscV.panRiscVWordOp (width := 8) .sub [shiftWord 7, shiftWord 2] == some (shiftWord 5)
#guard RiscV.panRiscVWordOp (width := 8) .sub [] == none
#guard RiscV.panRiscVWordOp (width := 8) .sub [shiftWord 7] == none

def evalRiscVAddThree : Option (PanValue ShiftWord) :=
  RiscV.evalPanRiscVFlatExp [] (fun _ => none) (fun _ => none)
    (fun _ => false) (fun _ => none)
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    (.op .add [.const (shiftWord 1), .const (shiftWord 2), .const (shiftWord 3)])

#guard match evalRiscVAddThree with
  | some (.word value) => value == shiftWord 6
  | _ => false

#guard RiscV.panRiscVCmp .lower (shiftWord 0x80) (shiftWord 0) == shiftWord 0
#guard RiscV.panRiscVCmp .less (shiftWord 0x80) (shiftWord 0) == shiftWord 1
#guard RiscV.panRiscVCmp .notLower (shiftWord 0x80) (shiftWord 0) == shiftWord 1
#guard RiscV.panRiscVCmp .notLess (shiftWord 0x80) (shiftWord 0) == shiftWord 0

def evalRiscVSignedLess : Option (PanValue ShiftWord) :=
  RiscV.evalPanRiscVFlatExp [] (fun _ => none) (fun _ => none)
    (fun _ => false) (fun _ => none)
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    (.cmp .less (.const (shiftWord 0x80)) (.const (shiftWord 0)))

def evalRiscVUnsignedLower : Option (PanValue ShiftWord) :=
  RiscV.evalPanRiscVFlatExp [] (fun _ => none) (fun _ => none)
    (fun _ => false) (fun _ => none)
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    (.cmp .lower (.const (shiftWord 0x80)) (.const (shiftWord 0)))

#guard match evalRiscVSignedLess with
  | some (.word value) => value == shiftWord 1
  | _ => false
#guard match evalRiscVUnsignedLower with
  | some (.word value) => value == shiftWord 0
  | _ => false

def evalGenericRiscVSignedLess : Option (PanValue ShiftWord) :=
  evalPanFlatExp [] (fun _ => none) (fun _ => none)
    (fun _ => false) (fun _ => none)
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    (.cmp .less (.const (shiftWord 0x80)) (.const (shiftWord 0)))
    (memoryAccess := some (panMemoryAccessOfModel RiscV.panRiscVMemoryModel))

def evalGenericRiscVUnsignedLower : Option (PanValue ShiftWord) :=
  evalPanFlatExp [] (fun _ => none) (fun _ => none)
    (fun _ => false) (fun _ => none)
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    (.cmp .lower (.const (shiftWord 0x80)) (.const (shiftWord 0)))
    (memoryAccess := some (panMemoryAccessOfModel RiscV.panRiscVMemoryModel))

#guard match evalGenericRiscVSignedLess with
  | some (.word value) => value == shiftWord 1
  | _ => false
#guard match evalGenericRiscVUnsignedLower with
  | some (.word value) => value == shiftWord 0
  | _ => false

def assignmentWordLocals : VarName → Option (PanValue ShiftWord) := fun name =>
  if name == "x" then some (.word (shiftWord 7)) else none

def evalRiscVValidAssignment :=
  RiscV.evalPanRiscVFlatProg []
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    assignmentWordLocals (fun _ => none) (fun _ => false) (fun _ => none)
    (.assign .local "x" (.const (shiftWord 9)))

def evalRiscVMismatchedAssignment :=
  RiscV.evalPanRiscVFlatProg []
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    assignmentWordLocals (fun _ => none) (fun _ => false) (fun _ => none)
    (.assign .local "x" (.rStruct []))

def evalRiscVMissingAssignment :=
  RiscV.evalPanRiscVFlatProg []
    (shiftWord 0) (shiftWord 0) (shiftWord 8)
    assignmentWordLocals (fun _ => none) (fun _ => false) (fun _ => none)
    (.assign .local "missing" (.const (shiftWord 9)))

#guard evalRiscVValidAssignment.isSome
#guard evalRiscVMismatchedAssignment.isNone
#guard evalRiscVMissingAssignment.isNone

def evalRiscVFuelMismatchedAssignment :=
  RiscV.evalPanRiscVFlatProgWithCallsAndFfi []
    []
    (fun _ _ _ _ _ _ => none)
    (shiftWord 0) (shiftWord 0) (shiftWord 8) 4
    assignmentWordLocals (fun _ => none) (fun _ => false) (fun _ => none)
    (.assign .local "x" (.rStruct []))

#guard evalRiscVFuelMismatchedAssignment.isNone

end Flapjack
