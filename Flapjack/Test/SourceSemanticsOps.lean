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

end Flapjack
