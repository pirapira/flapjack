import Flapjack.RiscV.Model
import Flapjack.Semantics

/-! RISC-V regressions for the complete source shift operation. -/

namespace Flapjack

abbrev ShiftWord := RiscV.Word 8

def shiftWord (value : Nat) : ShiftWord := BitVec.ofNat 8 value

#guard evalPanShiftFull .lsl (shiftWord 1) (shiftWord 2) = some (shiftWord 4)
#guard evalPanShiftFull .lsr (shiftWord 8) (shiftWord 1) = some (shiftWord 4)
#guard evalPanShiftFull .asr (shiftWord 0x80) (shiftWord 1) = some (shiftWord 0xc0)
#guard evalPanShiftFull .ror (shiftWord 0x81) (shiftWord 1) = some (shiftWord 0xc0)

end Flapjack
