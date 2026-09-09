import Flapjack.RiscV.CorrectnessStackRiscVDivision

/-! Regression coverage for StackLang unsigned division lowering. -/

namespace Flapjack.RiscV

open Flapjack

example :
    labCompilePlain
      (.word (.arith (.div 5 2 3)) : LabPlain (Word 64)) =
      some [.divU 5 2 3] := by
  exact labCompilePlain_div 5 2 3 (by omega) (by omega) (by omega)

end Flapjack.RiscV
