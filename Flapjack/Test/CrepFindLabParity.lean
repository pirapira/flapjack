import Flapjack.CrepToLoop

/-! Direct parity for `crep_to_loop$find_lab` (`find_lab_def`, line 27). -/
namespace Flapjack.Test.CrepFindLabParity

def context : LoopContext Nat :=
  { vars := [], functions := [("f", (64, 2))], maxVar := 0, target := .rv64i }

def parityGuard : Bool :=
  crepFindLab context "f" == 64 && crepFindLab context "missing" == 0

#eval parityGuard
#guard parityGuard

end Flapjack.Test.CrepFindLabParity
