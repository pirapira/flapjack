import Flapjack.PanStructsAfindi

namespace Flapjack.Test.PanStructsAfindiParity

/-! Direct parity for `pan_structs$afindi_def`
    (`pan_structsScript.sml:25`). -/
def entries : List (String × Nat) := [("a", 10), ("b", 20), ("c", 30)]

def parityGuard : Bool :=
  (afindi "a" ([] : List (String × Nat)) == none) &&
  (afindi "a" entries == some 0) &&
  (afindi "b" entries == some 1) &&
  (afindi "c" entries == some 2) &&
  (afindi "z" entries == none) &&
  (afindi "a" [("a", 10), ("b", 20), ("a", 30)] == some 0)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanStructsAfindiParity
