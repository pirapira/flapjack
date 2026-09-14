import Flapjack.PanGlobals

namespace Flapjack.Test.PanGlobalsFreshNameParity

/-! Direct parity for `pan_globals$fresh_name_def`
    (`pan_globalsScript.sml:55`). -/
def parityGuard : Bool :=
  globalFreshName "x" [] == "x" &&
  globalFreshName "x" ["x"] == "x'" &&
  globalFreshName "x" ["x", "x'", "x''"] == "x'''" &&
  globalFreshName "x'" ["x'", "x''"] == "x'''" &&
  globalFreshName "main" ["worker", "helper"] == "main"

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanGlobalsFreshNameParity
