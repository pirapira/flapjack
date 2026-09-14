import Flapjack.PanGlobals

namespace Flapjack.Test.PanGlobalsFpermNameParity

/-! Direct parity for `pan_globals$fperm_name_def`
    (`pan_globalsScript.sml:184`). -/
def parityGuard : Bool :=
  globalRenameFunctionName "foo" "bar" "foo" == "bar" &&
  globalRenameFunctionName "foo" "bar" "bar" == "foo" &&
  globalRenameFunctionName "foo" "bar" "worker" == "worker" &&
  globalRenameFunctionName "foo" "foo" "foo" == "foo" &&
  globalRenameFunctionName "foo'" "bar'" "foo'" == "bar'"

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanGlobalsFpermNameParity
