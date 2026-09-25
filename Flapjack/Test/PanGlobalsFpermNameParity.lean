import Flapjack.Pancake.PanGlobals

namespace Flapjack.Test.PanGlobalsFpermNameParity

/-! Direct parity for `pan_globals$fperm_name_def`
    (`pan_globalsScript.sml:184`), reviewed under flapjack-6nn.1.1.

    The HOL oracle is `scripts/hol-probes/pan_globals_fperm_name_probe.out`;
    the rows below replay that probe for the unchanged (missing) key, the
    source-collision key, the target-collision key, identical names, and names
    that already carry apostrophes. -/

def parityGuard : Bool :=
  globalRenameFunctionName "foo" "bar" "foo" == "bar" &&
  globalRenameFunctionName "foo" "bar" "bar" == "foo" &&
  globalRenameFunctionName "foo" "bar" "worker" == "worker" &&
  globalRenameFunctionName "foo" "foo" "foo" == "foo" &&
  globalRenameFunctionName "foo'" "bar'" "foo'" == "bar'" &&
  globalRenameFunctionName "foo'" "bar'" "bar'" == "foo'" &&
  globalRenameFunctionName "a'" "b'" "c'" == "c'"

#eval parityGuard
#guard parityGuard

-- Kernel-checked rows corresponding to the committed HOL oracle rows.
theorem source_collision :
    globalRenameFunctionName "foo" "bar" "foo" = "bar" := rfl
theorem target_collision :
    globalRenameFunctionName "foo" "bar" "bar" = "foo" := rfl
theorem unchanged :
    globalRenameFunctionName "foo" "bar" "worker" = "worker" := rfl
theorem same_names :
    globalRenameFunctionName "foo" "foo" "foo" = "foo" := rfl
theorem quoted_source :
    globalRenameFunctionName "foo'" "bar'" "foo'" = "bar'" := rfl
theorem quoted_target :
    globalRenameFunctionName "foo'" "bar'" "bar'" = "foo'" := rfl
theorem quoted_unchanged :
    globalRenameFunctionName "a'" "b'" "c'" = "c'" := rfl

def runChecks : IO Bool := do
  IO.println (if parityGuard then
    "PASS pan_globals fperm_name_def parity (7 HOL rows)"
    else "FAIL pan_globals fperm_name_def parity (7 HOL rows)")
  pure parityGuard

end Flapjack.Test.PanGlobalsFpermNameParity
