import Flapjack.Pancake.PanGlobals

namespace Flapjack.Test.PanGlobalsFpermParity

/-! Direct parity for `pan_globals$fperm_def`
    (`pan_globalsScript.sml:191`). -/
def parityGuard : Bool :=
  let renamedCall :=
    globalRenameProg "foo" "bar" ((.call none "foo" []) : Prog Nat)
  let renamedDecCall :=
    globalRenameProg "foo" "bar"
      (.decCall "x" .one "bar" [] (.skip : Prog Nat))
  let renamedHandler :=
    globalRenameProg "foo" "bar"
      (.call (some (none, some ("E", "exn",
        (.call none "foo" [] : Prog Nat)))) "worker" [])
  let renamedControl :=
    globalRenameProg "foo" "bar"
      ((.seq
        (.ite (.const 0) (.call none "foo" [])
          (.while (.const 1)
            (.dec "x" .one (.const 2) (.call none "foo" []))))
        (.assign .local "x" (.const 3))) : Prog Nat)
  let unchanged := globalRenameProg "foo" "bar" (.return (.const 9) : Prog Nat)
  (match renamedCall with
  | .call none "bar" [] => true
  | _ => false) &&
  (match renamedDecCall with
  | .decCall "x" .one "foo" [] .skip => true
  | _ => false) &&
  (match renamedHandler with
  | .call (some (none, some ("E", "exn", .call none "bar" []))) "worker" [] => true
  | _ => false) &&
  (match renamedControl with
  | .seq
      (.ite (.const 0) (.call none "bar" [])
        (.while (.const 1)
          (.dec "x" .one (.const 2) (.call none "bar" []))))
      (.assign .local "x" (.const 3)) => true
  | _ => false) &&
  (match unchanged with
  | .return (.const 9) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

/-- Replays the direct original-HOL rows of
    `scripts/hol-probes/pan_globals_fperm_probe.out` and reports a PASS line
    (`flapjack-6nn.1.2`). -/
def runChecks : IO Bool := do
  IO.println (if parityGuard then
    "PASS pan_globals fperm_def parity (4 HOL rows)"
    else "FAIL pan_globals fperm_def parity (4 HOL rows)")
  pure parityGuard

end Flapjack.Test.PanGlobalsFpermParity
