import Flapjack.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$exp_hdl`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/exp_hdl_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:106-112`.
-/

namespace Flapjack.Test.ExpHdlParity

open Flapjack

def vars : InfoMap (Shape × List Nat) := [("x", (.one, [3, 4]))]

def missingOK : Bool :=
  match expHdl (α := Nat) vars "missing" with
  | .skip => true
  | _ => false

def knownOK : Bool :=
  match expHdl (α := Nat) vars "x" with
  | .seq (.assign 3 (.loadGlob 0))
      (.seq (.assign 4 (.loadGlob 1)) .skip) => true
  | _ => false

def parityGuard : Bool := missingOK && knownOK

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS exp_hdl missing/known global-load assignments"
  else
    IO.println "FAIL exp_hdl parity"
  pure parityGuard

end Flapjack.Test.ExpHdlParity
