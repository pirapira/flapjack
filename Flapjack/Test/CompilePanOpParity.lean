import Flapjack.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$compile_panop`

The expected value comes from the direct HOL-EVAL fixture
`scripts/hol-probes/compile_panop_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:35`.
-/

namespace Flapjack.Test.CompilePanOpParity

open Flapjack

def parityGuard : Bool :=
  match compilePanOp .mul with
  | .mul => true

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_panop Mul"
  else
    IO.println "FAIL compile_panop parity"
  pure parityGuard

end Flapjack.Test.CompilePanOpParity
