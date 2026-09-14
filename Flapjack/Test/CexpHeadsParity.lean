import Flapjack.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$cexp_heads`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/cexp_heads_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:19-26`.
-/

namespace Flapjack.Test.CexpHeadsParity

open Flapjack

def parityGuard : Bool :=
  cexpHeads ([] : List (List (CrepExp Nat))) == some [] &&
  cexpHeads [[.const 1, .const 2], [.var 3, .var 4]] ==
    some [.const 1, .var 3] &&
  cexpHeads ([[], [.const 5]] : List (List (CrepExp Nat))) == none &&
  cexpHeads ([[.const 6], []] : List (List (CrepExp Nat))) == none

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS cexp_heads empty/heads/empty-head/empty-tail"
  else
    IO.println "FAIL cexp_heads parity"
  pure parityGuard

end Flapjack.Test.CexpHeadsParity
