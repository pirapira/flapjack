import Flapjack.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$wrap_rt`

The expected cases come from the direct HOL-EVAL fixture
`scripts/hol-probes/wrap_rt_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:131-136`.
-/

namespace Flapjack.Test.WrapRtParity

open Flapjack

def isNone : Option (Shape × List Nat) → Bool
  | none => true
  | _ => false

def isOneWord : Option (Shape × List Nat) → Bool
  | some (.one, [1]) => true
  | _ => false

def isEmptyComb : Option (Shape × List Nat) → Bool
  | some (.comb [], []) => true
  | _ => false

def isNamed : Option (Shape × List Nat) → Bool
  | some (.named "S", []) => true
  | _ => false

def parityGuard : Bool :=
  isNone (wrapRt none) &&
  isNone (wrapRt (some (.one, []))) &&
  isOneWord (wrapRt (some (.one, [1]))) &&
  isEmptyComb (wrapRt (some (.comb [], []))) &&
  isNamed (wrapRt (some (.named "S", [])))

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS wrap_rt none/empty-one/preserved parity"
  else
    IO.println "FAIL wrap_rt parity"
  pure parityGuard

end Flapjack.Test.WrapRtParity
