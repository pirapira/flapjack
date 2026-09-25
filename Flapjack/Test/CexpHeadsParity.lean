import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.CrepProps

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
  cexpHeadsSimp ([] : List (List (CrepExp Nat))) == some [] &&
  cexpHeads [[.const 1, .const 2], [.var 3, .var 4]] ==
    some [.const 1, .var 3] &&
  cexpHeadsSimp [[.const 1, .const 2], [.var 3, .var 4]] ==
    some [.const 1, .var 3] &&
  cexpHeads ([[], [.const 5]] : List (List (CrepExp Nat))) == none &&
  cexpHeadsSimp ([[], [.const 5]] : List (List (CrepExp Nat))) == none &&
  cexpHeads ([[.const 6], []] : List (List (CrepExp Nat))) == none &&
  cexpHeadsSimp ([[.const 6], []] : List (List (CrepExp Nat))) == none &&
  cexpHeadsW (width := 64) ([] : List (List (CrepExp (BitVec 64)))) == some [] &&
  cexpHeadsW (width := 64) [[.const (1 : BitVec 64)], [.var 3]] ==
    some [.const 1, .var 3] &&
  cexpHeadsW (width := 64) ([[], [.const (5 : BitVec 64)]] :
    List (List (CrepExp (BitVec 64)))) == none &&
  cexpHeadsW (width := 64) ([[.const (6 : BitVec 64)], []] :
    List (List (CrepExp (BitVec 64)))) == none

#eval parityGuard
#guard parityGuard

theorem cexpHeads_eq_cexpHeadsSimp_fixture :
    cexpHeads ([[.const 1, .const 2], [.var 3, .var 4]] : List (List (CrepExp Nat))) =
      cexpHeadsSimp [[.const 1, .const 2], [.var 3, .var 4]] :=
  cexpHeads_eq_cexpHeadsSimp [[.const 1, .const 2], [.var 3, .var 4]]

theorem cexpHeads_eq_cexpHeadsSimp_empty_fixture :
    cexpHeads ([[], [.const 5]] : List (List (CrepExp Nat))) =
      cexpHeadsSimp [[], [.const 5]] :=
  cexpHeads_eq_cexpHeadsSimp [[], [.const 5]]

#check @cexpHeads_eq_cexpHeadsSimp

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS cexp_heads empty/heads/empty-head/empty-tail"
  else
    IO.println "FAIL cexp_heads parity"
  pure parityGuard

end Flapjack.Test.CexpHeadsParity
