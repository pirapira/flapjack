import Flapjack.Crepe

/-!
# Original-domain parity for `crepLang$exps`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_exps_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:193-207`.
-/

namespace Flapjack.Test.CrepExpsParity

open Flapjack

def parityGuard : Bool :=
  crepExps (.const 3 : CrepExp Nat) == [.const 3] &&
  crepExps (.var 7 : CrepExp Nat) == [.var 7] &&
  crepExps (.loadGlob 2 : CrepExp Nat) == [.loadGlob 2] &&
  crepExps (.baseAddr : CrepExp Nat) == [.baseAddr] &&
  crepExps (.topAddr : CrepExp Nat) == [.topAddr] &&
  crepExps (.load (.var 1) : CrepExp Nat) == [.var 1] &&
  crepExps (.load32 (.loadByte (.var 2)) : CrepExp Nat) == [.var 2] &&
  crepExps (.op .add [.const 1, .var 4] : CrepExp Nat) ==
    [.const 1, .var 4] &&
  crepExps (.crepOp .mul [.load (.var 2), .const 5] : CrepExp Nat) ==
    [.var 2, .const 5] &&
  crepExps (.cmp .equal (.var 6) (.const 0) : CrepExp Nat) ==
    [.var 6, .const 0] &&
  crepExps (.shift .lsl (.var 8) (.const 1) : CrepExp Nat) ==
    [.var 8, .const 1]

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS crep exps leaves/load/ops/cmp/shift"
  else
    IO.println "FAIL crep exps parity"
  pure parityGuard

end Flapjack.Test.CrepExpsParity
