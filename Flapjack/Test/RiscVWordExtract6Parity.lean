import Flapjack.RiscV.CorrectnessEncoding

/-! The checked HOL oracle values are in
    `scripts/hol-probes/riscv_word_extract_6_probe.out`.  These guards pin the
    zero and largest in-range boundary cases for
    `riscv_targetProof$word_extract_6`. -/

namespace Flapjack.Test.RiscVWordExtract6Parity

open Flapjack.RiscV

def zeroGuard : Bool :=
  decide (BitVec.extractLsb' 0 6 (0 : BitVec 64) =
    BitVec.setWidth 6 (0 : BitVec 64))

def maxInRangeGuard : Bool :=
  decide (BitVec.extractLsb' 0 6 (63 : BitVec 64) =
    BitVec.setWidth 6 (63 : BitVec 64))

example : BitVec.extractLsb' 0 6 (0 : BitVec 64) =
    BitVec.setWidth 6 (0 : BitVec 64) :=
  wordExtract6OfLt64 0 (by decide)

example : BitVec.extractLsb' 0 6 (63 : BitVec 64) =
    BitVec.setWidth 6 (63 : BitVec 64) :=
  wordExtract6OfLt64 63 (by decide)

#guard zeroGuard
#guard maxInRangeGuard
#guard zeroGuard && maxInRangeGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("word_extract_6 at zero", zeroGuard),
      ("word_extract_6 at 63", maxInRangeGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVWordExtract6Parity
