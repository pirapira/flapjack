import Flapjack.RiscV.PanMemory

/-! # `RiscV.panRiscVByteAlign` versus HOL `byte$byte_align`

HOL `byte_align_def` is `align (LOG2 (dimindex DIV 8))`, i.e. clear the low
`LOG2 (width / 8)` bits. The production `RiscV.panRiscVByteAlign` rounds down
to a multiple of the supplied `bytesInWord`. These agree exactly when
`bytesInWord` is a power of two, which covers the only reachable production
RISC-V width (`Word 64`, `bytesInWord = 8 = 2^3`). The non-power-of-two width
24 case below is a direct oracle counterexample pinned by
`scripts/hol-probes/byte_align_probe.out`. -/

namespace Flapjack.Test.PanRiscVByteAlignParity

open Flapjack RiscV

/-- Width 24, `bytesInWord = 3`: HOL aligns `5` to `4`, production divides to `3`. -/
theorem width24_diverges :
    panRiscVByteAlign (BitVec.ofNat 24 3) (BitVec.ofNat 24 5) = BitVec.ofNat 24 3 ∧
      BitVec.ofNat 24 ((5 >>> 1) <<< 1) = (BitVec.ofNat 24 4) := by
  constructor <;> decide

/-- Production `Word 64` alignment is the HOL bit mask (direct oracle `ba64_13 = 8w`). -/
theorem width64_agrees :
    panRiscVByteAlign (8 : Word 64) (BitVec.ofNat 64 13) = BitVec.ofNat 64 8 := by
  decide

/-- Width 8, `bytesInWord = 1`: alignment is the identity (oracle `ba8_7 = 7w`). -/
theorem width8_agrees :
    panRiscVByteAlign (BitVec.ofNat 8 1) (BitVec.ofNat 8 7) = BitVec.ofNat 8 7 := by
  decide

/-- The general power-of-two characterization at the production width. -/
theorem width64_bitMask (address : Word 64) :
    panRiscVByteAlign (8 : Word 64) address =
      BitVec.ofNat 64 ((address.toNat >>> 3) <<< 3) :=
  panRiscVByteAlign_eight_eq_bitMask address

example : panRiscVByteAlign (BitVec.ofNat 24 3) (BitVec.ofNat 24 5) = BitVec.ofNat 24 3 :=
  width24_diverges.1

def byteAlignGuard : Bool :=
  (panRiscVByteAlign (BitVec.ofNat 24 3) (BitVec.ofNat 24 5) == BitVec.ofNat 24 3) &&
    (BitVec.ofNat 24 ((5 >>> 1) <<< 1) == (BitVec.ofNat 24 4)) &&
    (panRiscVByteAlign (8 : Word 64) (BitVec.ofNat 64 13) == BitVec.ofNat 64 8) &&
    (panRiscVByteAlign (BitVec.ofNat 8 1) (BitVec.ofNat 8 7) == BitVec.ofNat 8 7)

#eval byteAlignGuard
#guard byteAlignGuard

def runChecks : IO Bool := do
  if byteAlignGuard then
    IO.println "PASS RiscV panRiscVByteAlign vs HOL byte_align (width 24 divergence, 64/8 agreement)"
    pure true
  else
    IO.println "FAIL RiscV panRiscVByteAlign vs HOL byte_align"
    pure false

end Flapjack.Test.PanRiscVByteAlignParity
