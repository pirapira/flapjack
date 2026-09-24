import Flapjack.RiscV.CakeAllocatorBitsBridge
import Flapjack.Compiler.Backend.WordToStack

/-!
# Executable Cake bitmap recursion ↔ tagged `bitsToWordW`/`wordListW`

Untagged bridge regression for bead `flapjack-pxn.18.5.15.3.1.1`: the executed
`Flapjack.RiscV.CakeAlloc` bitmap recursion maps onto the tagged
`bitsToWordW`/`wordListW` for every input, including the out-of-range
`LENGTH > width` boundary (both sides truncate). The direct original-HOL rows
are in `scripts/hol-probes/word_to_stack_bits_to_word_probe.out`
(`bits_overflow_65=0xFFFFFFFFFFFFFFFFw`, `wordlist_chunk=[7w; 7w; 1w]`).
-/

namespace Flapjack.Test.CakeAllocatorBitsBridgeParity

open Flapjack
open Flapjack.Compiler.Backend.WordToStack
open Flapjack.RiscV.CakeAlloc

private def bridgeGuard : Bool :=
  (BitVec.ofNat 64 (Flapjack.RiscV.CakeAlloc.bitsToWord (List.replicate 65 true)) ==
      bitsToWordW (width := 64) (List.replicate 65 true)) &&
    (BitVec.ofNat 8 (Flapjack.RiscV.CakeAlloc.bitsToWord [true, false, true]) ==
      bitsToWordW (width := 8) [true, false, true]) &&
    ((Flapjack.RiscV.CakeAlloc.frameBitmapWords 3
          [true, true, true, true, true]).map (BitVec.ofNat 8) ==
        wordListW (width := 8) [true, true, true, true, true] 3)

#eval bridgeGuard
#guard bridgeGuard

example : BitVec.ofNat 64 (Flapjack.RiscV.CakeAlloc.bitsToWord [true, false, true]) =
    bitsToWordW (width := 64) [true, false, true] :=
  bitsToWord_ofNat_eq _

example : (Flapjack.RiscV.CakeAlloc.frameBitmapWords 3
      [true, true, true, true, true]).map (BitVec.ofNat 8) =
    wordListW (width := 8) [true, true, true, true, true] 3 :=
  frameBitmapWords_map 3 _

def runChecks : IO Bool := do
  if bridgeGuard then
    IO.println "PASS executable Cake bitmap recursion maps to tagged bitsToWordW/wordListW"
  else
    IO.println "FAIL executable Cake bitmap recursion bridge"
  pure bridgeGuard

end Flapjack.Test.CakeAllocatorBitsBridgeParity