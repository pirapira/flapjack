import Flapjack.Pancake.Semantics.PanSem.MemByteAssembly

namespace Flapjack.Test.PanSemMemByteAssemblyParity

open Flapjack

/-- Replay the little-endian four-byte assembly identity on concrete bytes,
comparing against `RiscV.panRiscVWordOfBytes` (the base-256 codec). -/
def leAssemblyGuard : Bool :=
  decide
    ((BitVec.setWidth 32 (0x78 : BitVec 8) ||| (BitVec.setWidth 32 (0x56 : BitVec 8)) <<< 8
        ||| (BitVec.setWidth 32 (0x34 : BitVec 8)) <<< 16
        ||| (BitVec.setWidth 32 (0x12 : BitVec 8)) <<< 24)
      = RiscV.panRiscVWordOfBytes (width := 32) false
          [BitVec.setWidth 32 (0x78 : BitVec 8), BitVec.setWidth 32 (0x56 : BitVec 8),
           BitVec.setWidth 32 (0x34 : BitVec 8), BitVec.setWidth 32 (0x12 : BitVec 8)])

def zeroHighByteGuard : Bool :=
  decide
    ((BitVec.setWidth 32 (0 : BitVec 8) ||| (BitVec.setWidth 32 (0 : BitVec 8)) <<< 8
        ||| (BitVec.setWidth 32 (0 : BitVec 8)) <<< 16
        ||| (BitVec.setWidth 32 (255 : BitVec 8)) <<< 24)
      = BitVec.ofNat 32 (256 ^ 3 * 255))

#guard leAssemblyGuard
#guard zeroHighByteGuard

def runChecks : IO Bool := do
  if leAssemblyGuard && zeroHighByteGuard then
    IO.println "PASS exact panSem 32-bit little-endian byte OR/shift = base-256 assembly"
    pure true
  else
    IO.println "FAIL exact panSem 32-bit little-endian byte OR/shift = base-256 assembly"
    pure false

end Flapjack.Test.PanSemMemByteAssemblyParity
