import Flapjack.RiscV.Encoding
import Flapjack.Test.CorrectnessTarget
import Flapjack.Test.PipelineDiagnostics
import Flapjack.Test.SourceGlobalParity

/-!
# Pancake/RISC-V compiler parity tests

These are executable tests, so they run with `lake test` in addition to the
compile-time `#guard` regressions.  The two byte vectors below were obtained
from CakeML's `cake --pancake --target=riscv` on the corresponding minimal
Pancake programs.  Cake's generated entry body is followed by the shared
runtime; we pin the generated words here and test the complete Lean linked
image separately.

The full source-to-runtime-image comparison is intentionally not weakened to
an existence check: the source test currently records that the Lean entry
point can produce an artifact, while the golden vectors and linked image make
the exact-output obligations explicit for the next parity increments.
-/

namespace Flapjack.Test.CompilerParity

open Flapjack Flapjack.RiscV

def cakeReturnWords (value : Nat) : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 (value * 0x10), BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00 ]

def leanReturnWords (value : Nat) : List (BitVec 8) :=
  RiscV.encodeInstructions
    [.ori 10 0 (BitVec.ofNat 64 value), .jalr 0 1 0]

/-! The exact Lean source-entry bytes are pinned separately from the
    Cake-derived section-shape golden in SourceGlobalParity. -/
def rotateArtifactGolden : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x83,
    BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x30,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e,
    BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0xea, BitVec.ofNat 8 0x5a, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xda,
    BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0xde,
    BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f,
    BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xfa, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x50, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0d, BitVec.ofNat 8 0x10,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6f,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x8f, BitVec.ofNat 8 0xbf, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9f, BitVec.ofNat 8 0xf1,
    BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0xde,
    BitVec.ofNat 8 0xb1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0xee, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0xef, BitVec.ofNat 8 0xde,
    BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xe2,
    BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x02, BitVec.ofNat 8 0xf2, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0x42,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00 ]

def rotateArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.rotateSource with
  | some bytes => bytes == rotateArtifactGolden
  | none => false

def minimalSourceArtifact : Bool :=
  match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "fun 1 main() { return 7; }" with
  | .ok artifact => artifact.bytes.length > 0
  | .error _ => false

def checkEq [BEq α] [Repr α]
    (name : String) (actual expected : α) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {repr expected}, got {repr actual}"
    pure false

def checkBool (name : String) (condition : Bool) : IO Bool := do
  if condition then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}"
    pure false

def main : IO Unit := do
  let results ← [
    checkEq "Cake return 0 generated words"
      (leanReturnWords 0) (cakeReturnWords 0),
    checkEq "Cake return 7 generated words"
      (leanReturnWords 7) (cakeReturnWords 7),
    checkEq "Lean target linked image"
      pipelineCallTargetLinkedImage (some pipelineCallTargetImage),
    checkBool "Lean rotate-right exact source artifact bytes"
      rotateArtifactMatchesGolden,
    checkBool "Lean source entry produces an artifact" minimalSourceArtifact,
    checkBool "Pancake computed local-store address compiles" nestedLocalStoreBytesAccepted,
    Flapjack.Test.SourceGlobalParity.runChecks
    ].mapM id
  unless results.all id do
    IO.Process.exit 1

end Flapjack.Test.CompilerParity

def main : IO Unit := Flapjack.Test.CompilerParity.main
