import Flapjack.RiscV.Encoding
import Flapjack.Test.CorrectnessTarget
import Flapjack.Test.PipelineDiagnostics
import Flapjack.Test.SourceGlobalParity
import Flapjack.Test.RegisterTransfer
import Flapjack.Test.LoopToWord
import Flapjack.Test.PanMemoryParity
import Flapjack.Test.PanShapeParity
import Flapjack.Test.PanWordParity
import Flapjack.Test.PanOpParity
import Flapjack.Test.PanFixedLoadParity
import Flapjack.Test.PanFixedStoreParity
import Flapjack.Test.PanFlatStoreParity
import Flapjack.Test.PanFlattenParity
import Flapjack.Test.PanResVarParity
import Flapjack.Test.PanPrimopParity
import Flapjack.Test.PanSetVarParity
import Flapjack.Test.CakeStackReseatParity
import Flapjack.Test.LoopGetVarsParity
import Flapjack.Test.LoopSetGlobalsParity
import Flapjack.Test.LoopSetVarsParity
import Flapjack.Test.LoopSetVarParity
import Flapjack.Test.LoopDecClockParity
import Flapjack.Test.LoopFixClockParity
import Flapjack.Test.LoopFindCodeParity
import Flapjack.Test.LoopPrimopParity
import Flapjack.Test.LoopArithParity
import Flapjack.Test.LoopMemStoreParity
import Flapjack.Test.LoopMemLoadParity
import Flapjack.Test.LoopMemoryStateParity
import Flapjack.Test.LoopStateResultParity
import Flapjack.Test.InstructionTransfer
import Flapjack.Test.ArtifactFormat
import Flapjack.Test.ParsedFullSsaPipeline
import Flapjack.Test.EndToEndParity

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

/-! Exact source-entry golden for the existing global initializer fixture. -/
def globalArtifactGolden : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x03,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0xd5,
    BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83,
    BitVec.ofNat 8 0xbe,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0f,
    BitVec.ofNat 8 0x30,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x9e,
    BitVec.ofNat 8 0xfe,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0xea,
    BitVec.ofNat 8 0x5a,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x0a,
    BitVec.ofNat 8 0xda,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0xda,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x83,
    BitVec.ofNat 8 0xbe,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x03,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0xd5,
    BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0xb0,
    BitVec.ofNat 8 0xde,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0xda,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x83,
    BitVec.ofNat 8 0xbe,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0f,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x0a,
    BitVec.ofNat 8 0xfa,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0f,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0xd5,
    BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83,
    BitVec.ofNat 8 0xbe,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x10,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x9e,
    BitVec.ofNat 8 0xce,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x61,
    BitVec.ofNat 8 0xc6,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x81,
    BitVec.ofNat 8 0xd1,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x81,
    BitVec.ofNat 8 0xf1,
    BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13,
    BitVec.ofNat 8 0x02,
    BitVec.ofNat 8 0x70,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x62,
    BitVec.ofNat 8 0x42,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0xb0,
    BitVec.ofNat 8 0x51,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6f,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0f,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0xd5,
    BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x03,
    BitVec.ofNat 8 0xbe,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x0d,
    BitVec.ofNat 8 0x10,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x1e,
    BitVec.ofNat 8 0xbe,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x6e,
    BitVec.ofNat 8 0xc6,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x8e,
    BitVec.ofNat 8 0xce,
    BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,
    BitVec.ofNat 8 0x8e,
    BitVec.ofNat 8 0xfe,
    BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83,
    BitVec.ofNat 8 0xb1,
    BitVec.ofNat 8 0x0e,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0xe1,
    BitVec.ofNat 8 0x31,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67,
    BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x00, ]

def globalArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.globalSource with
  | some bytes => bytes == globalArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing two-global binary fixture. -/
def multiGlobalArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x03,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0xd5,BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83,BitVec.ofNat 8 0xbe,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0f,BitVec.ofNat 8 0x30,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x9e,BitVec.ofNat 8 0xfe,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0x33,BitVec.ofNat 8 0xea,BitVec.ofNat 8 0x5a,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33,BitVec.ofNat 8 0x0a,BitVec.ofNat 8 0xda,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0xda,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0x83,BitVec.ofNat 8 0xbe,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x03,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0xd5,BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x23,BitVec.ofNat 8 0xb0,BitVec.ofNat 8 0xde,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0xda,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0x83,BitVec.ofNat 8 0xbe,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0f,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0x33,BitVec.ofNat 8 0x0a,BitVec.ofNat 8 0xfa,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0f,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0xd5,BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83,BitVec.ofNat 8 0xbe,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x13,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x10,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x9e,BitVec.ofNat 8 0xce,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x61,BitVec.ofNat 8 0xc6,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x81,BitVec.ofNat 8 0xd1,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x81,BitVec.ofNat 8 0xf1,BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13,BitVec.ofNat 8 0x02,BitVec.ofNat 8 0x10,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x62,BitVec.ofNat 8 0x42,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23,BitVec.ofNat 8 0xb0,BitVec.ofNat 8 0x51,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0f,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0xd5,BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83,BitVec.ofNat 8 0xbe,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x13,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x10,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x9e,BitVec.ofNat 8 0xce,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x61,BitVec.ofNat 8 0xc6,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x81,BitVec.ofNat 8 0xd1,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x81,BitVec.ofNat 8 0xf1,BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13,BitVec.ofNat 8 0x02,BitVec.ofNat 8 0x20,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x62,BitVec.ofNat 8 0x42,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23,BitVec.ofNat 8 0xb0,BitVec.ofNat 8 0x51,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x6f,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x40,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0xd5,BitVec.ofNat 8 0x41,BitVec.ofNat 8 0x03,BitVec.ofNat 8 0xbe,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0d,BitVec.ofNat 8 0x10,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x33,BitVec.ofNat 8 0x1e,BitVec.ofNat 8 0xbe,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x6f,BitVec.ofNat 8 0xc6,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x8f,BitVec.ofNat 8 0xcf,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x8f,BitVec.ofNat 8 0xdf,BitVec.ofNat 8 0x41,BitVec.ofNat 8 0x83,BitVec.ofNat 8 0xbf,BitVec.ofNat 8 0x0f,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0xd5,BitVec.ofNat 8 0x41,BitVec.ofNat 8 0x03,BitVec.ofNat 8 0xbe,BitVec.ofNat 8 0x0e,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93,BitVec.ofNat 8 0x0d,BitVec.ofNat 8 0x10,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x33,BitVec.ofNat 8 0x1e,BitVec.ofNat 8 0xbe,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x61,BitVec.ofNat 8 0xc6,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x81,BitVec.ofNat 8 0xc1,BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x81,BitVec.ofNat 8 0xd1,BitVec.ofNat 8 0x41,BitVec.ofNat 8 0x83,BitVec.ofNat 8 0xb1,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3,BitVec.ofNat 8 0x81,BitVec.ofNat 8 0xf1,BitVec.ofNat 8 0x01,BitVec.ofNat 8 0x33,BitVec.ofNat 8 0xe1,BitVec.ofNat 8 0x31,BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67,BitVec.ofNat 8 0x80,BitVec.ofNat 8 0x00,BitVec.ofNat 8 0x00,
  ]

def multiGlobalArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.multiGlobalSource with
  | some bytes => bytes == multiGlobalArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing n-ary global fixture. -/
def naryGlobalArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xea, BitVec.ofNat 8 0x5a, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0xde, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xfa, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xd1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xd1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x20, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xd1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xd1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xb1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0d, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1e, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x8f, BitVec.ofNat 8 0xcf, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x8f, BitVec.ofNat 8 0xdf, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbf, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0d, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1e, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x8f, BitVec.ofNat 8 0xcf, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x8f, BitVec.ofNat 8 0xdf, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbf, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xe1, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
  ]

def naryGlobalArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.naryGlobalSource with
  | some bytes => bytes == naryGlobalArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing global multiplication fixture. -/
def longMulGlobalArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xea, BitVec.ofNat 8 0x5a, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0xde, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xfa, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xd1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xd1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0d, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1e, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x6e, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x8e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x8e, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xb1, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0d, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1e, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x6e, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x8e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x8e, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb2, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0xb2, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x82, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x02,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xe3, BitVec.ofNat 8 0x52, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0x63, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
  ]

def longMulGlobalArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.longMulGlobalSource with
  | some bytes => bytes == longMulGlobalArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing named-struct fixture. -/
def namedStructArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xea, BitVec.ofNat 8 0x5a, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0xde, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xfa, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xe1, BitVec.ofNat 8 0x52, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xe1, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0xf0, BitVec.ofNat 8 0x9f, BitVec.ofNat 8 0xfe,
  ]

def namedStructArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.namedStructSource with
  | some bytes => bytes == namedStructArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing shared-memory fixture. -/
def sharedMemoryArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xea, BitVec.ofNat 8 0x5a, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0xde, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xfa, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x02,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xc0, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x3e,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0xc0, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x8e, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xc1, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xe2, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0xf0, BitVec.ofNat 8 0x1f, BitVec.ofNat 8 0xfe,
  ]

def sharedMemoryArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.sharedMemorySource with
  | some bytes => bytes == sharedMemoryArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing shadowing fixture. -/
def shadowingArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xea, BitVec.ofNat 8 0x5a, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0xde, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xfa, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xd1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x05,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x90, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xe1, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xfa, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbf, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xc0, BitVec.ofNat 8 0x08,
    BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0xf0, BitVec.ofNat 8 0x9f, BitVec.ofNat 8 0xfc, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xfa, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xe1, BitVec.ofNat 8 0x52, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0xf0, BitVec.ofNat 8 0xdf, BitVec.ofNat 8 0xfb,
  ]

def shadowingArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.shadowingSource with
  | some bytes => bytes == shadowingArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing global shared-load fixture. -/
def globalSharedLoadArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xea, BitVec.ofNat 8 0x5a, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0xde, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xda, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0a, BitVec.ofNat 8 0xfa, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xd1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xf1, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xc0, BitVec.ofNat 8 0x04,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb2, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0xd5, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xbe, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0e, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x9e, BitVec.ofNat 8 0xce, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0xc6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x82, BitVec.ofNat 8 0xd2, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x82, BitVec.ofNat 8 0xf2, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x63, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xb3, BitVec.ofNat 8 0x63, BitVec.ofNat 8 0x63, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xb0, BitVec.ofNat 8 0x72, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xe1, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0xf0, BitVec.ofNat 8 0x9f, BitVec.ofNat 8 0xfb,
  ]

def globalSharedLoadArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.globalSharedLoadSource with
  | some bytes => bytes == globalSharedLoadArtifactGolden
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
    checkBool "Lean global initializer exact source artifact bytes"
      globalArtifactMatchesGolden,
    checkBool "Lean multi-global exact source artifact bytes"
      multiGlobalArtifactMatchesGolden,
    checkBool "Lean n-ary global exact source artifact bytes"
      naryGlobalArtifactMatchesGolden,
    checkBool "Lean global multiplication exact source artifact bytes"
      longMulGlobalArtifactMatchesGolden,
    checkBool "Lean named-struct exact source artifact bytes"
      namedStructArtifactMatchesGolden,
    checkBool "Lean shared-memory exact source artifact bytes"
      sharedMemoryArtifactMatchesGolden,
    checkBool "Lean shadowing exact source artifact bytes"
      shadowingArtifactMatchesGolden,
    checkBool "Lean global shared-load exact source artifact bytes"
      globalSharedLoadArtifactMatchesGolden,
    checkBool "Lean source entry produces an artifact" minimalSourceArtifact,
    checkBool "Pancake computed local-store address compiles" nestedLocalStoreBytesAccepted,
    checkBool "Pancake RISC-V artifact envelope markers" ArtifactFormat.pancakeEnvelopeMatches,
    checkBool "Pancake RISC-V artifact prologue" ArtifactFormat.pancakePrologueMatches,
    Flapjack.Test.SourceGlobalParity.runChecks,
    Flapjack.Test.LoopToWord.runChecks,
    Flapjack.Test.LoopGetVarsParity.runChecks,
    Flapjack.Test.LoopSetGlobalsParity.runChecks,
    Flapjack.Test.LoopSetVarsParity.runChecks,
    Flapjack.Test.LoopSetVarParity.runChecks,
    Flapjack.Test.LoopDecClockParity.runChecks,
    Flapjack.Test.LoopFixClockParity.runChecks,
    Flapjack.Test.LoopFindCodeParity.runChecks,
    Flapjack.Test.LoopPrimopParity.runChecks,
    Flapjack.Test.LoopArithParity.runChecks,
    Flapjack.Test.PanPrimopParity.runChecks,
    Flapjack.Test.PanSetVarParity.runChecks,
    Flapjack.Test.LoopMemStoreParity.runChecks,
    Flapjack.Test.LoopMemLoadParity.runChecks,
    Flapjack.Test.LoopMemoryStateParity.runChecks,
    Flapjack.Test.LoopStateResultParity.runChecks,
    Flapjack.Test.EndToEndParity.runChecks,
    Flapjack.Test.CakeStackReseatParity.runChecks
    ].mapM id
  unless results.all id do
    IO.Process.exit 1

end Flapjack.Test.CompilerParity

def main : IO Unit := Flapjack.Test.CompilerParity.main
