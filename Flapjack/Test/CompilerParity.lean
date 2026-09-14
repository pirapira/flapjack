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
import Flapjack.Test.PanNestedSeqParity
import Flapjack.Test.PanExpIdsParity
import Flapjack.Test.PanWithShapeParity
import Flapjack.Test.PanShapeValParity
import Flapjack.Test.PanGlobalsCompileExpParity
import Flapjack.Test.PanGlobalsFreshNameParity
import Flapjack.Test.PanGlobalsCompileParity
import Flapjack.Test.PanGlobalsCompileDecsParity
import Flapjack.Test.PanGlobalsResortDeclsParity
import Flapjack.Test.PanGlobalsFpermNameParity
import Flapjack.Test.PanGlobalsFpermParity
import Flapjack.Test.PanGlobalsFpermDecsParity
import Flapjack.Test.PanGlobalsNewMainNameParity
import Flapjack.Test.PanGlobalsDecShapesParity
import Flapjack.Test.PanGlobalsCompileTopForStartParity
import Flapjack.Test.CrepeDestConstParity
import Flapjack.Test.CrepeDest2ExpParity
import Flapjack.Test.CrepeMulConstParity
import Flapjack.Test.CrepeSimpExpParity
import Flapjack.Test.CrepeSimpProgParity
import Flapjack.Test.PanStructsAfindiParity
import Flapjack.Test.PanStructsCompileShapeParity
import Flapjack.Test.PanStructsOldExpShapeParity
import Flapjack.Test.PanStructsCompileExpParity
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
import Flapjack.Test.LoopLocalsTouchedParity
import Flapjack.Test.LoopAssignedVarsParity
import Flapjack.Test.LoopVarsOfExpParity
import Flapjack.Test.LoopArithVarsParity
import Flapjack.Test.LoopShrinkParity
import Flapjack.Test.LoopMarkAllParity
import Flapjack.Test.LoopLiveCompParity
import Flapjack.Test.LoopLiveOptimiseParity
import Flapjack.Test.OCompileParity
import Flapjack.Test.LoopAccVarsParity
import Flapjack.Test.LoopNestedSeqParity
import Flapjack.Test.LoopIsLoadParity
import Flapjack.Test.LoopCallParity
import Flapjack.Test.LoopEvalParity
import Flapjack.Test.LoopEvaluateParity
import Flapjack.Test.LoopObservationalSemanticsParity
import Flapjack.Test.PanItreeFfiParity
import Flapjack.Test.PanItreeTracePrefixParity
import Flapjack.Test.PanItreeTracePrefix0Parity
import Flapjack.Test.PanItreeLtreeParity
import Flapjack.Test.PanHProgStoreParity
import Flapjack.Test.PanHProgParity
import Flapjack.Test.PanHProgLoadParity
import Flapjack.Test.PanHProgReturnParity
import Flapjack.Test.PanHProgRaiseParity
import Flapjack.Test.PanValuePcRaisedPayloadCorrectness
import Flapjack.Test.CrepeGlobalStoreCorrectness
import Flapjack.Test.PanHProgExtCallParity
import Flapjack.Test.PanHProgStoreByteParity
import Flapjack.Test.PanHProgStore32Parity
import Flapjack.Test.PanHProgPrimitiveParity
import Flapjack.Test.PanSetGlobalParity
import Flapjack.Test.PanSemSetGlobalParity
import Flapjack.Test.PanSemSetKvarParity
import Flapjack.Test.PanSemLookupKvarParity
import Flapjack.Test.PanSemIsValidValueParity
import Flapjack.Test.PanSemWriteBytearrayParity
import Flapjack.Test.PanItreeEvaluateParity
import Flapjack.Test.PanExtParity
import Flapjack.Test.PanHHandleCallRetParity
import Flapjack.Test.PanHHandleDecCallRetParity
import Flapjack.Test.PanHProgDecCallParity
import Flapjack.Test.PanHProgCallParity
import Flapjack.Test.CrepPrimopParity
import Flapjack.Test.CrepeLoadShapeParity
import Flapjack.Test.CrepeNestedSeqParity
import Flapjack.Test.CrepAssignedFreeVarsParity
import Flapjack.Test.CrepeStoresParity
import Flapjack.Test.CrepeProgramGenericRaiseCorrectness
import Flapjack.Test.CrepeNestedDecsParity
import Flapjack.Test.CrepeStoreGlobalsParity
import Flapjack.Test.CrepeLoadGlobalsParity
import Flapjack.Test.CrepeAssignRetParity
import Flapjack.Test.CrepeVarCexpParity
import Flapjack.Test.CrepExpsParity
import Flapjack.Test.CexpHeadsParity
import Flapjack.Test.CompFieldParity
import Flapjack.Test.CompilePanOpParity
import Flapjack.Test.CompileExpParity
import Flapjack.Test.ExpHdlParity
import Flapjack.Test.RetVarParity
import Flapjack.Test.RetHdlParity
import Flapjack.Test.WrapRtParity
import Flapjack.Test.CompileDefParity
import Flapjack.Test.CompileToCrepeParity
import Flapjack.Test.CompileProgParity
import Flapjack.Test.PanSimpParity
import Flapjack.Test.CrepProgIfParity
import Flapjack.Test.CompileCrepOpParity
import Flapjack.Test.CrepCompileExpParity
import Flapjack.Test.CrepExitLoopParity
import Flapjack.Test.CrepEvaluateParity
import Flapjack.Test.CrepFixClockParity
import Flapjack.Test.CrepEvalParity
import Flapjack.Test.CrepShMemLoadParity
import Flapjack.Test.CrepShMemOpParity
import Flapjack.Test.CrepShMemStoreParity
import Flapjack.Test.CrepMemLoadParity
import Flapjack.Test.CrepEvalParity
import Flapjack.Test.PanNbOpParity
import Flapjack.Test.CrepObservationalSemanticsParity
import Flapjack.Test.CrepLookupCodeParity
import Flapjack.Test.PanDecClockParity
import Flapjack.Test.PanUpdLocalsParity
import Flapjack.Test.PanBstParity
import Flapjack.Test.PanBStateUpdatesParity
import Flapjack.Test.PanBStateEmptyLocalsParity
import Flapjack.Test.PanEmptyLocalsParity
import Flapjack.Test.PanSetKvarParity
import Flapjack.Test.PanShMemLoadParity
import Flapjack.Test.PanShMemStoreParity
import Flapjack.Test.PanEvalParity
import Flapjack.Test.PanEvaluateParity
import Flapjack.Test.PanObservationalSemanticsParity
import Flapjack.Test.ParserTryDefaultParity
import Flapjack.Test.ParserExtractSumParity
import Flapjack.Test.ParserMkleafParity
import Flapjack.Test.ParserMknodeParity
import Flapjack.Test.ParserMksubtreeParity
import Flapjack.Test.ParserConsumeTokParity
import Flapjack.Test.ParserKeepTokParity
import Flapjack.Test.ParserKeepKwParity
import Flapjack.Test.ParserKeepIdentParity
import Flapjack.Test.ParserKeepAnnotParity
import Flapjack.Test.ParserTryProgParity
import Flapjack.Test.ParserPancakePegParity
import Flapjack.Test.ParserParseStatementParity
import Flapjack.Test.PanLangWfShapeParity
import Flapjack.Test.PanLangWfFieldsContextParity
import Flapjack.Test.PanHHandleCallRetParity
import Flapjack.Test.PanMrecParity
import Flapjack.Test.PanHProgDecParity
import Flapjack.Test.PanHProgSeqParity
import Flapjack.Test.PanHProgCondParity
import Flapjack.Test.PanHProgStoreMemParity
import Flapjack.Test.PanHProgAssignParity
import Flapjack.Test.PanHProgWhileParity
import Flapjack.Test.LoopCutStateParity
import Flapjack.Test.LoopCutResParity
import Flapjack.Test.LoopShMemLoadParity
import Flapjack.Test.LoopShMemStoreParity
import Flapjack.Test.LoopShMemOpParity
import Flapjack.Test.LoopGetVarImmParity
import Flapjack.Test.LoopCallEnvParity
import Flapjack.Test.InstructionTransfer
import Flapjack.Test.ArtifactFormat
import Flapjack.Test.CrepeGlobalAddressParity
import Flapjack.Test.ParsedFullSsaPipeline
import Flapjack.Test.EndToEndParity
import Flapjack.Test.RiscVArtifactParity
import Flapjack.Test.RiscVRegisterMapParity
import Flapjack.Test.CakeAllocatorCore

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
    Flapjack.Test.LoopLocalsTouchedParity.runChecks,
    Flapjack.Test.LoopAssignedVarsParity.runChecks,
    Flapjack.Test.LoopAccVarsParity.runChecks,
    Flapjack.Test.LoopNestedSeqParity.runChecks,
    Flapjack.Test.PanNestedSeqParity.runChecks,
    Flapjack.Test.PanExpIdsParity.runChecks,
    Flapjack.Test.PanWithShapeParity.runChecks,
    Flapjack.Test.PanShapeValParity.runChecks,
    Flapjack.Test.LoopIsLoadParity.runChecks,
    Flapjack.Test.LoopCallParity.runChecks,
    Flapjack.Test.LoopEvalParity.runChecks,
    Flapjack.Test.LoopEvaluateParity.runChecks,
    Flapjack.Test.LoopObservationalSemanticsParity.runChecks,
    Flapjack.Test.PanItreeFfiParity.runChecks,
    Flapjack.Test.PanItreeTracePrefixParity.runChecks,
    Flapjack.Test.PanItreeTracePrefix0Parity.runChecks,
    Flapjack.Test.PanItreeLtreeParity.runChecks,
    Flapjack.Test.PanHProgStoreParity.runChecks,
    Flapjack.Test.PanHProgParity.runChecks,
    Flapjack.Test.PanHProgLoadParity.runChecks,
    Flapjack.Test.PanHProgReturnParity.runChecks,
    Flapjack.Test.PanHProgRaiseParity.runChecks,
    Flapjack.Test.PanHProgExtCallParity.runChecks,
    Flapjack.Test.PanHProgStoreByteParity.runChecks,
    Flapjack.Test.PanHProgStore32Parity.runChecks,
    Flapjack.Test.PanHProgPrimitiveParity.runChecks,
    Flapjack.Test.PanSetGlobalParity.runChecks,
    Flapjack.Test.PanSemSetGlobalParity.runChecks,
    Flapjack.Test.PanSemSetKvarParity.runChecks,
    Flapjack.Test.PanSemLookupKvarParity.runChecks,
    Flapjack.Test.PanSemIsValidValueParity.runChecks,
    Flapjack.Test.PanSemWriteBytearrayParity.runChecks,
    Flapjack.Test.PanItreeEvaluateParity.runChecks,
    Flapjack.Test.PanExtParity.runChecks,
    Flapjack.Test.PanHHandleCallRetParity.runChecks,
    Flapjack.Test.PanHHandleDecCallRetParity.runChecks,
    Flapjack.Test.PanHProgDecCallParity.runChecks,
    Flapjack.Test.PanHProgCallParity.runChecks,
    Flapjack.Test.CrepPrimopParity.runChecks,
    Flapjack.Test.CrepeLoadShapeParity.runChecks,
    Flapjack.Test.CrepeNestedSeqParity.runChecks,
    Flapjack.Test.CrepAssignedFreeVarsParity.runChecks,
    Flapjack.Test.CrepeStoresParity.runChecks,
    Flapjack.Test.CrepeProgramGenericRaiseCorrectness.runChecks,
    Flapjack.Test.CrepeNestedDecsParity.runChecks,
    Flapjack.Test.CrepeStoreGlobalsParity.runChecks,
    Flapjack.Test.CrepeLoadGlobalsParity.runChecks,
    Flapjack.Test.CrepeAssignRetParity.runChecks,
    Flapjack.Test.CrepeVarCexpParity.runChecks,
    Flapjack.Test.CrepExpsParity.runChecks,
    Flapjack.Test.CexpHeadsParity.runChecks,
    Flapjack.Test.CompFieldParity.runChecks,
    Flapjack.Test.CompilePanOpParity.runChecks,
    Flapjack.Test.CompileExpParity.runChecks,
    Flapjack.Test.ExpHdlParity.runChecks,
    Flapjack.Test.RetVarParity.runChecks,
    Flapjack.Test.RetHdlParity.runChecks,
    Flapjack.Test.WrapRtParity.runChecks,
    Flapjack.Test.CompileDefParity.runChecks,
    Flapjack.Test.CompileToCrepeParity.runChecks,
    Flapjack.Test.CompileProgParity.runChecks,
    Flapjack.Test.PanSimpParity.runChecks,
    Flapjack.Test.CrepExitLoopParity.runChecks,
    Flapjack.Test.CrepEvaluateParity.runChecks,
    Flapjack.Test.CrepFixClockParity.runChecks,
    Flapjack.Test.CrepEvalParity.runChecks,
    Flapjack.Test.CrepShMemLoadParity.runChecks,
    Flapjack.Test.CrepShMemOpParity.runChecks,
    Flapjack.Test.CrepShMemStoreParity.runChecks,
    Flapjack.Test.CrepMemLoadParity.runChecks,
    Flapjack.Test.CrepEvalParity.runChecks,
    Flapjack.Test.PanNbOpParity.runChecks,
    Flapjack.Test.CrepObservationalSemanticsParity.runChecks,
    Flapjack.Test.CrepLookupCodeParity.runChecks,
    Flapjack.Test.PanDecClockParity.runChecks,
    Flapjack.Test.PanUpdLocalsParity.runChecks,
    Flapjack.Test.PanBstParity.runChecks,
    Flapjack.Test.PanBStateUpdatesParity.runChecks,
    Flapjack.Test.PanBStateEmptyLocalsParity.runChecks,
    Flapjack.Test.PanEmptyLocalsParity.runChecks,
    Flapjack.Test.PanSetKvarParity.runChecks,
    Flapjack.Test.PanShMemLoadParity.runChecks,
    Flapjack.Test.PanShMemStoreParity.runChecks,
    Flapjack.Test.PanEvalParity.runChecks,
    Flapjack.Test.PanEvaluateParity.runChecks,
    Flapjack.Test.PanObservationalSemanticsParity.runChecks,
    Flapjack.Test.PanHHandleCallRetParity.runChecks,
    Flapjack.Test.PanMrecParity.runChecks,
    Flapjack.Test.PanHProgDecParity.runChecks,
    Flapjack.Test.PanHProgSeqParity.runChecks,
    Flapjack.Test.PanHProgCondParity.runChecks,
    Flapjack.Test.PanHProgStoreMemParity.runChecks,
    Flapjack.Test.PanHProgAssignParity.runChecks,
    Flapjack.Test.PanHProgWhileParity.runChecks,
    Flapjack.Test.LoopCutStateParity.runChecks,
    Flapjack.Test.LoopCutResParity.runChecks,
    Flapjack.Test.LoopShMemLoadParity.runChecks,
    Flapjack.Test.LoopShMemStoreParity.runChecks,
    Flapjack.Test.LoopShMemOpParity.runChecks,
    Flapjack.Test.LoopGetVarImmParity.runChecks,
    Flapjack.Test.LoopCallEnvParity.runChecks,
    Flapjack.Test.EndToEndParity.runChecks,
    Flapjack.Test.CakeStackReseatParity.runChecks,
    Flapjack.Test.CrepeGlobalAddressParity.runChecks,
    Flapjack.Test.RiscVArtifactParity.runChecks,
    Flapjack.Test.RiscVRegisterMapParity.runChecks,
    Flapjack.Test.CakeAllocatorCore.runChecks
    ].mapM id
  unless results.all id do
    IO.Process.exit 1

end Flapjack.Test.CompilerParity

def main : IO Unit := Flapjack.Test.CompilerParity.main
