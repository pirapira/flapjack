import Flapjack.RiscV.Encoding
import Flapjack.Test.RiscVColourLivenessParity
import Flapjack.Test.PipelineDiagnostics
import Flapjack.Test.SourceGlobalParity
import Flapjack.Test.RegisterTransfer
import Flapjack.Test.PanMemoryParity
import Flapjack.Test.PanShapeParity
import Flapjack.Test.PanShapeVarsParity
import Flapjack.Test.PanStructsCompileCorrect
import Flapjack.Test.PanStructsValueValidityParity
import Flapjack.Test.PanPropsShapeOfWfParity
import Flapjack.Test.PanPropsEveryExpParity
import Flapjack.Test.PanPropsExpsOfParity
import Flapjack.Test.PanPropsLocalisedParity
import Flapjack.Test.PanGetEidsParity
import Flapjack.Test.PanWordParity
import Flapjack.Test.PanEvaluateDeclsParity
import Flapjack.Test.LabPositionParity
import Flapjack.Test.PanOpParity
import Flapjack.Test.PanFixedLoadParity
import Flapjack.Test.PanFixedStoreParity
import Flapjack.Test.PanFlatStoreParity
import Flapjack.Test.PanFlattenParity
import Flapjack.Test.PanNestedSeqParity
import Flapjack.Test.PanExpIdsParity
import Flapjack.Test.PanLangFunIdsParity
import Flapjack.Test.PanLangFreeVarIdsParity
import Flapjack.Test.PanLangShapeHOLParity
import Flapjack.Test.PanLangExpHOLParity
import Flapjack.Test.PanLangProgHOLParity
import Flapjack.Test.PanLangDeclHOLParity
import Flapjack.Test.PanWithShapeParity
import Flapjack.Test.CrepInlineGenlistParity
import Flapjack.Test.CrepInlineRelParity
import Flapjack.Test.CrepSemTotalClockLeavesParity
import Flapjack.Test.CrepSemTotalCallParity
import Flapjack.Pancake.Proofs.PanToCrep.TotalEvaluateCases
import Flapjack.Test.CrepSemTotalAssignParity
import Flapjack.Test.CrepSemTotalStoreParity
import Flapjack.Test.CrepSemTotalShMemParity
import Flapjack.Test.CrepSemTotalExtCallParity
import Flapjack.Test.CrepInlineFmapParity
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
import Flapjack.Test.PanGlobalsNameByteRangedParity
import Flapjack.Test.PanGlobalsDecShapesParity
import Flapjack.Test.PanGlobalsExpIdsParity
import Flapjack.Test.PanGlobalsCompileTopForStartParity
import Flapjack.Test.PanGlobalsCompileTopShapeWfParity
import Flapjack.Test.PanGlobalsExceptionsAppendParity
import Flapjack.Test.PanGlobalsExceptionsFilterIsFunctionParity
import Flapjack.Test.PanGlobalsDeclPredicateParity
import Flapjack.Test.PanGlobalsFunctionsFilterNilParity
import Flapjack.Test.PanGlobalsMemFunctionsHOLParity
import Flapjack.Test.PanGlobalsFpermClusterParity
import Flapjack.Test.PanGlobalsDecShapesClusterParity
import Flapjack.Test.PanGlobalsFunctionPreservationParity
import Flapjack.Test.PanGlobalsNameCorrectnessParity
import Flapjack.Test.PanGlobalsFreshNameFilterParity
import Flapjack.Test.PanGlobalsCompileDecsStructuralParity
import Flapjack.Test.PanGlobalsCompileDecsThreadingParity
import Flapjack.Test.PanGlobalsAlookupMapParity
import Flapjack.Test.PanLangFunctionsParity
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
import Flapjack.Test.PanSetVarParity
import Flapjack.Test.CakeStackReseatParity
import Flapjack.Test.LoopSetGlobalsParity
import Flapjack.Test.LoopSetVarsParity
import Flapjack.Test.LoopSetVarParity
import Flapjack.Test.LoopDecClockParity
import Flapjack.Test.LoopFixClockParity
import Flapjack.Test.LoopFindCodeParity
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
import Flapjack.Test.LoopObservationalSemanticsParity
import Flapjack.Test.LoopSemEvaluateParity
import Flapjack.Test.LoopLiveEffectFreeParity
import Flapjack.Test.LoopPrimopParity
import Flapjack.Test.LoopShMemParity
import Flapjack.Test.LoopFfiParity
import Flapjack.Test.LoopMemExactParity
import Flapjack.Test.PanItreeFfiParity
import Flapjack.Test.PanItreeTracePrefixParity
import Flapjack.Test.PanItreeTracePrefix0Parity
import Flapjack.Test.PanItreeLtreeParity
import Flapjack.Test.PanHProgStoreParity
import Flapjack.Test.PanHProgParity
import Flapjack.Test.PanHProgLoadParity
import Flapjack.Test.PanHProgReturnParity
import Flapjack.Test.PanHProgRaiseParity
import Flapjack.Test.PanValueFfiClockLe
import Flapjack.Test.PanValueEvaluatorStability
import Flapjack.Test.PanToCrepMaxListParity
import Flapjack.Test.PanToCrepRelationsParity
import Flapjack.Test.PanToCrepUtilitiesParity
import Flapjack.Test.BackendCommonCarryParity
import Flapjack.Test.PanCrepPrimopParity
import Flapjack.Test.CompileProgParamsParity
import Flapjack.Test.PanToCrepCodeRelParity
import Flapjack.Test.PanToCrepStateRelParity
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
import Flapjack.Test.CrepeLoadShapeParity
import Flapjack.Test.CrepToLoopCutsetParity
import Flapjack.Test.CrepToLoopParity
import Flapjack.Test.CrepToLoopDecLive
import Flapjack.Test.CakeRegAlloc
import Flapjack.Test.WordDeadCodeParity
import Flapjack.Test.CrepeNestedSeqParity
import Flapjack.Test.CrepeStoresParity
import Flapjack.Test.CrepeNestedDecsParity
import Flapjack.Test.CrepeStoreGlobalsParity
import Flapjack.Test.CrepGlobalShapeParity
import Flapjack.Test.CrepLookupCodeHOLParity
import Flapjack.Test.CrepExpHOLParity
import Flapjack.Test.CrepProgHOLParity
import Flapjack.Test.CrepEvalConstructorParity
import Flapjack.Test.CrepLocalsWordLabParity
import Flapjack.Test.CrepMemoryRelParity
import Flapjack.Test.CrepSemStateExactParity
import Flapjack.Test.CrepFuelCutoffParity
import Flapjack.Test.PanToCrepGlobalsLookupParity
import Flapjack.Test.PanToCrepCallExceptionParity
import Flapjack.Test.PanToCrepCallExceptionHandlerParity
import Flapjack.Test.CrepeAssignRetParity
import Flapjack.Test.CrepeVarCexpParity
import Flapjack.Test.CrepExpsParity
import Flapjack.Test.CexpHeadsParity
import Flapjack.Test.CompFieldParity
import Flapjack.Test.CompilePanOpParity
import Flapjack.Test.CompileExpParity
import Flapjack.Test.ExpHdlParity
import Flapjack.Test.ExpHdlHOLParity
import Flapjack.Test.RetVarParity
import Flapjack.Test.RetHdlParity
import Flapjack.Test.WrapRtParity
import Flapjack.Test.CompileDefParity
import Flapjack.Test.CompileToCrepeParity
import Flapjack.Test.CompileProgParity
import Flapjack.Test.DupExnEidsParity
import Flapjack.Test.CrepRuntimeTargetParity
import Flapjack.Test.CrepRuntimeFfiTargetParity
import Flapjack.Test.CrepRuntimeExtCallStateRelParity
import Flapjack.Test.CrepEveryExpParity
import Flapjack.Test.CrepAssignedVarsParity
import Flapjack.Test.MkCtxtImpLocalsRelParity
import Flapjack.Test.FmEmptyZipAlistParity
import Flapjack.Test.PanSimpParity
import Flapjack.Test.PanProgramSimpParity
import Flapjack.Test.PanValueWfParity
import Flapjack.Test.CrepeCompileExpVariablesParity
import Flapjack.Test.PanSimpOthersParity
import Flapjack.Test.CrepProgIfParity
import Flapjack.Test.CompileCrepOpParity
import Flapjack.Test.CrepCompileExpParity
import Flapjack.Test.CrepExitLoopParity
import Flapjack.Test.PanNbOpParity
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
import Flapjack.Test.PanSemLookupCodeParity
import Flapjack.Test.PanSemTickParity
import Flapjack.Test.PanSemSkipParity
import Flapjack.Test.PanSemAssignParity
import Flapjack.Test.PanSemDecParity
import Flapjack.Test.PanSemPrimitiveParity
import Flapjack.Test.PanSemErrorPropagationParity
import Flapjack.Test.PanSemWhileErrorParity
import Flapjack.Test.PanSemReturnRaiseErrorParity
import Flapjack.Test.PanSemExtCallErrorParity
import Flapjack.Test.PanSemSeqParity
import Flapjack.Test.PanSemTotalParity
import Flapjack.Test.PanSemTotalStepsParity
import Flapjack.Test.PanSemTotalEvalExactParity
import Flapjack.Test.PanRiscVByteAlignParity
import Flapjack.Test.PanSemValueHOLParity
import Flapjack.Test.PanSemStateExactParity
import Flapjack.Test.PanSemLocalUpdatesExactParity
import Flapjack.Test.PanPropsShapeResVarParity
import Flapjack.Test.PanCommonPropsZipDisjointParity
import Flapjack.Test.CrepPropsAssignedVarsParity
import Flapjack.Test.PanSemIsValidValueExactParity
import Flapjack.Test.PanSemDecExactParity
import Flapjack.Test.PanSemAssignPrimitiveExactParity
import Flapjack.Test.PanSemReturnRaiseExactParity
import Flapjack.Test.PanSemIteParity
import Flapjack.Test.PanSemAssignMemoryParity
import Flapjack.Test.PanSemReturnRaiseMemoryParity
import Flapjack.Test.PanSemEvalExactParity
import Flapjack.Test.PanSemStoreExactParity
import Flapjack.Test.PanSemTickShMemExactParity
import Flapjack.Test.PanSemExtCallExactParity
import Flapjack.Test.PanSemDecCallExactParity
import Flapjack.Test.PanSemCallExactParity
import Flapjack.Test.PanSemControlExactParity
import Flapjack.Test.PanSemEvaluateDeclsExactParity
import Flapjack.Test.PanSemClockExactParity
import Flapjack.Test.PanSemStateSimpExactParity
import Flapjack.Test.PanSemStateDefsExactParity
import Flapjack.Test.PanSemMemByteAssemblyParity
import Flapjack.Test.PanSemMemLoad32AltParity
import Flapjack.Test.PanSemMemStore32AltParity
import Flapjack.Test.PanSemCallErrorExactParity
import Flapjack.Test.PanSemDecErrorExactParity
import Flapjack.Test.PanSemPrimitiveErrorExactParity
import Flapjack.Test.PanSemAssignErrorExactParity
import Flapjack.Test.PanSemStoreErrorExactParity
import Flapjack.Test.PanSemStore32ErrorExactParity
import Flapjack.Test.PanSemIteErrorExactParity
import Flapjack.Test.PanSemFuelDecompositionParity
import Flapjack.Test.CrepReplicateConstParity
import Flapjack.Test.WordConvsLabelsRelParity
import Flapjack.Test.WordLangExtractLabelsParity
import Flapjack.Test.WordLangInstPredsParity
import Flapjack.Test.WordLangFlatExpParity
import Flapjack.Test.WordLangInstOkLessParity
import Flapjack.Test.WordLangFullInstOkLessParity
import Flapjack.Test.WordLangCallArgParity
import Flapjack.Test.RegAllocVarParity
import Flapjack.Test.WordLangNotCreatedParity
import Flapjack.Test.WordLangEveryVarParity
import Flapjack.Test.WordLangGoodHandlersParity
import Flapjack.Test.NumSetAuditParity
import Flapjack.Test.WordLangEveryNameParity
import Flapjack.Test.WordLangAllocConventionsParity
import Flapjack.Test.LabPropsLineOkPreParity
import Flapjack.Test.LabPropsSecEndsLabelParity
import Flapjack.Test.CakeAllocatorBitsBridgeParity
import Flapjack.Test.StackNamesParity
import Flapjack.Test.StackRemoveInitParity
import Flapjack.Test.WordLocWParity
import Flapjack.Test.StackRemoveHelpersParity
import Flapjack.Test.LoopSemStateParity
import Flapjack.Test.LoopLangExpParity
import Flapjack.Test.LoopLangProgParity
import Flapjack.Test.SptreeParity
import Flapjack.Test.MlStringCodecParity
import Flapjack.Test.MlStringParity
import Flapjack.Test.MlStringBridgeParity
import Flapjack.Test.StackLangInstOverloadsParity
import Flapjack.Test.RiscvConfigParity
import Flapjack.Test.MiscAppListParity
import Flapjack.Test.StackToLabFlattenOpsParity
import Flapjack.Test.StackToLabFlattenBaseParity
import Flapjack.Test.StackToLabFlattenAppParity
import Flapjack.Test.AsmConfigChecksParity
import Flapjack.Test.PanSemDecCallErrorParity
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
import Flapjack.Test.ParserByteNamesParity
import Flapjack.Test.ParserByteRangedParity
import Flapjack.Test.ParserKeywordParity
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
import Flapjack.Test.RiscVMemOpParity
import Flapjack.Test.RiscVArtifactParity
import Flapjack.Test.RiscVWordExtract6Parity
import Flapjack.Test.RiscVEncodeLengthParity
import Flapjack.Test.WordColourLivenessParity
import Flapjack.Test.RiscVMemOpParity
import Flapjack.Test.RiscVRegisterMapParity
import Flapjack.Test.CakeAllocatorCore
import Flapjack.Test.CakeFramePolicy
import Flapjack.Test.CakeFrameContainment
import Flapjack.Test.WordStackCallParity
import Flapjack.Test.StackRawCall
import Flapjack.Test.WordInstNormalizeParity
import Flapjack.Test.WordInstSelectParity
import Flapjack.Test.WordStackLoadOffsetParity
import Flapjack.Test.CakeTailCallSsaParity
import Flapjack.Test.CakeForcedParity
import Flapjack.Test.CakeMkBijParity
import Flapjack.Test.CakeSsaSetupParity
import Flapjack.Test.ShapeToStringParity
import Flapjack.Test.CakeApplyColourParity
import Flapjack.Test.CakeSsaTempParity
import Flapjack.Test.CakeSsaBoundaryParity
import Flapjack.Test.CakeSsaControlParity
import Flapjack.Test.CakeSsaCallParity
import Flapjack.Test.CakeSsaInstParity
import Flapjack.Test.CakeWordAllocParity
import Flapjack.Test.CakeSsaSharedParity
import Flapjack.Test.CakeSsaMemoryParity
import Flapjack.Test.CakeSsaLeafParity
import Flapjack.Test.CakeDeadCodeStateParity
import Flapjack.Test.CakeReturnSoundness
import Flapjack.Test.CakeCompileSingleCorrectness
import Flapjack.Test.CakeApplyColourParity
import Flapjack.Test.CakeSpillCostParity
import Flapjack.Test.CakeFrameVectorParity
import Flapjack.Test.WordFuseConditions
import Flapjack.Test.RiscVAbiParity
import Flapjack.Test.RiscVAbiAdapterParity
import Flapjack.Test.LoopToWordBoundaryParity
import Flapjack.Test.SptreeOrderParity
import Flapjack.Test.WordSimpSeqAssocParity
import Flapjack.Test.RiscVFarTransferParity
import Flapjack.Test.FfiHOLParity
import Flapjack.Test.FfiBridgeParity
import Flapjack.Test.PanLangShapeSizeWithContextParity
import Flapjack.Test.PanLangShapeSizeParity
import Flapjack.Test.PanLangIsWfShapeParity
import Flapjack.Test.PanLangExceptionsParity
import Flapjack.Test.PanLangVarExpParity
import Flapjack.Test.PanSemIsValWordHOLParity
import Flapjack.Test.PanSemEmptyLocalsHOLParity
import Flapjack.Test.PanSemMemStore32HOLParity
import Flapjack.Test.PanSemMemStoreHOLParity
import Flapjack.Test.PanSemShMemHOLParity
import Flapjack.Test.PanSemDecsStcnamesHOLParity
import Flapjack.Test.PanSemMemLoadExactParity

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

/-! Cake's byte-load-with-offset instruction is an RV `lb` (funct3 4), not
    the funct3 0 encoding.  This pins the field exposed by the
    source-to-RISC-V differential fuzzer. -/
def cakeLoadByteOffsetWords : List (BitVec 8) :=
  RiscV.encodeInstructionBytes
    (.loadByteOffset 10 5 (BitVec.ofNat 64 8))

def cakeLoadByteOffsetEncodingParity : Bool :=
  cakeLoadByteOffsetWords ==
    [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xC5,
      BitVec.ofNat 8 0x82, BitVec.ofNat 8 0x00 ]

#guard cakeLoadByteOffsetEncodingParity

def leanReturnWords (value : Nat) : List (BitVec 8) :=
  RiscV.encodeInstructions
    [.ori 10 0 (BitVec.ofNat 64 value), .jalr 0 1 0]

/-! The exact Lean source-entry bytes are pinned separately from the
    Cake-derived section-shape golden in SourceGlobalParity. -/
/-! These Lean source-entry byte vectors are exact regression pins for the
    checked source entry point (`compileSourceBytes`).  They are refreshed when
    the source pipeline changes its Cake-compatible ABI or instruction
    filtering, most recently after the Cake base+offset memory addressing mode
    (`Addr base offset`) was fused at the Lab boundary.  The Cake-derived
    section goldens remain separately pinned in
    `Flapjack/Test/SourceGlobalParity.lean`; the residual byte-level gap to the
    original Cake artifact is tracked by `flapjack-pxn.8.5.10.4` (register/ABI
    parity). -/

def rotateArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xEA, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0xDA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xD5, BitVec.ofNat 8 0xFD, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0x50, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6D, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x04,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8F, BitVec.ofNat 8 0xBF, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9F, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xDE, BitVec.ofNat 8 0xB1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xEE, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xEF, BitVec.ofNat 8 0xDE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xE2, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0xF2, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x60, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00
  ]

def rotateArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.rotateSource with
  | some bytes => bytes == rotateArtifactGolden
  | none => false

/-! Exact source-entry golden for the existing global initializer fixture. -/
def globalArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xEA, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0xDA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xD5, BitVec.ofNat 8 0xFD, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x70, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6D, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1E, BitVec.ofNat 8 0xBE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xB1, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE0, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00
  ]

def globalArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.globalSource with
  | some bytes => bytes == globalArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing two-global binary fixture. -/
def multiGlobalArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xEA, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0xDA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xD5, BitVec.ofNat 8 0xFD, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x20, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6D, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1E, BitVec.ofNat 8 0xBE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8F, BitVec.ofNat 8 0xCF, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8F, BitVec.ofNat 8 0xDF, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xBF, BitVec.ofNat 8 0x0F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6D, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1E, BitVec.ofNat 8 0xBE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xC1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xB1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE0, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00
  ]

def multiGlobalArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.multiGlobalSource with
  | some bytes => bytes == multiGlobalArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing n-ary global fixture. -/
def naryGlobalArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xEA, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0xDA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xD5, BitVec.ofNat 8 0xFD, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x20, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xB1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6D, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1E, BitVec.ofNat 8 0xBE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8F, BitVec.ofNat 8 0xCF, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8F, BitVec.ofNat 8 0xDF, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xBF, BitVec.ofNat 8 0x0F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6D, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1E, BitVec.ofNat 8 0xBE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8F, BitVec.ofNat 8 0xCF, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8F, BitVec.ofNat 8 0xDF, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xBF, BitVec.ofNat 8 0x0F, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE0, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00
  ]

def naryGlobalArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.naryGlobalSource with
  | some bytes => bytes == naryGlobalArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing global multiplication fixture. -/
def longMulGlobalArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xEA, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0xDA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xD5, BitVec.ofNat 8 0xFD, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6D, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1E, BitVec.ofNat 8 0xBE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xB1, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6D, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x1E, BitVec.ofNat 8 0xBE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xB2, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xB2, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x02,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x82, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xE3, BitVec.ofNat 8 0x52, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x60, BitVec.ofNat 8 0x63, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00
  ]

def longMulGlobalArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.longMulGlobalSource with
  | some bytes => bytes == longMulGlobalArtifactGolden
  | none => false
def namedStructArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xEA, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0xDA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xD5, BitVec.ofNat 8 0xFD, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE0, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE0, BitVec.ofNat 8 0x52, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00
  ]

def namedStructArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.namedStructSource with
  | some bytes => bytes == namedStructArtifactGolden
  | none => false
/-! Exact source-entry golden for the existing shared-memory fixture. -/
def sharedMemoryArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xEA, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0xDA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xD5, BitVec.ofNat 8 0xFD, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC0, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x3E,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x8E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xC1, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xE2, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x60, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00
  ]

def sharedMemoryArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.sharedMemorySource with
  | some bytes => bytes == sharedMemoryArtifactGolden
  | none => false
/-! Source-entry regression for the existing shadowing fixture.

The authoritative Cake comparison is the exact corpus manifest, which compares
every section's base and bytes. -/
def shadowingArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xEA, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0xDA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xD5, BitVec.ofNat 8 0xFD, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0x90, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE0, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0xE3, BitVec.ofNat 8 0x7E, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x65, BitVec.ofNat 8 0x20, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0xF0, BitVec.ofNat 8 0x1F, BitVec.ofNat 8 0xF8, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0xFA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x0F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x0D,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xFA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3F, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x38, BitVec.ofNat 8 0xFA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x4A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x8F, BitVec.ofNat 8 0x5F, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xDF, BitVec.ofNat 8 0xDF, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xF5, BitVec.ofNat 8 0xFD,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xE3, BitVec.ofNat 8 0x70, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0xFD,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x65, BitVec.ofNat 8 0x20, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0xF0, BitVec.ofNat 8 0x5F, BitVec.ofNat 8 0xF4,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3F, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0xFA, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x0C, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0xF0, BitVec.ofNat 8 0xDF, BitVec.ofNat 8 0xF9,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3F, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xF5, BitVec.ofNat 8 0xFD,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0xF0, BitVec.ofNat 8 0x1F, BitVec.ofNat 8 0xF3, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE0, BitVec.ofNat 8 0x52, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00
  ]
def shadowingArtifactMatchesGolden : Bool :=
  match Flapjack.Test.SourceGlobalParity.compileSourceBytes
      Flapjack.Test.SourceGlobalParity.shadowingSource with
  | some bytes => bytes == shadowingArtifactGolden
  | none => false

/-! Exact source-entry golden for the existing global shared-load fixture. -/
def globalSharedLoadArtifactGolden : List (BitVec 8) :=
  [
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFC, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xEA, BitVec.ofNat 8 0x5A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0xDA, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0x34, BitVec.ofNat 8 0xD5, BitVec.ofNat 8 0xFD, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x0A, BitVec.ofNat 8 0x8A, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x0E, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xD1, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x81, BitVec.ofNat 8 0xF1, BitVec.ofNat 8 0x41, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x51, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xB2, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x6E, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x9E, BitVec.ofNat 8 0xCE, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x62, BitVec.ofNat 8 0xC6, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x82, BitVec.ofNat 8 0xD2, BitVec.ofNat 8 0x01, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x82, BitVec.ofNat 8 0xF2, BitVec.ofNat 8 0x41,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x63, BitVec.ofNat 8 0x42, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x63, BitVec.ofNat 8 0x63, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x23, BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x72, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x61, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE0, BitVec.ofNat 8 0x31, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00
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
    checkBool "Lean source entry produces an artifact" minimalSourceArtifact,
    checkBool "Pancake computed local-store address compiles" nestedLocalStoreBytesAccepted,
    checkBool "Pancake RISC-V artifact envelope markers" ArtifactFormat.pancakeEnvelopeMatches,
    checkBool "Pancake RISC-V artifact prologue" ArtifactFormat.pancakePrologueMatches,
    Flapjack.Test.SourceGlobalParity.runChecks,
    checkBool "shadowing global source remains accepted"
      Flapjack.Test.SourceGlobalParity.shadowingBytesAccepted,
    Flapjack.Test.LoopSetGlobalsParity.runChecks,
    Flapjack.Test.LoopSetVarsParity.runChecks,
    Flapjack.Test.LoopSetVarParity.runChecks,
    Flapjack.Test.LoopDecClockParity.runChecks,
    Flapjack.Test.LoopFixClockParity.runChecks,
    Flapjack.Test.LoopFindCodeParity.runChecks,
    Flapjack.Test.LoopArithParity.runChecks,
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
    Flapjack.Test.CrepInlineGenlistParity.runChecks,
    Flapjack.Test.CrepInlineFmapParity.runChecks,
    Flapjack.Test.CrepInlineRelParity.runChecks,
    Flapjack.Test.PanGlobalsExceptionsAppendParity.runChecks,
    Flapjack.Test.PanGlobalsExceptionsFilterIsFunctionParity.runChecks,
    Flapjack.Test.PanGlobalsDeclPredicateParity.runChecks,
    Flapjack.Test.PanGlobalsFunctionsFilterNilParity.runChecks,
    Flapjack.Test.PanGlobalsMemFunctionsHOLParity.runChecks,
    Flapjack.Test.PanGlobalsFpermNameParity.runChecks,
    Flapjack.Test.PanGlobalsFpermParity.runChecks,
    Flapjack.Test.PanGlobalsFpermDecsParity.runChecks,
    Flapjack.Test.PanGlobalsResortDeclsParity.runChecks,
    Flapjack.Test.PanGlobalsDecShapesParity.runChecks,
    Flapjack.Test.PanGlobalsFpermClusterParity.runChecks,
    Flapjack.Test.PanGlobalsDecShapesClusterParity.runChecks,
    Flapjack.Test.PanGlobalsFunctionPreservationParity.runChecks,
    Flapjack.Test.PanGlobalsNameCorrectnessParity.runChecks,
    Flapjack.Test.PanGlobalsFreshNameFilterParity.runChecks,
    Flapjack.Test.PanGlobalsCompileDecsStructuralParity.runChecks,
    Flapjack.Test.PanGlobalsCompileDecsThreadingParity.runChecks,
    Flapjack.Test.PanGlobalsAlookupMapParity.runChecks,
    Flapjack.Test.PanLangFunctionsParity.runChecks,
    Flapjack.Test.PanLangWfShapeParity.runChecks,
    Flapjack.Test.PanShapeValParity.runChecks,
    Flapjack.Test.LoopIsLoadParity.runChecks,
    Flapjack.Test.LoopCallParity.runChecks,
    Flapjack.Test.LoopEvalParity.runChecks,
    Flapjack.Test.LoopObservationalSemanticsParity.runChecks,
    Flapjack.Test.LoopSemEvaluateParity.runChecks,
    Flapjack.Test.LoopLiveEffectFreeParity.runChecks,
    Flapjack.Test.LoopPrimopParity.runChecks,
    Flapjack.Test.LoopShMemParity.runChecks,
    Flapjack.Test.LoopFfiParity.runChecks,
    Flapjack.Test.LoopMemExactParity.runChecks,
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
    Flapjack.Test.CrepeLoadShapeParity.runChecks,
    Flapjack.Test.CrepToLoopCutsetParity.runChecks,
    Flapjack.Test.CrepToLoopParity.runChecks,
    Flapjack.Test.CrepToLoopDecLive.runChecks,
    Flapjack.Test.CakeRegAlloc.runChecks,
    Flapjack.Test.CakeWordAllocParity.runChecks,
    Flapjack.Test.CrepeNestedSeqParity.runChecks,
    Flapjack.Test.CrepeStoresParity.runChecks,
    Flapjack.Test.CrepeNestedDecsParity.runChecks,
    Flapjack.Test.CrepeStoreGlobalsParity.runChecks,
    Flapjack.Test.CrepeAssignRetParity.runChecks,
    Flapjack.Test.CrepeVarCexpParity.runChecks,
    Flapjack.Test.CrepExpsParity.runChecks,
    Flapjack.Test.CexpHeadsParity.runChecks,
    Flapjack.Test.CompFieldParity.runChecks,
    Flapjack.Test.CompilePanOpParity.runChecks,
    Flapjack.Test.CompileExpParity.runChecks,
    Flapjack.Test.ExpHdlParity.runChecks,
    Flapjack.Test.ExpHdlHOLParity.runChecks,
    Flapjack.Test.RetVarParity.runChecks,
    Flapjack.Test.RetHdlParity.runChecks,
    Flapjack.Test.WrapRtParity.runChecks,
    Flapjack.Test.CompileDefParity.runChecks,
    Flapjack.Test.CompileToCrepeParity.runChecks,
    Flapjack.Test.CompileProgParity.runChecks,
    Flapjack.Test.DupExnEidsParity.runChecks,
    Flapjack.Test.CrepRuntimeTargetParity.runChecks,
    Flapjack.Test.CrepRuntimeFfiTargetParity.runChecks,
    Flapjack.Test.CrepRuntimeExtCallStateRelParity.runChecks,
    Flapjack.Test.CrepEveryExpParity.runChecks,
    Flapjack.Test.CrepAssignedVarsParity.runChecks,
    Flapjack.Test.MkCtxtImpLocalsRelParity.runChecks,
    Flapjack.Test.FmEmptyZipAlistParity.runChecks,
    Flapjack.Test.PanToCrepRelationsParity.runChecks,
    Flapjack.Test.PanToCrepCodeRelParity.runChecks,
    Flapjack.Test.PanToCrepStateRelParity.runChecks,
    Flapjack.Test.PanSimpParity.runChecks,
    Flapjack.Test.CrepExitLoopParity.runChecks,
    Flapjack.Test.PanNbOpParity.runChecks,
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
    Flapjack.Test.PanSemLookupCodeParity.runChecks,
    Flapjack.Test.PanSemTickParity.runChecks,
    Flapjack.Test.PanSemSkipParity.runChecks,
    Flapjack.Test.PanSemAssignParity.runChecks,
    Flapjack.Test.PanSemDecParity.runChecks,
    Flapjack.Test.PanSemPrimitiveParity.runChecks,
    Flapjack.Test.PanSemErrorPropagationParity.runChecks,
    Flapjack.Test.PanSemWhileErrorParity.runChecks,
    Flapjack.Test.PanSemReturnRaiseErrorParity.runChecks,
    Flapjack.Test.PanSemExtCallErrorParity.runChecks,
    Flapjack.Test.PanSemSeqParity.runChecks,
    Flapjack.Test.PanSemTotalParity.runChecks,
    Flapjack.Test.PanSemTotalStepsParity.runChecks,
    Flapjack.Test.PanSemTotalEvalExactParity.runChecks,
    Flapjack.Test.PanRiscVByteAlignParity.runChecks,
    Flapjack.Test.PanSemValueHOLParity.runChecks,
    Flapjack.Test.PanSemStateExactParity.runChecks,
    Flapjack.Test.PanSemLocalUpdatesExactParity.runChecks,
    Flapjack.Test.PanPropsShapeResVarParity.runChecks,
    Flapjack.Test.PanCommonPropsZipDisjointParity.runChecks,
    Flapjack.Test.CrepPropsAssignedVarsParity.runChecks,
    Flapjack.Test.PanSemIsValidValueExactParity.runChecks,
    Flapjack.Test.PanSemDecExactParity.runChecks,
    Flapjack.Test.PanSemAssignPrimitiveExactParity.runChecks,
    Flapjack.Test.PanSemReturnRaiseExactParity.runChecks,
    Flapjack.Test.PanSemIteParity.runChecks,
    Flapjack.Test.PanSemAssignMemoryParity.runChecks,
Flapjack.Test.PanSemReturnRaiseMemoryParity.runChecks,
    Flapjack.Test.PanSemEvalExactParity.runChecks,
  Flapjack.Test.PanSemStoreExactParity.runChecks,
  Flapjack.Test.PanSemTickShMemExactParity.runChecks,
  Flapjack.Test.PanSemExtCallExactParity.runChecks,
  Flapjack.Test.PanSemDecCallExactParity.runChecks,
  Flapjack.Test.PanSemCallExactParity.runChecks,
  Flapjack.Test.PanSemControlExactParity.runChecks,
  Flapjack.Test.PanSemEvaluateDeclsExactParity.runChecks,
  Flapjack.Test.PanSemClockExactParity.runChecks,
  Flapjack.Test.PanSemStateSimpExactParity.runChecks,
  Flapjack.Test.PanSemStateDefsExactParity.runChecks,
  Flapjack.Test.PanSemMemByteAssemblyParity.runChecks,
  Flapjack.Test.PanSemMemLoad32AltParity.runChecks,
Flapjack.Test.PanSemMemStore32AltParity.runChecks,
Flapjack.Test.PanSemCallErrorExactParity.runChecks,
Flapjack.Test.PanSemDecErrorExactParity.runChecks,
Flapjack.Test.PanSemPrimitiveErrorExactParity.runChecks,
Flapjack.Test.PanSemAssignErrorExactParity.runChecks,
Flapjack.Test.PanSemStoreErrorExactParity.runChecks,
Flapjack.Test.PanSemStore32ErrorExactParity.runChecks,
Flapjack.Test.PanSemIteErrorExactParity.runChecks,
Flapjack.Test.PanSemFuelDecompositionParity.runChecks,
    Flapjack.Test.CrepReplicateConstParity.runChecks,
    Flapjack.Test.WordConvsLabelsRelParity.runChecks,
    Flapjack.Test.WordLangExtractLabelsParity.runChecks,
    Flapjack.Test.WordLangInstPredsParity.runChecks,
    Flapjack.Test.WordLangFlatExpParity.runChecks,
    Flapjack.Test.WordLangInstOkLessParity.runChecks,
    Flapjack.Test.WordLangFullInstOkLessParity.runChecks,
    Flapjack.Test.WordLangCallArgParity.runChecks,
    Flapjack.Test.RegAllocVarParity.runChecks,
    Flapjack.Test.WordLangNotCreatedParity.runChecks,
    Flapjack.Test.WordLangEveryVarParity.runChecks,
    Flapjack.Test.WordLangGoodHandlersParity.runChecks,
    Flapjack.Test.NumSetAuditParity.runChecks,
    Flapjack.Test.WordLangEveryNameParity.runChecks,
    Flapjack.Test.WordLangAllocConventionsParity.runChecks,
    Flapjack.Test.LabPropsLineOkPreParity.runChecks,
    Flapjack.Test.LabPropsSecEndsLabelParity.runChecks,
    Flapjack.Test.CakeAllocatorBitsBridgeParity.runChecks,
    Flapjack.Test.StackNamesParity.runChecks,
    Flapjack.Test.StackRemoveInitParity.runChecks,
    Flapjack.Test.WordLocWParity.runChecks,
    Flapjack.Test.StackRemoveHelpersParity.runChecks,
    Flapjack.Test.LoopSemStateParity.runChecks,
    Flapjack.Test.LoopLangExpParity.runChecks,
    Flapjack.Test.LoopLangProgParity.runChecks,
    Flapjack.Test.SptreeParity.runChecks,
    Flapjack.Test.MlStringCodecParity.runChecks,
    Flapjack.Test.StackLangInstOverloadsParity.runChecks,
    Flapjack.Test.RiscvConfigParity.runChecks,
    Flapjack.Test.MiscAppListParity.runChecks,
    Flapjack.Test.StackToLabFlattenOpsParity.runChecks,
    Flapjack.Test.StackToLabFlattenBaseParity.runChecks,
    Flapjack.Test.StackToLabFlattenAppParity.runChecks,
    Flapjack.Test.AsmConfigChecksParity.runChecks,
    Flapjack.Test.PanSemDecCallErrorParity.runChecks,
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
    Flapjack.Test.CakeStackReseatParity.runChecks,
    Flapjack.Test.RiscVMemOpParity.runChecks,
    Flapjack.Test.RiscVArtifactParity.runChecks,
    Flapjack.Test.RiscVWordExtract6Parity.runChecks,
    Flapjack.Test.RiscVEncodeLengthParity.runChecks,
    Flapjack.Test.WordColourLivenessParity.runChecks,
    Flapjack.Test.RiscVRegisterMapParity.runChecks,
    Flapjack.Test.CakeAllocatorCore.runChecks,
    Flapjack.Test.CakeFramePolicy.runChecks,
    Flapjack.Test.CakeFrameContainment.runChecks,
    Flapjack.Test.WordStackCallParity.runChecks,
    Flapjack.Test.RiscVMemOpParity.runChecks,
    Flapjack.Test.WordInstNormalizeParity.runChecks,
    Flapjack.Test.CakeForcedParity.runChecks,
    Flapjack.Test.CakeMkBijParity.runChecks,
    Flapjack.Test.CakeSsaSetupParity.runChecks,
    Flapjack.Test.CakeSsaTempParity.runChecks,
    Flapjack.Test.CakeSsaBoundaryParity.runChecks,
    Flapjack.Test.CakeSsaControlParity.runChecks,
    Flapjack.Test.CakeSsaCallParity.runChecks,
    Flapjack.Test.CakeSsaInstParity.runChecks,
    Flapjack.Test.CakeSsaSharedParity.runChecks,
    Flapjack.Test.CakeSsaMemoryParity.runChecks,
    Flapjack.Test.CakeSsaLeafParity.runChecks,
    Flapjack.Test.CakeDeadCodeStateParity.runChecks,
    Flapjack.Test.CakeReturnSoundness.runChecks,
    Flapjack.Test.CakeApplyColourParity.runChecks,
    Flapjack.Test.CakeSpillCostParity.runChecks,
    Flapjack.Test.CakeFrameVectorParity.runChecks,
    Flapjack.Test.WordFuseConditions.runChecks,
    Flapjack.Test.RiscVAbiParity.runChecks,
    Flapjack.Test.RiscVAbiAdapterParity.runChecks,
    Flapjack.Test.LoopToWordBoundaryParity.runChecks,
    Flapjack.Test.SptreeOrderParity.runChecks,
    Flapjack.Test.CrepLocalsWordLabParity.runChecks,
    Flapjack.Test.CrepMemoryRelParity.runChecks,
    Flapjack.Test.CrepSemStateExactParity.runChecks,
    Flapjack.Test.CrepFuelCutoffParity.runChecks,
    Flapjack.Test.CrepSemTotalClockLeavesParity.runChecks,
    Flapjack.Test.CrepSemTotalCallParity.runChecks,
    Flapjack.Test.FfiHOLParity.runChecks,
    Flapjack.Test.CrepSemTotalAssignParity.runChecks,
    Flapjack.Test.FfiBridgeParity.runChecks,
    Flapjack.Test.CrepSemTotalStoreParity.runChecks,
    Flapjack.Test.CrepSemTotalShMemParity.runChecks,
    Flapjack.Test.PanLangShapeSizeWithContextParity.runChecks,
    Flapjack.Test.PanLangShapeSizeParity.runChecks,
    Flapjack.Test.PanLangIsWfShapeParity.runChecks,
    Flapjack.Test.PanSemIsValWordHOLParity.runChecks,
    Flapjack.Test.PanSemEmptyLocalsHOLParity.runChecks,
    Flapjack.Test.PanSemMemStore32HOLParity.runChecks,
    Flapjack.Test.PanSemMemStoreHOLParity.runChecks,
    Flapjack.Test.PanSemShMemHOLParity.runChecks,
    Flapjack.Test.PanSemDecsStcnamesHOLParity.runChecks,
    Flapjack.Test.PanSemMemLoadExactParity.runChecks,
    Flapjack.Test.CrepSemTotalExtCallParity.runChecks
    ].mapM id
  unless results.all id do
    IO.Process.exit 1

end Flapjack.Test.CompilerParity

def main : IO Unit := Flapjack.Test.CompilerParity.main
