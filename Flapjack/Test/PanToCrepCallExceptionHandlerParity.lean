import Flapjack.Pancake.Proofs.PanToCrep.EvaluateCases
import Flapjack.Test.PanEvaluateParity

/-! A direct fixed-RV64 runtime fixture for a state-owned Call that catches a
one-word exception and returns the handler local. The source-side HOL oracle is
`call_handles_exception_7` in `pan_sem_e2e_probe.out`. -/

namespace Flapjack.Test.PanToCrepCallExceptionHandlerParity

open Flapjack
open Flapjack.Test.PanEvaluateParity

private abbrev Word64 := RiscV.Word 64

private def payload : Word64 := BitVec.ofNat 64 7
private def exceptionCode : Word64 := BitVec.ofNat 64 3

private def handlerContext : PanToCrepProofContext Word64 :=
  { vars := FUPDATE FEMPTY ("caught", (Shape.one, [1]))
    funcs := FUPDATE FEMPTY ("raiseE", ([], Shape.one))
    eids := FUPDATE FEMPTY ("E", exceptionCode)
    vmax := 1 }

private def handlerProgram : Prog Word64 :=
  .call (some (none, some ("E", "caught",
    .return (.var .local "caught")))) "raiseE" []

private def handlerTargetCode : FunName → Option (List Nat × CrepProg Word64) :=
  fun function =>
    if function == "raiseE" then
      some ([], compileCodeRelProg
        (ctxtFc handlerContext.funcs handlerContext.eids [] [] [])
        (.raise "E" (.const payload)))
    else none

private def handlerTargetState : CrepRuntimeState Word64 Unit :=
  { locals := fun slot =>
      if slot == 1 then some (.word (BitVec.ofNat 64 0)) else none
    globals := fun _ => none
    code := handlerTargetCode
    memory := fun _ => .word 0
    memaddrs := fun _ => false
    shMemaddrs := fun _ => false
    memoryModel := panSemBitVec64WordModel
    bytesInWord := panSemBitVec64BytesInWord
    ffiContext := statefulTestContext
    clock := 10
    bigEndian := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

private def handlerTargetFfi : CrepRuntimeFfiHandler Word64 Unit FfiFinalEvent :=
  fun _ ffi => CrepRuntimeFfiResponse.returned ffi []

private def handlerTargetPrimitive : CrepPrimitiveHandler Word64 := fun _ _ => none

private def handlerTargetResult :=
  evalCrepRuntimeResult handlerTargetFfi handlerTargetPrimitive 12
    handlerTargetState (compileCodeRelProg handlerContext handlerProgram)

private def compiledHandlerContinuation : CrepProg Word64 :=
  .seq (.seq (.assign 1 (.loadGlob (0 : BitVec 5))) .skip)
    (.return [.var 1])

private def compiledHandlerCall : CrepProg Word64 :=
  .dec 2 (.const (BitVec.ofNat 64 0))
    (.call (some ([2], some (exceptionCode, compiledHandlerContinuation)))
      "raiseE" [])

theorem compileHandlerCallFixture :
    compileCodeRelProg handlerContext handlerProgram = compiledHandlerCall := by
  simp [compileCodeRelProg, handlerContext,
    handlerProgram, compiledHandlerCall, compiledHandlerContinuation,
    compileProgHOL, compileExpHOL, compileArgsHOL, functionReturnNamesHOL,
    allocatedNamesHOL, expHdlFiniteMap, loadGlobals,
    nestedDecs, panMap2, crepNestedSeq, FUPDATE, FLOOKUP]

def targetCatchesAndReturnsPayload : Bool :=
  match handlerTargetResult with
  | some (.returned [value], post) =>
      value == payload &&
      globalsLookup post (.word payload) == some [.word payload]
  | _ => false

#guard targetCatchesAndReturnsPayload

end Flapjack.Test.PanToCrepCallExceptionHandlerParity
