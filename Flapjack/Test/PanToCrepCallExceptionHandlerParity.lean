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

/-! The original HOL oracle also covers a two-word exception payload via
`call_handles_struct_exception_7_8`; exercise the target `exp_hdl` bridge on
the corresponding two return-global cells and existing local slots. -/
private def pairHandlerVariables : FiniteMap String (Shape × List Nat) :=
  FUPDATE FEMPTY ("caught", (.comb [.one, .one], [1, 2]))

private def pairHandlerState : CrepRuntimeState Word64 Unit :=
  { handlerTargetState with
    locals := fun slot =>
      if slot == 1 then some (.word (BitVec.ofNat 64 0))
      else if slot == 2 then some (.word (BitVec.ofNat 64 0))
      else none
    globals := fun address =>
      if address == 0 then some (.word payload)
      else if address == 1 then some (.word (BitVec.ofNat 64 8))
      else none }

private def pairExpHdlResult :=
  evalCrepRuntimeProg handlerTargetFfi handlerTargetPrimitive 4 pairHandlerState
    (expHdlFiniteMap pairHandlerVariables "caught")

example : pairExpHdlResult = some (.normal,
    { pairHandlerState with locals :=
      (updateCrepRuntimeLocal
        (updateCrepRuntimeLocal pairHandlerState.locals 1 (.word payload))
        2 (.word (BitVec.ofNat 64 8))) }) := by
  have hvar : FLOOKUP pairHandlerVariables "caught" =
      some (.comb [.one, .one], [1, 2]) := by
    simp [pairHandlerVariables, FUPDATE, FLOOKUP]
  have hslot1 : ∃ old, pairHandlerState.locals 1 = some old :=
    ⟨.word (BitVec.ofNat 64 0), by simp [pairHandlerState]⟩
  have hslot2 : ∃ old, pairHandlerState.locals 2 = some old :=
    ⟨.word (BitVec.ofNat 64 0), by simp [pairHandlerState]⟩
  have hglobal0 : pairHandlerState.globals (0 : BitVec 5) = some (.word payload) := by
    simp [pairHandlerState, payload]
  have hglobal1 : pairHandlerState.globals (1 : BitVec 5) =
      some (.word (BitVec.ofNat 64 8)) := by
    simp [pairHandlerState, payload]
  simpa [pairExpHdlResult] using
    crepRuntimeExpHdlTwoWords handlerTargetFfi handlerTargetPrimitive
      pairHandlerState pairHandlerVariables "caught" 1 2 payload
      (BitVec.ofNat 64 8) hvar (by decide) hslot1 hslot2 hglobal0 hglobal1

def targetLoadsPairPayload : Bool :=
  match pairExpHdlResult with
  | some (.normal, post) =>
      post.locals 1 == some (.word payload) &&
      post.locals 2 == some (.word (BitVec.ofNat 64 8))
  | _ => false

#guard targetLoadsPairPayload

end Flapjack.Test.PanToCrepCallExceptionHandlerParity
