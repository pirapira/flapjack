import Flapjack.Pancake.Proofs.PanToCrep.EvaluateCases
import Flapjack.Test.PanEvaluateParity

/-! A direct fixed-RV64 runtime fixture for a state-owned Call that catches a
one-word exception and returns the handler local. The source-side HOL oracle is
`call_handles_exception_7` in `pan_sem_e2e_probe.out`. -/

namespace Flapjack.Test.PanToCrepCallExceptionHandlerParity

open Flapjack
open Flapjack.Test.PanEvaluateParity

private abbrev Word64 := RiscV.Word 64

/-! These kernel tests feed a Local-derived, nonconstant address IH into the
flat-load Call-argument proofs. The generic assumptions let the fixture cover
both source `PanSemState` and production target `CrepRuntimeState` boundaries. -/
example (context : PanToCrepProofContext Word64)
    (source : PanSemState Word64 (FfiState σ))
    (target : CrepRuntimeState Word64 σ) (name : String)
    (addressWord loaded : Word64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceLocal : source.locals name = some (.word addressWord))
    (hsourceLoad : evalPanSemStateExp source
      (.load .one (.var .local name)) = some (.word loaded)) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one (.var .local name))).1 = some [loaded] := by
  exact (compileExpHOL_loadOne_localAddress_ofHOLIH context source target name
    addressWord loaded hstate hcode hlocals hsourceLocal hsourceLoad).1

example (context : PanToCrepProofContext Word64)
    (source : PanSemState Word64 (FfiState σ))
    (target : CrepRuntimeState Word64 σ) (name : String)
    (addressWord loaded0 loaded1 : Word64)
    (hstate : stateRel source target)
    (hcanonical : target = riscvCrepWordTarget target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceLocal : source.locals name = some (.word addressWord))
    (hsourceLoad : evalPanSemStateExp source
      (.load (.comb [.one, .one]) (.var .local name)) =
        some (.rStruct [.word loaded0, .word loaded1])) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load (.comb [.one, .one]) (.var .local name))).1 =
      some [loaded0, loaded1] := by
  exact (compileExpHOL_loadTwo_localAddress_ofHOLIH context source target name
    addressWord loaded0 loaded1 hstate hcanonical hcode hlocals hsourceLocal
    hsourceLoad).1

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

private def raisedSourceResult : PanValueFfiClockResult Word64 Unit :=
  (.control (.raised (fun _ => none) (fun _ => none)
      (fun _ => some (.word (BitVec.ofNat 64 0))) statefulTestFfiState
      "E" (.word payload)), 4)

example : panToCrepClockResultRel handlerContext raisedSourceResult
    (.raised exceptionCode, pairHandlerState) := by
  simp [panToCrepClockResultRel, raisedSourceResult, handlerContext,
    exceptionCode, pairHandlerState, payload, globalsLookup, panSemShapeOf,
    panValueFlatten, FUPDATE, FLOOKUP]

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

/-! Exercise the full state-owned target Call dispatcher with the two-word
payload from HOL `call_handles_struct_exception_7_8`, rather than testing
`exp_hdl` alone. The handler loads both return-global cells into its existing
local slots and returns the pair. -/
private def pairCallContext : PanToCrepProofContext Word64 :=
  { vars := pairHandlerVariables
    funcs := FUPDATE FEMPTY ("raisePair", ([], .comb [.one, .one]))
    eids := FUPDATE FEMPTY ("E", exceptionCode)
    vmax := 2 }

private def pairCallProgram : Prog Word64 :=
  .call (some (none, some ("E", "caught",
    .return (.var .local "caught")))) "raisePair" []

private def pairCallBody : Prog Word64 :=
  .raise "E" (.rStruct [.const payload, .const (BitVec.ofNat 64 8)])

private def pairCallCode : FunName → Option (List Nat × CrepProg Word64) :=
  fun function =>
    if function == "raisePair" then
      some ([], compileCodeRelProg
        (ctxtFc pairCallContext.funcs pairCallContext.eids [] [] [])
        pairCallBody)
    else none

private def pairCallTargetState : CrepRuntimeState Word64 Unit :=
  { pairHandlerState with code := pairCallCode }

private def pairCallTargetResult :=
  evalCrepRuntimeResult handlerTargetFfi handlerTargetPrimitive 12
    pairCallTargetState (compileCodeRelProg pairCallContext pairCallProgram)

def targetCallCatchesAndReturnsPair : Bool :=
  match pairCallTargetResult with
  | some (.returned [first, second], post) =>
      first == payload && second == BitVec.ofNat 64 8 &&
      globalsLookup post (.rStruct [.word payload, .word (BitVec.ofNat 64 8)]) =
        some [.word payload, .word (BitVec.ofNat 64 8)]
  | _ => false

#guard targetCallCatchesAndReturnsPair

/-! Arbitrary-list target `exp_hdl` support, exercised on a three-word payload.
The proof uses state-owned return-global cells and writes into preexisting
handler locals in order. The source HOL `exp_hdl` oracle pins the generated
load/store sequence; this fixture validates the generalized runtime theorem. -/
private def tripleHandlerVariables : FiniteMap String (Shape × List Nat) :=
  FUPDATE FEMPTY ("caught", (.comb [.one, .one, .one], [1, 2, 3]))

private def tripleHandlerState : CrepRuntimeState Word64 Unit :=
  { handlerTargetState with
    locals := fun slot =>
      if slot == 1 || slot == 2 || slot == 3 then some (.word 0) else none
    globals := fun address =>
      if address == 0 then some (.word payload)
      else if address == 1 then some (.word (BitVec.ofNat 64 8))
      else if address == 2 then some (.word (BitVec.ofNat 64 9))
      else none }

private def tripleValues : List Word64 := [payload, BitVec.ofNat 64 8, BitVec.ofNat 64 9]

private def tripleExpHdlResult :=
  evalCrepRuntimeProg handlerTargetFfi handlerTargetPrimitive 5 tripleHandlerState
    (expHdlFiniteMap tripleHandlerVariables "caught")

example : tripleExpHdlResult = some (.normal,
    { tripleHandlerState with locals :=
      (updateCrepRuntimeLocal
        (updateCrepRuntimeLocal
          (updateCrepRuntimeLocal tripleHandlerState.locals 1 (.word payload))
          2 (.word (BitVec.ofNat 64 8)))
        3 (.word (BitVec.ofNat 64 9))) }) := by
  have hvar : FLOOKUP tripleHandlerVariables "caught" =
      some (.comb [.one, .one, .one], [1, 2, 3]) := by
    simp [tripleHandlerVariables, FUPDATE, FLOOKUP]
  have hslots : ∀ slot, slot ∈ [1, 2, 3] →
      ∃ old, tripleHandlerState.locals slot = some old := by
    intro slot hslot
    have hslot' : slot = 1 ∨ slot = 2 ∨ slot = 3 := by simpa using hslot
    rcases hslot' with hslot | hslot | hslot <;> subst slot <;>
      exact ⟨.word 0, by simp [tripleHandlerState]⟩
  have hglobals : crepRuntimeGlobalWordsRel tripleHandlerState 0
      [1, 2, 3] tripleValues := by
    change evalCrepRuntimeExp tripleHandlerState (.loadGlob 0) = some payload ∧
      (evalCrepRuntimeExp tripleHandlerState (.loadGlob 1) = some (BitVec.ofNat 64 8) ∧
        (evalCrepRuntimeExp tripleHandlerState (.loadGlob 2) = some (BitVec.ofNat 64 9) ∧ True))
    simp [evalCrepRuntimeExp, panTheWord, tripleHandlerState, payload]
  simpa [tripleExpHdlResult, tripleValues, List.zip_cons_cons,
    List.foldl_cons] using
    crepRuntimeExpHdlFiniteMapWords handlerTargetFfi handlerTargetPrimitive
      tripleHandlerState tripleHandlerVariables "caught"
      (.comb [.one, .one, .one]) [1, 2, 3] tripleValues hvar hslots hglobals

def targetLoadsTriplePayload : Bool :=
  match tripleExpHdlResult with
  | some (.normal, post) =>
      post.locals 1 == some (.word payload) &&
      post.locals 2 == some (.word (BitVec.ofNat 64 8)) &&
      post.locals 3 == some (.word (BitVec.ofNat 64 9))
  | _ => false

#guard targetLoadsTriplePayload

end Flapjack.Test.PanToCrepCallExceptionHandlerParity
