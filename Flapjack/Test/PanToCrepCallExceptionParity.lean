import Flapjack.Pancake.Proofs.PanToCrep.EvaluateCases
import Flapjack.Test.PanEvaluateParity

/-! A concrete, nonempty source/target code-map instance of the fixed-RV64
Call exception simulation case. The proof exercises the derived Crep callee
body and confirms the exception payload reaches `globals_lookup`. -/

namespace Flapjack.Test.PanToCrepCallExceptionParity

open Flapjack
open Flapjack.Test.PanEvaluateParity

private abbrev Word64 := RiscV.Word 64

def exceptionValue : Word64 := BitVec.ofNat 64 7
def exceptionCode : Word64 := BitVec.ofNat 64 3

def callExceptionContext : PanToCrepProofContext Word64 :=
  { vars := FEMPTY
    funcs := FUPDATE FEMPTY ("raiseE", ([], .one))
    eids := FUPDATE FEMPTY ("E", exceptionCode)
    vmax := 0 }

def callExceptionSourceState : PanSemState Word64 (FfiState Unit) :=
  { emptyPanSourceState 10
      [("raiseE", ([], .raise "E" (.const exceptionValue), .one))] with
    memory := fun _ => some (.word 0)
    exceptionShapes := FUPDATE FEMPTY ("E", .one) }

def callExceptionTargetCode : FunName →
    Option (List Nat × CrepProg Word64) :=
  fun function =>
    if function == "raiseE" then
      some ([], compileCodeRelProg
        (ctxtFc callExceptionContext.funcs callExceptionContext.eids [] [] [])
        (.raise "E" (.const exceptionValue)))
    else none

def callExceptionTargetState : CrepRuntimeState Word64 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := callExceptionTargetCode
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

private def targetHandler : CrepRuntimeFfiHandler Word64 Unit FfiFinalEvent :=
  fun _ ffi => CrepRuntimeFfiResponse.returned ffi []

private def targetPrimitive : CrepPrimitiveHandler Word64 := fun _ _ => none

private theorem stateFixture : stateRel callExceptionSourceState
    callExceptionTargetState := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext address
  simp [callExceptionSourceState, callExceptionTargetState,
    emptyPanSourceState, panTheWord]

private theorem exceptionFixture : excpRel callExceptionContext.eids
    callExceptionSourceState.exceptionShapes := by
  constructor
  · funext exception
    simp [FDOM, callExceptionContext, callExceptionSourceState,
      emptyPanSourceState, FUPDATE, FEMPTY]
  · intro exception exception' code code' hlookup hlookup' _heq
    simp [FLOOKUP, callExceptionContext, FUPDATE, FEMPTY] at hlookup hlookup'
    have hname : exception = "E" := hlookup.1.symm
    have hname' : exception' = "E" := hlookup'.1.symm
    exact hname.trans hname'.symm

private theorem localsFixture : localsRel callExceptionContext
    callExceptionSourceState.locals callExceptionTargetState.locals := by
  constructor
  · simp [noOverlap, callExceptionContext]
  · constructor
    · simp [ctxtMax, callExceptionContext]
    · intro name value hlookup
      simp [callExceptionSourceState, emptyPanSourceState, FLOOKUP] at hlookup

private theorem codeFixture : codeRel callExceptionContext
    (panSemCodeAsLookup callExceptionSourceState.code)
    callExceptionTargetState.code := by
  intro function variableShapes program returnShape hlookup
  change panSemCodeLookup callExceptionSourceState.code function = _ at hlookup
  by_cases hname : function = "raiseE"
  · subst function
    have htuple : ([], .raise "E" (.const exceptionValue), .one) =
        (variableShapes, program, returnShape) := by
      apply Option.some.inj
      simpa [callExceptionSourceState, emptyPanSourceState,
        panSemCodeLookup, lookupInfo] using hlookup
    rcases htuple with ⟨rfl, rfl, rfl⟩
    have hlocal : localisedProg
        (.raise "E" (.const exceptionValue) : Prog Word64) := by
      simp [localisedProg, localisedExp, expGlobalVars]
    have hsignature : FLOOKUP callExceptionContext.funcs "raiseE" =
        some ([], Shape.one) := by
      simp [callExceptionContext, FLOOKUP, FUPDATE]
    refine ⟨hlocal, hsignature, ?_⟩
    simp [callExceptionTargetState, callExceptionTargetCode, FLOOKUP,
      Shape.shapeSize, ctxtFc, maxList, FUPDATE_LIST,
      callExceptionContext, compileCodeRelProg]
  · simp [callExceptionSourceState, emptyPanSourceState, panSemCodeLookup,
      lookupInfo] at hlookup
    exact False.elim (hname hlookup.1.symm)

theorem callExceptionSimulationFixture :
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 8
        callExceptionTargetState
        (compileCodeRelProg callExceptionContext (.call none "raiseE" [])) =
          some (.raised exceptionCode, targetPost) ∧
      globalsLookup targetPost (.word exceptionValue) =
        some [.word exceptionValue] := by
  have hresult := panToCrepPcCompileCorrectCallRaiseOneWordExceptionCodeStateRiscV64
    callExceptionContext statefulTestContext statefulTestPrimitive
    statefulTestHandler targetHandler targetPrimitive
    callExceptionSourceState callExceptionTargetState "raiseE" "E"
    exceptionCode exceptionValue stateFixture codeFixture exceptionFixture
    localsFixture (by simp [callExceptionContext, exceptionCode, FLOOKUP, FUPDATE])
    (by simp [callExceptionSourceState, emptyPanSourceState,
      panSemCodeLookup, lookupInfo])
    (by simp [callExceptionSourceState, emptyPanSourceState,
      FUPDATE])
    (by decide)
  rcases hresult with ⟨_hsource, targetPost, hrun, _hstate, _hcode,
    _hexcp, hglobals, _hclock⟩
  exact ⟨targetPost, hrun, hglobals⟩

end Flapjack.Test.PanToCrepCallExceptionParity
