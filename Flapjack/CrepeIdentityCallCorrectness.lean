import Flapjack.CrepeDecCallRelation
import Flapjack.CrepeExpCorrectness

/-!
An executable source-to-Crep correctness witness for a declaration call.

The generic call rules deliberately leave the callee and continuation
simulations as hypotheses.  This small closed identity program supplies both
witnesses through the actual Pancake and Crep evaluators, and therefore keeps
the source/target control relation connected to the compiled declaration
environment.
-/

namespace Flapjack

def correctnessIdentitySourceFunctions :
    List (FunName × List VarName × Prog α) :=
  [("id", ["x"], .return (.var .local "x"))]

def correctnessIdentitySourceMain (value : α) : Prog α :=
  .decCall "result" .one "id" [.const value]
    (.return (.var .local "result"))

def correctnessIdentitySourceLocals : VarName → Option (PanValue α) :=
  fun _ => none

def correctnessIdentitySourceGlobals : VarName → Option (PanValue α) :=
  fun _ => none

def correctnessIdentitySourceMemory : α → Option (PanValue α) :=
  fun _ => none

def correctnessIdentityCrepState : CrepState α :=
  { locals := fun _ => none, memory := fun _ => none }

def correctnessIdentityCallState (value : α) : CrepState α :=
  { locals := updateCrepLocal (fun _ => none) 1 value
    memory := fun _ => none }

theorem compile_full_pan_value_identity_declaration_call_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (value : α) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
      (correctnessIdentitySourceFunctions (α := α))
      0 0 1 20
      correctnessIdentitySourceLocals correctnessIdentitySourceGlobals
      correctnessIdentitySourceMemory
      (correctnessIdentitySourceMain value) =
      some (restorePanValueControlLocal "result"
        (correctnessIdentitySourceLocals "result")
        (.returned (fun _ => none) correctnessIdentitySourceGlobals
          correctnessIdentitySourceMemory [.word value])) ∧
    evalCrepFullProg
      (compileToCrepe (correctnessIdentityContext (α := α))
        (correctnessIdentityDeclarations value))
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
      0 0 22 correctnessIdentityCrepState
      (compileProg (correctnessIdentityContext (α := α))
        (correctnessIdentitySourceMain value)) =
      some (restoreCrepResultList correctnessIdentityCrepState.locals
        (allocatedNames (correctnessIdentityContext (α := α)) .one)
        (.returned (correctnessIdentityCallState value) [value])) ∧
    panValueCrepControlRel [] (correctnessIdentityContext (α := α))
      (fun _ _ _ => True)
      (restorePanValueControlLocal "result"
        (correctnessIdentitySourceLocals "result")
        (.returned (fun _ => none) correctnessIdentitySourceGlobals
          correctnessIdentitySourceMemory [.word value]))
      (restoreCrepResultList correctnessIdentityCrepState.locals
        (allocatedNames (correctnessIdentityContext (α := α)) .one)
        (.returned (correctnessIdentityCallState value) [value])) := by
  have hsourceCall :
      evalPanValueCallWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
        (correctnessIdentitySourceFunctions (α := α))
        0 0 1 19 correctnessIdentitySourceLocals
        correctnessIdentitySourceGlobals correctnessIdentitySourceMemory
        none "id" [.const value] =
        some (.returned (fun _ => none) correctnessIdentitySourceGlobals
          correctnessIdentitySourceMemory [.word value]) := by
    have hvalues :
      evalPanValueExps [] correctnessIdentitySourceLocals
          correctnessIdentitySourceGlobals correctnessIdentitySourceMemory
          0 0 1 [.const value] = some [.word value] := by
      simpa [evalPanValueExps] using
        (evalPanValueExp_const_words_list [] correctnessIdentitySourceLocals
          correctnessIdentitySourceGlobals correctnessIdentitySourceMemory
          0 0 1 [value])
    have hlookup :
        lookupPanFunction "id"
          (correctnessIdentitySourceFunctions (α := α)) =
          some (["x"], .return (.var .local "x")) := by
      simp [correctnessIdentitySourceFunctions, lookupPanFunction]
    let calleeLocals : VarName → Option (PanValue α) :=
      updatePanValueMap (fun _ => none) "x" (.word value)
    have hbind :
        bindPanValueParameters ["x"] [.word value] = some calleeLocals := by
      simp [calleeLocals, bindPanValueParameters]
    have hcallee :
        evalPanValueProgWithPrimitiveCallsAndFfi
          (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
          (correctnessIdentitySourceFunctions (α := α))
          0 0 1 18 calleeLocals correctnessIdentitySourceGlobals
          correctnessIdentitySourceMemory
          (.return (.var .local "x")) =
          some (.returned (fun _ => none) correctnessIdentitySourceGlobals
            correctnessIdentitySourceMemory [.word value]) := by
      simp [calleeLocals, evalPanValueProgWithPrimitiveCallsAndFfi,
        evalPanValueExp, updatePanValueMap]
    have hcall := evalPanValueCall_returned_no_destination
      (primitive := (fun _ _ => none))
      (handler := (fun _ _ _ _ _ _ => none))
      (structs := [])
      (functions := correctnessIdentitySourceFunctions (α := α))
      (sourceLocals := correctnessIdentitySourceLocals)
      (sourceGlobals := correctnessIdentitySourceGlobals)
      (sourceMemory := correctnessIdentitySourceMemory)
      (baseAddress := 0) (topAddress := 0) (bytesInWord := 1)
      (fuel := 18) (contracts := none) (memoryAccess := none)
      (memoryHandler := none) (function := "id")
      (arguments := [.const value]) (values := [.word value])
      (parameters := ["x"]) (body := .return (.var .local "x"))
      (calleeLocals := calleeLocals)
      (calleeGlobals := correctnessIdentitySourceGlobals)
      (calleeMemory := correctnessIdentitySourceMemory)
      (calleeBodyLocals := fun _ => none)
      (calleeValues := [.word value])
      (hvalues := hvalues) (hlookup := hlookup)
      (hparameters := by simp [panValueParametersValid])
      (hbind := hbind) (hcallee := hcallee)
      (hreturn := by simp [panValueReturnValid])
      (hlimit := by simp [panValueValuesWithinLimit])
    simpa using hcall
  have hsourceBody :
      evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
        (correctnessIdentitySourceFunctions (α := α))
        0 0 1 19 (updatePanValueMap correctnessIdentitySourceLocals
          "result" (.word value)) correctnessIdentitySourceGlobals
        correctnessIdentitySourceMemory
        (.return (.var .local "result")) =
        some (.returned (fun _ => none) correctnessIdentitySourceGlobals
          correctnessIdentitySourceMemory [.word value]) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
      updatePanValueMap]
  have hsource :
      evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
        (correctnessIdentitySourceFunctions (α := α))
        0 0 1 20 correctnessIdentitySourceLocals
        correctnessIdentitySourceGlobals correctnessIdentitySourceMemory
      (correctnessIdentitySourceMain value) =
        some (restorePanValueControlLocal "result"
          (correctnessIdentitySourceLocals "result")
          (.returned (fun _ => none) correctnessIdentitySourceGlobals
            correctnessIdentitySourceMemory [.word value])) := by
    simpa [correctnessIdentitySourceMain] using
      (evalPanValueProg_decCall_compose
      (fun _ _ => none) (fun _ _ _ _ _ _ => none) []
      (correctnessIdentitySourceFunctions (α := α))
      correctnessIdentitySourceLocals correctnessIdentitySourceGlobals
      correctnessIdentitySourceMemory 0 0 1 19 none none none
      "result" .one "id" [.const value]
      (.return (.var .local "result"))
      correctnessIdentitySourceGlobals correctnessIdentitySourceMemory
      (.word value)
      (.returned (fun _ => none) correctnessIdentitySourceGlobals
        correctnessIdentitySourceMemory [.word value])
      hsourceCall (by simp [panValueShape, panShapeMatches])
      hsourceBody)
  let callState : CrepState α :=
    { locals := updateCrepLocal (fun _ => none) 1 value
      memory := fun _ => none }
  have hcrepCall :
      evalCrepFullCall
      (compileToCrepe (correctnessIdentityContext (α := α))
          (correctnessIdentityDeclarations value))
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
      0 0 19
        { locals := initializeCrepLocals correctnessIdentityCrepState.locals
            (allocatedNames (correctnessIdentityContext (α := α)) .one)
          , memory := correctnessIdentityCrepState.memory }
        (some (allocatedNames (correctnessIdentityContext (α := α)) .one, none))
          "id" [.const value] =
        some (.normal callState) := by
    simp [callState, correctnessIdentityCrepState,
      correctnessIdentityContext, correctnessIdentityDeclarations,
      compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
      functionInfos, compileProg, compileExp, compileArgs, allocatedNames,
      evalCrepFullCall, evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
      updateCrepLocal, lookupCompiledFunction, assignCrepValues,
      lookupInfo, List.map, List.zip, List.foldl]
    funext current
    by_cases h : current = 1
    · simp [h, updateCrepLocal]
    · simp [h, initializeCrepLocals, updateCrepLocal]
  have hcrepBody :
      evalCrepFullProg
      (compileToCrepe (correctnessIdentityContext (α := α))
          (correctnessIdentityDeclarations value))
        (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
        0 0 20 callState
        (compileProg
          { vars := ("result", (.one, allocatedNames
              (correctnessIdentityContext (α := α)) .one)) ::
              (correctnessIdentityContext (α := α)).vars
            functions := (correctnessIdentityContext (α := α)).functions
            exceptions := (correctnessIdentityContext (α := α)).exceptions
            maxVar := (correctnessIdentityContext (α := α)).maxVar +
              Shape.shapeSize .one
            bytesInWord := (correctnessIdentityContext (α := α)).bytesInWord }
          (.return (.var .local "result"))) =
        some (.returned callState [value]) := by
    simp [callState, correctnessIdentityContext,
      correctnessIdentityDeclarations, compileToCrepe, compileFunctions,
      compileFunDecl, compileParamVars, functionInfos, compileProg,
      compileExp, compileArgs, allocatedNames, evalCrepFullProg,
      evalCrepFullExps, evalCrepFullExp, updateCrepLocal,
      lookupInfo, List.map]
  have hrel :
      panValueCrepControlRel [] (correctnessIdentityContext (α := α))
        (fun _ _ _ => True)
        (.returned correctnessIdentitySourceLocals
          correctnessIdentitySourceGlobals correctnessIdentitySourceMemory
          [.word value])
        (.returned correctnessIdentityCrepState [value]) := by
    refine ⟨?_, panValueCrepValuesRel_singleton (.word value)⟩
    refine ⟨rfl, ?_, ?_⟩
    · change panValueCrepLocalsRel []
        (correctnessIdentityContext (α := α)) (fun _ => none)
        correctnessIdentityCrepState.locals
      exact
        (panValueCrepLocalsRel_empty []
          (correctnessIdentityContext (α := α))
          correctnessIdentityCrepState.locals)
    · funext address
      simp [correctnessIdentitySourceMemory, correctnessIdentityCrepState,
        panValueWordMemory]
  have hrel' :
      panValueCrepControlRel [] (correctnessIdentityContext (α := α))
        (fun _ _ _ => True)
        (restorePanValueControlLocal "result"
          (correctnessIdentitySourceLocals "result")
          (.returned (fun _ => none) correctnessIdentitySourceGlobals
            correctnessIdentitySourceMemory [.word value]))
        (restoreCrepResultList correctnessIdentityCrepState.locals
          (allocatedNames (correctnessIdentityContext (α := α)) .one)
          (.returned callState [value])) := by
    have hsourceRestored :
        restorePanValueLocal (α := α) (fun _ : VarName => none)
            "result" (none : Option (PanValue α)) =
          (fun _ : VarName => none) := by
      funext name
      simp [restorePanValueLocal]
    have hpostState :
        panValueCrepStateRel [] (correctnessIdentityContext (α := α))
          (fun _ => none) correctnessIdentitySourceGlobals
          correctnessIdentitySourceMemory
          { locals := restoreCrepLocal callState.locals
              ((correctnessIdentityContext (α := α)).maxVar + 1)
              (correctnessIdentityCrepState.locals
                ((correctnessIdentityContext (α := α)).maxVar + 1))
            memory := callState.memory } := by
      refine ⟨rfl, ?_, ?_⟩
      · change panValueCrepLocalsRel []
          (correctnessIdentityContext (α := α)) (fun _ => none)
          _
        exact panValueCrepLocalsRel_empty []
          (correctnessIdentityContext (α := α)) _
      · funext address
        simp [callState, correctnessIdentitySourceMemory, panValueWordMemory]
    simp [restorePanValueControlLocal, restoreCrepResultList,
      restoreCrepResult, allocatedNames, correctnessIdentitySourceLocals,
      hsourceRestored]
    simp only [panValueCrepControlRel]
    change panValueCrepStateRel [] (correctnessIdentityContext (α := α))
        (fun _ => none) correctnessIdentitySourceGlobals
        correctnessIdentitySourceMemory
        { locals := restoreCrepLocal callState.locals
            ((correctnessIdentityContext (α := α)).maxVar + 1)
            (correctnessIdentityCrepState.locals
              ((correctnessIdentityContext (α := α)).maxVar + 1))
          memory := callState.memory } ∧
      panValueCrepValuesRel [.word value] [value]
    constructor
    · simpa [correctnessIdentitySourceLocals, restorePanValueLocal] using hpostState
    · exact panValueCrepValuesRel_singleton (.word value)
  have hresult := compile_full_pan_value_decCall_relation
    (correctnessIdentityContext (α := α)) [] 
    (correctnessIdentitySourceFunctions (α := α))
    (compileToCrepe (correctnessIdentityContext (α := α))
      (correctnessIdentityDeclarations value))
    correctnessIdentitySourceLocals correctnessIdentitySourceGlobals
    correctnessIdentitySourceMemory correctnessIdentityCrepState callState
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ => none)
      (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 0 1 19 none none none
    "result" .one "id" [.const value] (.return (.var .local "result"))
    [.const value]
    correctnessIdentitySourceGlobals correctnessIdentitySourceMemory (.word value)
    (.returned (fun _ => none) correctnessIdentitySourceGlobals
      correctnessIdentitySourceMemory [.word value])
    (.returned callState [value]) (fun _ _ _ => True)
    (by simp [compileArgs, compileExp]) hsourceCall
    (by simp [panValueShape, panShapeMatches]) hsourceBody
    hcrepCall hcrepBody hrel'
  simpa [callState, correctnessIdentityCallState, correctnessIdentitySourceMain,
    correctnessIdentityContext,
    correctnessIdentitySourceLocals, correctnessIdentitySourceGlobals,
    correctnessIdentitySourceMemory, correctnessIdentityCrepState,
    allocatedNames, Shape.shapeSize, restoreCrepResultList, restoreCrepResult,
    restorePanValueControlLocal, restorePanValueLocal, updateCrepLocal]
    using hresult

end Flapjack
