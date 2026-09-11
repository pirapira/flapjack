import Flapjack.CrepeDecCallRelation
import Flapjack.CrepeExpCorrectness
import Flapjack.CrepeFfiCorrectness
import Flapjack.RiscV.Model

/-!
End-to-end structured source-to-Crep correctness for a declaration whose
callee performs an FFI call before returning.  The compiled declaration table
is produced by the real Pancake-to-Crep compiler; the theorem is not a
hand-written Crep approximation.
-/

namespace Flapjack

open RiscV

def declarationFfiContext : CompileContext (Word 64) :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := BitVec.ofNat 64 8 }

def declarationFfiCalleeBody : Prog (Word 64) :=
  .seq
    (.extCall "inc" (.const (BitVec.ofNat 64 41)) (.const 0)
      (.const 0) (.const 0))
    (.return (.var .local "x"))

def declarationFfiCompiledCalleeBody : CrepProg (Word 64) :=
  (.seq
    (nestedDecs [2, 3, 4, 5]
      [.const (BitVec.ofNat 64 41), .const 0, .const 0, .const 0]
      (.extCall "inc" 2 3 4 5))
    (.return [.var 0]))

def declarationFfiSourceFunctions :
    List (FunName × List VarName × Prog (Word 64)) :=
  [("ffiId", ["x"], declarationFfiCalleeBody)]

def declarationFfiDeclarations : List (Decl (Word 64)) :=
  [.function
    { name := "ffiId", inline := false, exported := false,
      params := [("x", .one)], body := declarationFfiCalleeBody,
      returnShape := .one },
   .function
    { name := "main", inline := false, exported := true, params := [],
      body := .decCall "result" .one "ffiId"
        [.const (BitVec.ofNat 64 41)]
        (.return (.var .local "result")),
      returnShape := .one }]

def declarationFfiMain : Prog (Word 64) :=
  .decCall "result" .one "ffiId"
    [.const (BitVec.ofNat 64 41)]
    (.return (.var .local "result"))

def declarationFfiSourceHandler : PanValueFfiHandler (Word 64) :=
  fun function configuration _ _ _ locals =>
    if function == "inc" then
      some (updatePanValueMap locals "x" (.word (configuration + 1)))
    else none

def declarationFfiCrepHandler : CrepFfiHandler (Word 64) :=
  fun function configuration _ _ _ state =>
    if function == "inc" then
      some (.returned
        { state with
          locals := updateCrepLocal state.locals 0 (configuration + 1) })
    else none

def declarationFfiInitialState : CrepState (Word 64) :=
  { locals := fun _ => none, memory := fun _ => none }

def declarationFfiCallState : CrepState (Word 64) :=
  { locals := updateCrepLocal (fun _ => none) 1
      (BitVec.ofNat 64 42),
    memory := fun _ => none }

theorem crepState_eq {α : Type} (left right : CrepState α)
    (hlocals : left.locals = right.locals)
    (hmemory : left.memory = right.memory) : left = right := by
  cases left
  cases right
  simp_all

theorem declaration_ffi_source_to_crep_relation :
    evalPanValueProgWithPrimitiveCallsAndFfi
      (fun _ _ => none) declarationFfiSourceHandler []
      declarationFfiSourceFunctions
      0 100 8 21
      (fun _ => none) (fun _ => none) (fun _ => none)
      declarationFfiMain =
      some (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        [.word (BitVec.ofNat 64 42)]) ∧
    evalCrepFullProg
      (compileToCrepe declarationFfiContext declarationFfiDeclarations)
      (fun _ _ => none) declarationFfiCrepHandler
      defaultCrepSharedMem 0 100 23 declarationFfiInitialState
      (compileProg declarationFfiContext declarationFfiMain) =
      some (.returned declarationFfiInitialState
        [BitVec.ofNat 64 42]) ∧
    panValueCrepControlRel [] declarationFfiContext
      (fun _ _ _ => False)
      (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        [.word (BitVec.ofNat 64 42)])
      (.returned declarationFfiInitialState
        [BitVec.ofNat 64 42]) := by
  have hsourceCall :
      evalPanValueCallWithPrimitiveCallsAndFfi
        (fun _ _ => none) declarationFfiSourceHandler []
        declarationFfiSourceFunctions
        0 100 8 20
        (fun _ => none) (fun _ => none) (fun _ => none)
        none "ffiId" [.const (BitVec.ofNat 64 41)] =
      some (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        [.word (BitVec.ofNat 64 42)]) := by
    let calleeLocals : VarName → Option (PanValue (Word 64)) :=
      updatePanValueMap (fun _ => none) "x" (.word (BitVec.ofNat 64 41))
    have hcallee :
        evalPanValueProgWithPrimitiveCallsAndFfi
          (fun _ _ => none) declarationFfiSourceHandler []
          declarationFfiSourceFunctions
          0 100 8 19 calleeLocals
          (fun _ => none) (fun _ => none) declarationFfiCalleeBody =
        some (.returned (fun _ => none) (fun _ => none) (fun _ => none)
          [.word (BitVec.ofNat 64 42)]) := by
      have hlimit :
          panValuePayloadWithinLimit []
              (.word (BitVec.ofNat 64 42)) = true :=
        panValuePayloadWithinLimit_word [] (BitVec.ofNat 64 42)
      simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
        declarationFfiCalleeBody, calleeLocals,
        declarationFfiSourceHandler]
      unfold evalPanValueExps
      simp [evalPanValueExp.evalPanValueExps, evalPanValueExp]
      have hx :
          updatePanValueMap
              (updatePanValueMap (fun _ => none) "x"
                (PanValue.word (BitVec.ofNat 64 41))) "x"
              (PanValue.word (BitVec.ofNat 64 42)) "x" =
            some (PanValue.word (BitVec.ofNat 64 42)) := by
        simp [updatePanValueMap]
      rw [hx]
      simp [hlimit]
    apply evalPanValueCall_returned_no_destination
      (primitive := fun _ _ => none)
      (handler := declarationFfiSourceHandler)
      (structs := []) (functions := declarationFfiSourceFunctions)
      (sourceLocals := fun _ => none)
      (sourceGlobals := fun _ => none) (sourceMemory := fun _ => none)
      (baseAddress := 0) (topAddress := 100) (bytesInWord := 8)
      (fuel := 19) (contracts := none) (memoryAccess := none)
      (memoryHandler := none) (function := "ffiId")
      (arguments := [.const (BitVec.ofNat 64 41)])
      (values := [.word (BitVec.ofNat 64 41)])
      (parameters := ["x"]) (body := declarationFfiCalleeBody)
      (calleeLocals := calleeLocals)
      (calleeGlobals := fun _ => none) (calleeMemory := fun _ => none)
      (calleeBodyLocals := fun _ => none)
      (calleeValues := [.word (BitVec.ofNat 64 42)])
      (hvalues := by
        simpa [evalPanValueExps] using
          (evalPanValueExp_const_words_list []
            (fun _ => none) (fun _ => none) (fun _ => none)
            0 100 8 [BitVec.ofNat 64 41]))
      (hlookup := by
        simp [declarationFfiSourceFunctions, lookupPanFunction])
      (hparameters := by simp [panValueParametersValid])
      (hbind := by simp [calleeLocals, bindPanValueParameters])
      (hcallee := hcallee)
      (hreturn := by simp [panValueReturnValid])
      (hlimit := by simp [panValueValuesWithinLimit])
  have hsourceBody :
      evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) declarationFfiSourceHandler []
        declarationFfiSourceFunctions
        0 100 8 20
        (updatePanValueMap (fun _ => none) "result"
          (.word (BitVec.ofNat 64 42)))
        (fun _ => none) (fun _ => none)
        (.return (.var .local "result")) =
      some (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        [.word (BitVec.ofNat 64 42)]) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
      updatePanValueMap]
  have hcrepCall :
      evalCrepFullCall
        (compileToCrepe declarationFfiContext declarationFfiDeclarations)
        (fun _ _ => none) declarationFfiCrepHandler
        defaultCrepSharedMem 0 100 20
        { declarationFfiInitialState with
          locals := initializeCrepLocals declarationFfiInitialState.locals
            (allocatedNames declarationFfiContext .one) }
        (some (allocatedNames declarationFfiContext .one, none))
        "ffiId" [.const (BitVec.ofNat 64 41)] =
      some (.normal declarationFfiCallState) := by
    apply evalCrepFullCall_returned_with_destinations
      (caller :=
        { declarationFfiInitialState with
          locals := initializeCrepLocals declarationFfiInitialState.locals
            (allocatedNames declarationFfiContext .one) })
      (destinations := allocatedNames declarationFfiContext .one)
      (function := "ffiId")
      (arguments := [.const (BitVec.ofNat 64 41)])
      (body := declarationFfiCompiledCalleeBody)
      (callee :=
        { locals := updateCrepLocal (fun _ => none) 0
            (BitVec.ofNat 64 42)
          memory := fun _ => none })
      (values := [BitVec.ofNat 64 41])
      (parameters := [0])
      (calleeLocals := updateCrepLocal (fun _ => none) 0
        (BitVec.ofNat 64 41))
      (calleeValues := [BitVec.ofNat 64 42])
      (callerLocals := declarationFfiCallState.locals)
    · simp [declarationFfiContext, evalCrepFullExps, evalCrepFullExp]
    · simp [declarationFfiContext, declarationFfiDeclarations,
        compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
        functionInfos, compileProg, compileExp, compileArgs, allocatedNames,
        declarationFfiCalleeBody, declarationFfiCompiledCalleeBody,
        firstCompiledExp, lookupInfo,
        lookupCompiledFunction, nestedDecs]
    · simp [assignCrepValues]
    · let calleeBase : CrepState (Word 64) :=
          { locals := updateCrepLocal (fun _ => none) 0
              (BitVec.ofNat 64 41), memory := fun _ => none }
      let ffiInput : CrepState (Word 64) :=
          { locals := updateCrepLocal
              (updateCrepLocal
                (updateCrepLocal
                  (updateCrepLocal calleeBase.locals 2
                    (BitVec.ofNat 64 41)) 3 0) 4 0) 5 0,
            memory := fun _ => none }
      let ffiOutput : CrepState (Word 64) :=
          { locals := updateCrepLocal ffiInput.locals 0
              (BitVec.ofNat 64 42), memory := fun _ => none }
      let calleeOutput : CrepState (Word 64) :=
          { locals := updateCrepLocal (fun _ => none) 0
              (BitVec.ofNat 64 42), memory := fun _ => none }
      have hffi :
          declarationFfiCrepHandler "inc" (BitVec.ofNat 64 41) 0 0 0
            ffiInput = some (.returned ffiOutput) := by
        simp [declarationFfiCrepHandler, ffiInput, ffiOutput,
          calleeBase]
      have hext :
          evalCrepFullProg
            (compileToCrepe declarationFfiContext declarationFfiDeclarations)
            (fun _ _ => none) declarationFfiCrepHandler
            defaultCrepSharedMem 0 100 (13 + 1) ffiInput
            (.extCall "inc" 2 3 4 5) =
          some (.normal ffiOutput) := by
        apply evalCrepFullProg_extCall
          (configuration := 2) (configurationLength := 3)
          (array := 4) (arrayLength := 5)
          (configurationValue := BitVec.ofNat 64 41)
          (configurationLengthValue := 0) (arrayValue := 0)
          (arrayLengthValue := 0)
        · simp [ffiInput, updateCrepLocal]
        · simp [ffiInput, updateCrepLocal]
        · simp [ffiInput, updateCrepLocal]
        · simp [ffiInput, updateCrepLocal]
        · exact hffi
      have hnested :
          evalCrepFullProg
            (compileToCrepe declarationFfiContext declarationFfiDeclarations)
            (fun _ _ => none) declarationFfiCrepHandler
            defaultCrepSharedMem 0 100 18 calleeBase
            (nestedDecs [2, 3, 4, 5]
              [.const (BitVec.ofNat 64 41), .const 0, .const 0, .const 0]
              (.extCall "inc" 2 3 4 5)) =
          some (.normal calleeOutput) := by
        simp [nestedDecs, evalCrepFullProg, evalCrepFullExp,
          declarationFfiCrepHandler, restoreCrepResult,
          updateCrepLocal]
        apply crepState_eq
        · funext current
          by_cases h0 : current = 0 <;> by_cases h2 : current = 2 <;>
            by_cases h3 : current = 3 <;>
            by_cases h4 : current = 4 <;> by_cases h5 : current = 5 <;>
            all_goals simp [calleeOutput, calleeBase,
              restoreCrepLocal, updateCrepLocal, h0, h2, h3, h4, h5]
        · rfl
      have hnested' :
          evalCrepFullProg
            (compileToCrepe declarationFfiContext declarationFfiDeclarations)
            (fun _ _ => none) declarationFfiCrepHandler
            defaultCrepSharedMem 0 100 18
            { locals := updateCrepLocal (fun _ => none) 0
                (BitVec.ofNat 64 41), memory := declarationFfiInitialState.memory }
            (nestedDecs [2, 3, 4, 5]
              [.const (BitVec.ofNat 64 41), .const 0, .const 0, .const 0]
              (.extCall "inc" 2 3 4 5)) =
          some (.normal calleeOutput) := by
        simpa [calleeBase, declarationFfiInitialState] using hnested
      simp only [declarationFfiCompiledCalleeBody, evalCrepFullProg]
      rw [hnested']
      simp [evalCrepFullExps, evalCrepFullExp, calleeOutput,
        updateCrepLocal]
    · simp [allocatedNames, declarationFfiContext,
        declarationFfiInitialState, declarationFfiCallState,
        initializeCrepLocals, updateCrepLocal, assignCrepValues]
      funext current
      by_cases h : current = 1 <;>
        simp [updateCrepLocal, h]
  have hcrepBody :
      evalCrepFullProg
        (compileToCrepe declarationFfiContext declarationFfiDeclarations)
        (fun _ _ => none) declarationFfiCrepHandler
        defaultCrepSharedMem 0 100 (20 + 1) declarationFfiCallState
        (compileProg
          { vars := ("result", (.one,
              allocatedNames declarationFfiContext .one)) ::
              declarationFfiContext.vars
            functions := declarationFfiContext.functions
            exceptions := declarationFfiContext.exceptions
            maxVar := declarationFfiContext.maxVar + Shape.shapeSize .one
            bytesInWord := declarationFfiContext.bytesInWord }
          (.return (.var .local "result"))) =
      some (.returned declarationFfiCallState
        [BitVec.ofNat 64 42]) := by
    simp [declarationFfiContext, declarationFfiDeclarations,
      declarationFfiCallState, compileProg, compileExp,
      evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
      allocatedNames, updateCrepLocal, lookupInfo]
  have hrel :
      panValueCrepControlRel [] declarationFfiContext
        (fun _ _ _ => False)
        (restorePanValueControlLocal "result" none
          (.returned (fun _ => none) (fun _ => none) (fun _ => none)
            [.word (BitVec.ofNat 64 42)]))
        (restoreCrepResultList declarationFfiInitialState.locals
          (allocatedNames declarationFfiContext .one)
      (.returned declarationFfiCallState
            [BitVec.ofNat 64 42])) := by
    have hsourceRestored :
        restorePanValueLocal (fun _ : VarName => none)
            "result" (none : Option (PanValue (Word 64))) =
          (fun _ => none) := by
      funext name
      simp [restorePanValueLocal]
    have hpostState :
        panValueCrepStateRel [] declarationFfiContext
          (fun _ => none) (fun _ => none) (fun _ => none)
          { locals := restoreCrepLocal declarationFfiCallState.locals 1 none
            memory := fun _ => none } := by
      refine ⟨rfl, ?_, ?_⟩
      · intro name value shape slots hsource hlookup
        simp at hsource
      · funext address
        simp [panValueWordMemory]
    simp [panValueCrepControlRel, restorePanValueControlLocal,
      restoreCrepResultList, restoreCrepResult, allocatedNames,
      declarationFfiInitialState, declarationFfiCallState,
      hsourceRestored]
    exact ⟨hpostState, by
      exact panValueCrepValuesRel_singleton (.word (BitVec.ofNat 64 42))⟩
  have hresult := compile_full_pan_value_decCall_relation
    (context := declarationFfiContext) (structs := [])
    (sourceFunctions := declarationFfiSourceFunctions)
    (functions := compileToCrepe declarationFfiContext declarationFfiDeclarations)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none)
    (state := declarationFfiInitialState)
    (callState := declarationFfiCallState)
    (primitive := fun _ _ => none)
    (sourceHandler := declarationFfiSourceHandler)
    (crepPrimitive := fun _ _ => none)
    (ffi := declarationFfiCrepHandler)
    (sharedMem := defaultCrepSharedMem)
    (baseAddress := 0) (topAddress := 100) (bytesInWord := 8)
    (fuel := 20) (contracts := none) (memoryAccess := none)
    (memoryHandler := none) (name := "result") (shape := .one)
    (function := "ffiId")
    (arguments := [.const (BitVec.ofNat 64 41)])
    (body := .return (.var .local "result"))
    (compiledArguments := [.const (BitVec.ofNat 64 41)])
    (sourceCalleeGlobals := fun _ => none)
    (sourceCalleeMemory := fun _ => none)
    (sourceValue := .word (BitVec.ofNat 64 42))
    (sourceResult := .returned (fun _ => none) (fun _ => none)
      (fun _ => none) [.word (BitVec.ofNat 64 42)])
    (crepResult := .returned declarationFfiCallState
      [BitVec.ofNat 64 42])
    (exceptionRel := fun _ _ _ => False)
    (hcompileArgs := by
      simp [compileArgs, compileExp, declarationFfiContext])
    (hsourceCall := hsourceCall)
    (hsourceShape := by simp [panValueShape, panShapeMatches])
    (hsourceBody := hsourceBody)
    (hcrepCall := hcrepCall)
    (hcrepBody := hcrepBody)
    hrel
  have htargetRestored :
      restoreCrepLocal declarationFfiCallState.locals 1 none =
        (fun _ => none) := by
    funext current
    simp [declarationFfiCallState,
      restoreCrepLocal, updateCrepLocal]
  have hsourceRestoredFinal :
      restorePanValueLocal (fun _ : VarName => none)
          "result" (none : Option (PanValue (Word 64))) =
        (fun _ => none) := by
    funext name
    simp [restorePanValueLocal]
  have htargetRestoredFinal :
      restoreCrepLocal (fun _ : Nat => (none : Option (Word 64))) 1
          (none : Option (Word 64)) =
        (fun _ : Nat => (none : Option (Word 64))) := by
    funext current
    simp [restoreCrepLocal]
  constructor
  · simpa [declarationFfiMain, restorePanValueControlLocal,
      hsourceRestoredFinal] using hresult.1
  constructor
  · simpa [declarationFfiContext, declarationFfiInitialState,
      declarationFfiCallState, declarationFfiMain, compileProg,
      compileExp, compileArgs, nestedDecs, allocatedNames,
      Shape.shapeSize, restoreCrepResultList, restoreCrepResult,
      restoreCrepLocal, updateCrepLocal, htargetRestoredFinal] using
        hresult.2.1
  · simpa [declarationFfiContext, declarationFfiInitialState,
      declarationFfiCallState, declarationFfiMain,
      restorePanValueControlLocal, restorePanValueLocal,
      restoreCrepResultList,
      restoreCrepResult, restoreCrepLocal, updateCrepLocal,
      allocatedNames, hsourceRestoredFinal, htargetRestoredFinal] using
        hresult.2.2

/-! A failed host service must remain failed through the complete
    declaration-call lowering.  This is the negative counterpart to
    `declaration_ffi_source_to_crep_relation`: the source callee cannot
    complete its `extCall`, and the lowered Crep callee must stop at the same
    unavailable FFI boundary rather than accidentally reaching its return. -/

def declarationFfiUnavailableSourceHandler : PanValueFfiHandler (Word 64) :=
  fun _ _ _ _ _ _ => none

def declarationFfiUnavailableCrepHandler : CrepFfiHandler (Word 64) :=
  fun _ _ _ _ _ _ => none

theorem declaration_ffi_failure_propagates :
    evalPanValueProgWithPrimitiveCallsAndFfi
      (fun _ _ => none) declarationFfiUnavailableSourceHandler []
      declarationFfiSourceFunctions
      0 100 8 21
      (fun _ => none) (fun _ => none) (fun _ => none)
      declarationFfiMain = none ∧
    evalCrepFullProg
      (compileToCrepe declarationFfiContext declarationFfiDeclarations)
      (fun _ _ => none) declarationFfiUnavailableCrepHandler
      defaultCrepSharedMem 0 100 23 declarationFfiInitialState
      (compileProg declarationFfiContext declarationFfiMain) = none := by
  constructor
  · simp [declarationFfiMain, declarationFfiSourceFunctions,
      declarationFfiCalleeBody, declarationFfiUnavailableSourceHandler,
      evalPanValueProgWithPrimitiveCallsAndFfi,
      evalPanValueCallWithPrimitiveCallsAndFfi,
      evalPanValueExps, evalPanValueExp, evalPanValueExp.evalPanValueExps,
      lookupPanFunction,
      bindPanValueParameters, updatePanValueMap]
  · simp [declarationFfiContext, declarationFfiDeclarations,
      declarationFfiMain, declarationFfiCalleeBody,
      declarationFfiUnavailableCrepHandler, compileToCrepe,
      compileFunctions, compileFunDecl, compileParamVars, functionInfos,
      compileProg, compileExp, compileArgs, allocatedNames,
      firstCompiledExp, nestedDecs, evalCrepFullProg,
      evalCrepFullCall, evalCrepFullExps, evalCrepFullExp,
      lookupCompiledFunction, assignCrepValues, updateCrepLocal,
      restoreCrepResult]

end Flapjack
