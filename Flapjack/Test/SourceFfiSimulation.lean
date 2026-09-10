import Flapjack.CorrectnessFfiSource

/-! Regression for the source-local FFI state-relation boundary. -/

namespace Flapjack

def sourceFfiSimulationCompileContext : CompileContext (RiscV.Word 64) :=
  { vars := [("configuration", (.one, [1])),
      ("configurationLength", (.one, [2])),
      ("array", (.one, [3])), ("arrayLength", (.one, [4]))]
    functions := []
    exceptions := []
    maxVar := 0
    bytesInWord := BitVec.ofNat 64 8 }

def sourceFfiSimulationLoopContext : LoopContext (RiscV.Word 64) :=
  { vars := []
    functions := []
    maxVar := 0
    target := .rv64i }

def sourceFfiSimulationLocals (configuration configurationLength array arrayLength :
    RiscV.Word 64) : VarName → Option (RiscV.Word 64) :=
  fun name =>
    if name == "configuration" then some configuration
    else if name == "configurationLength" then some configurationLength
    else if name == "array" then some array
    else if name == "arrayLength" then some arrayLength
    else none

def sourceFfiSimulationState
    (configuration configurationLength array arrayLength : RiscV.Word 64) :
    LoopState (RiscV.Word 64) :=
  { locals := fun name =>
      if name = 1 then some configuration
      else if name = 2 then some configurationLength
      else if name = 3 then some array
      else if name = 4 then some arrayLength
      else none
    globals := fun _ => none
    memory := fun _ => none }

def sourceFfiSimulationHandler :
    FunName → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 →
      RiscV.Word 64 → LoopState (RiscV.Word 64) →
        Option (LoopState (RiscV.Word 64)) :=
  fun function configuration configurationLength array arrayLength state =>
    if function == "echo" then
      some ({ state with locals :=
          (updateLoopLocal
            (updateLoopLocal
              (updateLoopLocal
                (updateLoopLocal state.locals 9 configuration)
                10 configurationLength)
              11 array)
            12 arrayLength) })
    else none

def sourceFfiSimulationSourceHandler : PanFfiHandler (RiscV.Word 64) :=
  fun function configuration configurationLength array arrayLength locals =>
    if function == "echo" then
      some (updatePanLocal
        (updatePanLocal
          (updatePanLocal
            (updatePanLocal locals "seenConfiguration" configuration)
            "seenConfigurationLength" configurationLength)
          "seenArray" array)
        "seenArrayLength" arrayLength)
    else none

def sourceFfiSimulationNextLocals
    (configuration configurationLength array arrayLength : RiscV.Word 64) :
    VarName → Option (RiscV.Word 64) :=
  updatePanLocal
    (updatePanLocal
      (updatePanLocal
        (updatePanLocal
          (sourceFfiSimulationLocals configuration configurationLength array arrayLength)
          "seenConfiguration" configuration)
        "seenConfigurationLength" configurationLength)
      "seenArray" array)
    "seenArrayLength" arrayLength

def sourceFfiSimulationNextState
    (configuration configurationLength array arrayLength : RiscV.Word 64) :
    LoopState (RiscV.Word 64) :=
  { sourceFfiSimulationState configuration configurationLength array arrayLength with
    locals :=
      (updateLoopLocal
        (updateLoopLocal
          (updateLoopLocal
            (updateLoopLocal
              (sourceFfiSimulationState configuration configurationLength array arrayLength).locals
              9 configuration)
            10 configurationLength)
          11 array)
        12 arrayLength) }

def sourceFfiSimulationRelation :
    LoopState (RiscV.Word 64) → (VarName → Option (RiscV.Word 64)) → Prop :=
  fun state locals =>
    state.locals 9 = locals "seenConfiguration" ∧
      state.locals 10 = locals "seenConfigurationLength" ∧
      state.locals 11 = locals "seenArray" ∧
      state.locals 12 = locals "seenArrayLength"

theorem sourceFfiSimulation_leaf (configuration configurationLength array arrayLength :
    RiscV.Word 64) :
    evalLoopProgWithCallsAndFfi [] sourceFfiSimulationHandler 40
      (sourceFfiSimulationState configuration configurationLength array arrayLength)
      (loopCompileProg sourceFfiSimulationLoopContext []
        (compileProg sourceFfiSimulationCompileContext
          (.extCall "echo" (.var .local "configuration")
            (.var .local "configurationLength") (.var .local "array")
            (.var .local "arrayLength")))) =
      some (.normal
        (sourceFfiSimulationNextState configuration configurationLength array arrayLength)) := by
  have hsim :
      evalLoopProgWithCallsAndFfi [] sourceFfiSimulationHandler 40
          (sourceFfiSimulationState configuration configurationLength array arrayLength)
          (loopCompileProg sourceFfiSimulationLoopContext []
            (compileProg sourceFfiSimulationCompileContext
              (.extCall "echo" (.var .local "configuration")
                (.var .local "configurationLength") (.var .local "array")
                (.var .local "arrayLength")))) =
        some (.normal
          (sourceFfiSimulationNextState configuration configurationLength array arrayLength)) ∧
      evalPanProgWithCallsAndFfi [] sourceFfiSimulationSourceHandler 20
          (sourceFfiSimulationLocals configuration configurationLength array arrayLength)
          (.extCall "echo" (.var .local "configuration")
            (.var .local "configurationLength") (.var .local "array")
            (.var .local "arrayLength")) =
        some (.normal
          (sourceFfiSimulationNextLocals configuration configurationLength array arrayLength)) ∧
      sourceFfiSimulationRelation
          (sourceFfiSimulationNextState configuration configurationLength array arrayLength)
          (sourceFfiSimulationNextLocals configuration configurationLength array arrayLength) := by
    apply compilePanToLoop_extCall_local_state_simulation
      sourceFfiSimulationCompileContext sourceFfiSimulationLoopContext
      (sourceFfiSimulationState configuration configurationLength array arrayLength)
      (sourceFfiSimulationLocals configuration configurationLength array arrayLength)
      sourceFfiSimulationHandler sourceFfiSimulationSourceHandler "echo"
      configuration configurationLength array arrayLength
      (sourceFfiSimulationNextState configuration configurationLength array arrayLength)
      (sourceFfiSimulationNextLocals configuration configurationLength array arrayLength)
      sourceFfiSimulationRelation rfl
    all_goals simp [sourceFfiSimulationCompileContext,
      sourceFfiSimulationLocals, sourceFfiSimulationState,
      sourceFfiSimulationHandler, sourceFfiSimulationSourceHandler,
      sourceFfiSimulationNextLocals, sourceFfiSimulationNextState,
      sourceFfiSimulationRelation, updateLoopLocal, updatePanLocal,
      sourceFfiSetupState, lookupInfo, evalPanExtCall, evalPanExp]
    · funext name
      by_cases h1 : name = 1
      · subst name
        simp [updateLoopLocal]
      · by_cases h2 : name = 2
        · subst name
          simp [updateLoopLocal]
        · by_cases h3 : name = 3
          · subst name
            simp [updateLoopLocal]
          · by_cases h4 : name = 4
            · subst name
              simp [updateLoopLocal]
            · simp [updateLoopLocal, h1, h2, h3, h4]
  exact hsim.1

theorem sourceFfiSimulation_sequence
    (configuration configurationLength array arrayLength : RiscV.Word 64) :
    evalLoopProgWithCallsAndFfi [] sourceFfiSimulationHandler 41
      (sourceFfiSimulationState configuration configurationLength array arrayLength)
      (loopCompileProg sourceFfiSimulationLoopContext []
        (compileProg sourceFfiSimulationCompileContext
          (.seq (.extCall "echo" (.var .local "configuration")
            (.var .local "configurationLength") (.var .local "array")
            (.var .local "arrayLength")) .skip))) =
        some (.normal
          (sourceFfiSimulationNextState configuration configurationLength array arrayLength)) ∧
    evalPanProgWithCallsAndFfi [] sourceFfiSimulationSourceHandler 21
      (sourceFfiSimulationLocals configuration configurationLength array arrayLength)
      (.seq (.extCall "echo" (.var .local "configuration")
        (.var .local "configurationLength") (.var .local "array")
        (.var .local "arrayLength")) .skip) =
      some (.normal
        (sourceFfiSimulationNextLocals configuration configurationLength array arrayLength)) := by
  apply compilePanToLoop_seq_after_extCall
    sourceFfiSimulationCompileContext sourceFfiSimulationLoopContext
    (sourceFfiSimulationState configuration configurationLength array arrayLength)
    (sourceFfiSimulationLocals configuration configurationLength array arrayLength)
    sourceFfiSimulationHandler sourceFfiSimulationSourceHandler "echo"
    (sourceFfiSimulationNextState configuration configurationLength array arrayLength)
    (sourceFfiSimulationNextLocals configuration configurationLength array arrayLength)
    (.skip : Prog (RiscV.Word 64)) (.skip : LoopProg (RiscV.Word 64))
    (.normal (sourceFfiSimulationNextLocals configuration configurationLength array arrayLength))
    (.normal (sourceFfiSimulationNextState configuration configurationLength array arrayLength))
  · exact sourceFfiSimulation_leaf configuration configurationLength array arrayLength
  · simp [sourceFfiSimulationLocals,
      sourceFfiSimulationSourceHandler, sourceFfiSimulationNextLocals,
      evalPanProgWithCallsAndFfi, evalPanExtCall, evalPanExp]
  · simp [compileProg, loopCompileProg]
  · simp [evalLoopProgWithCallsAndFfi, evalLoopProg]
  · simp [evalPanProgWithCallsAndFfi]

theorem sourceFfiSimulation_failure
    (configuration configurationLength array arrayLength : RiscV.Word 64) :
    evalLoopProgWithCallsAndFfi [] sourceFfiSimulationHandler 40
      (sourceFfiSimulationState configuration configurationLength array arrayLength)
      (loopCompileProg sourceFfiSimulationLoopContext []
        (compileProg sourceFfiSimulationCompileContext
          (.extCall "missing" (.var .local "configuration")
            (.var .local "configurationLength") (.var .local "array")
            (.var .local "arrayLength")))) = none ∧
    evalPanProgWithCallsAndFfi [] sourceFfiSimulationSourceHandler 20
      (sourceFfiSimulationLocals configuration configurationLength array arrayLength)
      (.extCall "missing" (.var .local "configuration")
        (.var .local "configurationLength") (.var .local "array")
        (.var .local "arrayLength")) = none := by
  apply compilePanToLoop_extCall_local_failure
    sourceFfiSimulationCompileContext sourceFfiSimulationLoopContext
    (sourceFfiSimulationState configuration configurationLength array arrayLength)
    (sourceFfiSimulationLocals configuration configurationLength array arrayLength)
    sourceFfiSimulationHandler sourceFfiSimulationSourceHandler "missing"
    configuration configurationLength array arrayLength rfl
  all_goals simp [sourceFfiSimulationCompileContext,
    sourceFfiSimulationLocals, sourceFfiSimulationState,
    sourceFfiSimulationHandler, sourceFfiSimulationSourceHandler,
    evalPanExtCall, evalPanExp, lookupInfo]

end Flapjack
