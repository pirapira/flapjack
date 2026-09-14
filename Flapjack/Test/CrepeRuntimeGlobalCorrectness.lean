import Flapjack.CrepeRuntimeGlobalCorrectness

namespace Flapjack

def globalLoadRuntimeState : CrepRuntimeState Nat Unit :=
  { locals := fun name => if name == 5 then some 0 else none
    globals := fun address => if address == 200 then some 42 else none
    functions := []
    memory := fun _ => none
    memaddrs := fun _ => true
    shMemaddrs := fun _ => true
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 1
    ffiContext := natCrepRuntimeFfiContext
    clock := 10
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 100 }

def globalLoadRuntimeHandler : CrepRuntimeFfiHandler Nat Unit Unit :=
  fun _ state => .returned state []

/-! The runtime adapter keeps the target-width runtime state intact while
    routing its global field through the source-shaped 5-bit evaluator. -/

def runtimeTypedKey : Nat → CrepGlobalAddress := crepGlobalKeyOfNat

def runtimeTypedBaseState : CrepGlobalState Nat :=
  { locals := fun _ => none
    memory := fun _ => none
    globals := fun _ => none }

def runtimeTypedRuntimeState : CrepRuntimeState Nat Unit :=
  globalLoadRuntimeState.withTypedGlobalState runtimeTypedKey runtimeTypedBaseState

def runtimeTypedStoredRuntimeState : CrepRuntimeState Nat Unit :=
  storeCrepRuntimeTypedGlobalState runtimeTypedRuntimeState runtimeTypedKey
    runtimeTypedBaseState 4 11

def runtimeTypedStoreLoadValue : Option Nat :=
  evalCrepRuntimeExp runtimeTypedStoredRuntimeState (.loadGlob 4)

/- The guard routes runtime LoadGlob through the typed StoreGlob entrypoint,
   whose expected value is the source `crepSem` store/load result. -/
example : runtimeTypedStoreLoadValue = some 11 := by
  simp only [runtimeTypedStoreLoadValue, runtimeTypedStoredRuntimeState,
    storeCrepRuntimeTypedGlobalState]
  rw [evalCrepRuntimeExp_loadGlob_typedState]
  exact evalCrepTypedLoad_storeCrepTypedGlobal runtimeTypedKey
    runtimeTypedBaseState 4 11

theorem peerCrepRuntimeToLoop_loadGlob_regression :
    (evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 2
      globalLoadRuntimeState (.assign 5 (.loadGlob 200))).map
        (fun result => result.2.locals 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      3 (loopStateOfCrepRuntimeStateForGlobals globalLoadRuntimeState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadGlob 200)))).map
        (fun result => (loopResultState result).locals 5) := by
  exact crepRuntimeToLoop_loadGlob_assign_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    globalLoadRuntimeState [] 5 200 42
    ⟨0, by simp [globalLoadRuntimeState]⟩
    (by simp [globalLoadRuntimeState])

theorem peerCrepRuntimeToLoop_loadGlob_failure_regression :
    (evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 2
      { globalLoadRuntimeState with globals := fun _ => none }
      (.assign 5 (.loadGlob 200))).bind
        (crepRuntimeLocalProjection 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      3
      (loopStateOfCrepRuntimeStateForGlobals
        { globalLoadRuntimeState with globals := fun _ => none })
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadGlob 200)))).map
        (fun result => (loopResultState result).locals 5) := by
  exact crepRuntimeToLoop_loadGlob_assign_failure_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    { globalLoadRuntimeState with globals := fun _ => none } [] 5 200
    ⟨0, by simp [globalLoadRuntimeState]⟩

theorem peerCrepRuntimeToLoop_storeGlob_loadGlob_sequence_regression :
    (evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 3
      { globalLoadRuntimeState with globals := fun _ => none }
      (.seq (.storeGlob 200 (.const 42)) (.assign 5 (.loadGlob 200)))).map
        (fun result => result.2.globals 200) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      4
      (loopStateOfCrepRuntimeStateForGlobals
        { globalLoadRuntimeState with globals := fun _ => none })
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.seq (.storeGlob 200 (.const 42)) (.assign 5 (.loadGlob 200))))).map
        (fun result => (loopResultState result).globals 200) := by
  exact crepRuntimeToLoop_storeGlob_loadGlob_sequence_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    { globalLoadRuntimeState with globals := fun _ => none } 5 200 42
    ⟨0, by simp [globalLoadRuntimeState]⟩

theorem peerCrepRuntimeToLoop_storeGlob_state_regression :
    ∃ sourceTarget loopTarget,
      evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 2
        globalLoadRuntimeState (.storeGlob 200 (.const 42)) =
        some (.normal, sourceTarget) ∧
      evalLoopProgWithCallsAndFfi []
        (fun _ _ _ _ _ loopState => some loopState) 3
        (loopStateOfCrepRuntimeStateForGlobals globalLoadRuntimeState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [] (.storeGlob 200 (.const 42))) =
        some (.normal loopTarget) ∧
      crepRuntimeLoopStateRel sourceTarget loopTarget := by
  exact crepRuntimeToLoop_storeGlob_state_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    globalLoadRuntimeState [] 200 42

end Flapjack
