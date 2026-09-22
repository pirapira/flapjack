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

def runtimeTypedRawState : CrepRuntimeTypedState Nat Unit :=
  { runtime := globalLoadRuntimeState
    globals := fun _ => none }

/- The raw runtime wrapper keeps values as Nat but carries Cake's distinct
   five-bit global key.  The aliased read is therefore a representation-level
   guard, not a target-width-keyed update disguised as a global store. -/
example :
    evalCrepRuntimeExp
        ((runtimeTypedRawState.store runtimeTypedKey 4 19).toRuntime
          runtimeTypedKey) (.loadGlob 36) = some 19 := by
  rw [CrepRuntimeTypedState.load_after_store_toRuntime]
  simp [runtimeTypedRawState, CrepRuntimeTypedState.toGlobalState,
    runtimeTypedKey, evalCrepTypedLoad, storeCrepTypedGlobal, storeCrepGlobal,
    crepGlobalKeyOfNat]

def runtimeTypedRuntimeState : CrepRuntimeState Nat Unit :=
  globalLoadRuntimeState.withTypedGlobalState runtimeTypedKey runtimeTypedBaseState

def runtimeTypedStoredGlobalState : CrepGlobalState Nat :=
  storeCrepTypedGlobal runtimeTypedKey runtimeTypedBaseState 4 11

def runtimeTypedStoredRuntimeState : CrepRuntimeState Nat Unit :=
  globalLoadRuntimeState.withTypedGlobalState runtimeTypedKey
    runtimeTypedStoredGlobalState

def runtimeTypedStoreLoadValue : Option Nat :=
  evalCrepRuntimeExp runtimeTypedStoredRuntimeState (.loadGlob 4)

def runtimeTypedAliasedStoreLoadValue : Option Nat :=
  evalCrepRuntimeExp
    (storeCrepRuntimeTypedGlobalState globalLoadRuntimeState runtimeTypedKey
      runtimeTypedBaseState 4 17) (.loadGlob 36)

#guard runtimeTypedAliasedStoreLoadValue == some 17

example (state : CrepRuntimeTypedState (RiscV.Word 8) Unit)
    (key : RiscV.Word 8 → CrepGlobalAddress)
    (address value loadAddress baseAddress topAddress : RiscV.Word 8) :
    (state.store key address value).evalExpFull key baseAddress topAddress
        (.loadGlob loadAddress) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.toGlobalState address value) loadAddress := by
  exact CrepRuntimeTypedState.evalExpFull_load_after_store state key
    address value loadAddress baseAddress topAddress

example (state : CrepRuntimeTypedState (RiscV.Word 8) Unit)
    (key : RiscV.Word 8 → CrepGlobalAddress)
    (memoryState : CrepMemoryState (RiscV.Word 8))
    (address baseAddress topAddress : RiscV.Word 8) :
    state.evalExpCheckedFull key memoryState baseAddress topAddress
        (.loadGlob address) =
      evalCrepTypedLoad key state.toGlobalState address := by
  exact CrepRuntimeTypedState.evalExpCheckedFull_loadGlob state key
    memoryState address baseAddress topAddress

example (state : CrepRuntimeTypedState (RiscV.Word 8) Unit)
    (key : RiscV.Word 8 → CrepGlobalAddress)
    (address value loadAddress baseAddress topAddress : RiscV.Word 8) :
    (state.storeGlob key baseAddress topAddress address (.const value)).bind
        (fun next => next.evalExpFull key baseAddress topAddress
          (.loadGlob loadAddress)) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.toGlobalState address value) loadAddress := by
  exact CrepRuntimeTypedState.storeGlob_load_alias state key baseAddress topAddress
    address value loadAddress

example (state : CrepRuntimeTypedState (RiscV.Word 8) Unit)
    (key : RiscV.Word 8 → CrepGlobalAddress)
    (baseAddress topAddress address loadAddress value : RiscV.Word 8)
    (expression : CrepExp (RiscV.Word 8))
    (heval : state.evalExpFull key baseAddress topAddress expression = some value) :
    (state.storeGlob key baseAddress topAddress address expression).bind
        (fun next => next.evalExpFull key baseAddress topAddress
          (.loadGlob loadAddress)) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.toGlobalState address value) loadAddress := by
  exact CrepRuntimeTypedState.storeGlob_load_alias_of_eval state key baseAddress
    topAddress address expression value loadAddress heval

def runtimeTypedLoopBaseState : LoopState Nat :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def runtimeTypedLoopGlobalState : LoopTypedGlobalState Nat :=
  { legacy := runtimeTypedLoopBaseState
    globals := runtimeTypedBaseState }

#guard ((runtimeTypedLoopGlobalState.setGlobal runtimeTypedKey 4 (.const 17)).bind
    (fun state => state.load runtimeTypedKey 36)) == some 17

example :
    (runtimeTypedLoopGlobalState.store runtimeTypedKey 4 17).toLoopState
        runtimeTypedKey =
      loopStateWithTypedGlobalStore runtimeTypedLoopBaseState runtimeTypedKey
        runtimeTypedBaseState 4 17 := by
  exact LoopTypedGlobalState.toLoopState_store runtimeTypedLoopGlobalState
    runtimeTypedKey 4 17

example :
    (runtimeTypedLoopGlobalState.setGlobal runtimeTypedKey 4 (.const 17)).bind
        (fun state => state.load runtimeTypedKey 36) = some 17 := by
  exact LoopTypedGlobalState.setGlobal_load_alias runtimeTypedLoopGlobalState
    runtimeTypedKey 4 17 36

example (state : LoopTypedGlobalState (RiscV.Word 8))
    (key : RiscV.Word 8 → CrepGlobalAddress)
    (address value loadAddress : RiscV.Word 8) :
    (state.setGlobalFull key address (.const value)).bind
        (fun next => next.load key loadAddress) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.globals address value) loadAddress := by
  exact LoopTypedGlobalState.setGlobalFull_load_alias state key address value loadAddress

example :
    ((runtimeTypedLoopGlobalState.store runtimeTypedKey 4 17).toLoopState
        runtimeTypedKey).globals 36 = some 17 := by
  rw [LoopTypedGlobalState.store_toLoopState_load]
  simp [runtimeTypedLoopGlobalState, runtimeTypedKey, storeCrepTypedGlobal,
    evalCrepTypedLoad, storeCrepGlobal, crepGlobalKeyOfNat]

example :
    (runtimeTypedLoopGlobalState.store runtimeTypedKey 4 17).evalExp
        runtimeTypedKey (.lookup 36) = some 17 := by
  rw [LoopTypedGlobalState.store_evalExp_lookup]
  simp [runtimeTypedLoopGlobalState, runtimeTypedKey, storeCrepTypedGlobal,
    evalCrepTypedLoad, storeCrepGlobal, crepGlobalKeyOfNat]

def runtimeTypedAliasedLoopStoreState : LoopState Nat :=
  loopStateWithTypedGlobalStore runtimeTypedLoopBaseState runtimeTypedKey
    runtimeTypedBaseState 4 17

/- The Loop adapter preserves Cake's fixed-key alias fiber: a store at 4 is
   visible through the distinct target-width address 36, while its relation is
   stated against the typed 5-bit map rather than against raw equality. -/
#guard runtimeTypedAliasedLoopStoreState.globals 36 == some 17

example :
    CrepGlobalKeyRelation runtimeTypedKey
      runtimeTypedAliasedLoopStoreState.globals
      (storeCrepTypedGlobal runtimeTypedKey runtimeTypedBaseState 4 17).globals := by
  exact loopStateWithTypedGlobalStore_relation runtimeTypedLoopBaseState
    runtimeTypedKey runtimeTypedBaseState 4 17

example :
    runtimeTypedAliasedLoopStoreState.globals 36 =
      (storeCrepTypedGlobal runtimeTypedKey runtimeTypedBaseState 4 17).globals
        (runtimeTypedKey 36) := by
  exact loopStateWithTypedGlobalStore_load runtimeTypedLoopBaseState
    runtimeTypedKey runtimeTypedBaseState 4 36 17

example :
    evalCrepTypedLoad runtimeTypedKey
        (storeCrepTypedGlobal runtimeTypedKey runtimeTypedBaseState 4 17) 36 =
      runtimeTypedAliasedLoopStoreState.globals 36 := by
  exact loopStateWithTypedGlobalStore_typed_load runtimeTypedLoopBaseState
    runtimeTypedKey runtimeTypedBaseState 4 36 17

example :
    loopStateWithTypedGlobalStore
        (loopStateOfCrepRuntimeStateForGlobals globalLoadRuntimeState)
        runtimeTypedKey runtimeTypedBaseState 4 17 =
      loopStateOfCrepRuntimeStateForGlobals
        (storeCrepRuntimeTypedGlobalState globalLoadRuntimeState runtimeTypedKey
          runtimeTypedBaseState 4 17) := by
  exact loopStateWithTypedGlobalStore_runtime_adapter globalLoadRuntimeState
    runtimeTypedKey runtimeTypedBaseState 4 17

example :
    crepRuntimeTypedGlobalRelation runtimeTypedKey
      (storeCrepRuntimeTypedGlobalState globalLoadRuntimeState runtimeTypedKey
        runtimeTypedBaseState 4 17)
      (storeCrepTypedGlobal runtimeTypedKey runtimeTypedBaseState 4 17) := by
  exact crepRuntimeTypedGlobalRelation_store_adapter _ _ _ _ _

example : runtimeTypedAliasedStoreLoadValue = some 17 := by
  change evalCrepRuntimeExp
    (storeCrepRuntimeTypedGlobalState globalLoadRuntimeState runtimeTypedKey
      runtimeTypedBaseState 4 17) (.loadGlob 36) = some 17
  rw [evalCrepRuntimeExp_loadGlob_after_store_typedState]
  simp [runtimeTypedKey, runtimeTypedBaseState, storeCrepTypedGlobal,
    evalCrepTypedLoad, storeCrepGlobal, crepGlobalKeyOfNat]

/- The Loop-side projection carries the same fixed-width key relation, so an
   aliased read observes the Cake typed global state rather than an exact
   target-width address update. -/
example :
    CrepGlobalKeyRelation runtimeTypedKey
      (loopStateOfCrepRuntimeStateForGlobals runtimeTypedStoredRuntimeState).globals
      runtimeTypedStoredGlobalState.globals := by
  exact crepRuntimeTypedGlobalRelation_loopState_adapter
    globalLoadRuntimeState runtimeTypedKey runtimeTypedStoredGlobalState

example :
    (loopStateOfCrepRuntimeStateForGlobals runtimeTypedStoredRuntimeState).globals
      36 = some 11 := by
  change runtimeTypedStoredGlobalState.globals (runtimeTypedKey 36) = some 11
  simp [runtimeTypedStoredGlobalState, runtimeTypedBaseState, runtimeTypedKey,
    storeCrepTypedGlobal, storeCrepGlobal, crepGlobalKeyOfNat]

/- The relation-level guard uses the actual Cake key type.  On a 5-bit target
   the re-keying is injective, so the runtime's ordinary updateMemory is the
   same update as the source's typed StoreGlob map. -/
example (state : CrepRuntimeState (BitVec 5) Unit)
    (typedState : CrepGlobalState (BitVec 5))
    (address value : BitVec 5)
    (hrel : crepRuntimeTypedGlobalRelation (id : BitVec 5 → CrepGlobalAddress)
      state typedState) :
    crepRuntimeTypedGlobalRelation (id : BitVec 5 → CrepGlobalAddress)
      { state with globals := updateMemory state.globals address value }
      (storeCrepTypedGlobal id typedState address value) := by
  exact crepRuntimeTypedGlobalRelation_store_of_noalias id state typedState
    address value hrel (fun _ h => h)

example (state : CrepRuntimeState (BitVec 5) Unit)
    (typedState : CrepGlobalState (BitVec 5))
    (address value : BitVec 5) :
    crepRuntimeLoopTypedGlobalRel (id : BitVec 5 → CrepGlobalAddress)
      { (state.withTypedGlobalState id typedState) with
        globals := updateMemory
          (state.withTypedGlobalState id typedState).globals address value }
      { (loopStateOfCrepRuntimeStateForGlobals
          (state.withTypedGlobalState id typedState)) with
        globals := updateLoopGlobal
          (state.withTypedGlobalState id typedState).globals address value }
      (storeCrepTypedGlobal id typedState address value) := by
  exact crepRuntimeLoopTypedGlobalRel_store_of_noalias state id typedState
    address value (fun _ h => h)

example (state : CrepRuntimeState (BitVec 5) Unit)
    (typedState : CrepGlobalState (BitVec 5))
    (address value : BitVec 5) :
    CrepGlobalKeyRelation (id : BitVec 5 → CrepGlobalAddress)
      (updateLoopGlobal (state.withTypedGlobalState id typedState).globals
        address value)
      (storeCrepTypedGlobal id typedState address value).globals := by
  exact crepRuntimeTypedGlobalRelation_loopStore_of_noalias
    state id typedState address value (fun _ h => h)

/- The guard routes runtime LoadGlob through the typed StoreGlob entrypoint,
   whose expected value is the source `crepSem` store/load result. -/
example : runtimeTypedStoreLoadValue = some 11 := by
  change evalCrepRuntimeExp
    (globalLoadRuntimeState.withTypedGlobalState runtimeTypedKey
      runtimeTypedStoredGlobalState) (.loadGlob 4) = some 11
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
        ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadGlob 200)))).map
        (fun result => (loopResultState result).locals 5) := by
  exact crepRuntimeToLoop_loadGlob_assign_agreement
      ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    globalLoadRuntimeState [] 5 200 42
    ⟨0, by simp [globalLoadRuntimeState]⟩
    (by simp [lookupNatInfo])
    (by simp [globalLoadRuntimeState])

theorem typedCrepRuntimeToLoop_loadGlob_regression :
    (evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 2
      runtimeTypedStoredRuntimeState (.assign 5 (.loadGlob 4))).map
        (fun result => result.2.locals 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      3 (loopStateOfCrepRuntimeStateForGlobals runtimeTypedStoredRuntimeState)
      (loopCompileProg
        ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadGlob 4)))).map
        (fun result => (loopResultState result).locals 5) := by
  exact crepRuntimeToLoop_loadGlob_assign_agreement_typed
    ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1 globalLoadRuntimeState
    runtimeTypedKey runtimeTypedStoredGlobalState [] 5 4 11
    ⟨0, by simp [globalLoadRuntimeState]⟩
    (by simp [lookupNatInfo])
    (by simp [runtimeTypedStoredGlobalState, runtimeTypedBaseState,
      storeCrepTypedGlobal, storeCrepGlobal])

theorem typedCrepRuntimeToLoop_loadGlob_failure_regression :
    (evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 2
      runtimeTypedStoredRuntimeState (.assign 5 (.loadGlob 4))).bind
        (crepRuntimeLocalProjection 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      3 (loopStateOfCrepRuntimeStateForGlobals runtimeTypedStoredRuntimeState)
      (loopCompileProg
        ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadGlob 4)))).map
        (fun result => (loopResultState result).locals 5) := by
  exact crepRuntimeToLoop_loadGlob_assign_failure_agreement_typed
    ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1 globalLoadRuntimeState
    runtimeTypedKey runtimeTypedStoredGlobalState [] 5 4
    ⟨0, by simp [globalLoadRuntimeState]⟩
    (by simp [lookupNatInfo])

theorem typedCrepRuntimeToLoop_storeGlob_loadGlob_sequence_regression :
    (evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 3
      (globalLoadRuntimeState.withTypedGlobalState runtimeTypedKey
        runtimeTypedBaseState)
      (.seq (.storeGlob 4 (.const 13)) (.assign 5 (.loadGlob 4)))).map
        (fun result => result.2.globals 4) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      4
      (loopStateOfCrepRuntimeStateForGlobals
        (globalLoadRuntimeState.withTypedGlobalState runtimeTypedKey
          runtimeTypedBaseState))
      (loopCompileProg
        ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.seq (.storeGlob 4 (.const 13)) (.assign 5 (.loadGlob 4))))).map
        (fun result => (loopResultState result).globals 4) := by
  exact crepRuntimeToLoop_storeGlob_loadGlob_sequence_agreement_typed
    ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1 globalLoadRuntimeState
    runtimeTypedKey runtimeTypedBaseState 5 4 13
    ⟨0, by simp [globalLoadRuntimeState]⟩
    (by simp [lookupNatInfo])

theorem typedCrepRuntimeToLoop_storeGlob_state_regression :
    ∃ sourceTarget loopTarget,
      evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 2
        (globalLoadRuntimeState.withTypedGlobalState runtimeTypedKey
          runtimeTypedBaseState)
        (.storeGlob 4 (.const 13)) =
        some (.normal, sourceTarget) ∧
      evalLoopProgWithCallsAndFfi []
        (fun _ _ _ _ _ loopState => some loopState) 3
        (loopStateOfCrepRuntimeStateForGlobals
          (globalLoadRuntimeState.withTypedGlobalState runtimeTypedKey
            runtimeTypedBaseState))
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [] (.storeGlob 4 (.const 13))) =
        some (.normal loopTarget) ∧
      crepRuntimeLoopStateRel sourceTarget loopTarget := by
  exact crepRuntimeToLoop_storeGlob_state_agreement_typed
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1 globalLoadRuntimeState
    runtimeTypedKey runtimeTypedBaseState [] 4 13

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
        ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadGlob 200)))).map
        (fun result => (loopResultState result).locals 5) := by
  exact crepRuntimeToLoop_loadGlob_assign_failure_agreement
    ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    { globalLoadRuntimeState with globals := fun _ => none } [] 5 200
    ⟨0, by simp [globalLoadRuntimeState]⟩
    (by simp [lookupNatInfo])

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
        ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.seq (.storeGlob 200 (.const 42)) (.assign 5 (.loadGlob 200))))).map
        (fun result => (loopResultState result).globals 200) := by
  exact crepRuntimeToLoop_storeGlob_loadGlob_sequence_agreement
    ({ vars := [(5, 5)], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    { globalLoadRuntimeState with globals := fun _ => none } 5 200 42
    ⟨0, by simp [globalLoadRuntimeState]⟩
    (by simp [lookupNatInfo])

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
