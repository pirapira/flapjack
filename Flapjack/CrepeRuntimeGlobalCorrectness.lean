import Flapjack.CrepeRuntime
import Flapjack.CrepeGlobalEvaluator
import Flapjack.LoopSemantics

namespace Flapjack

/-! The runtime evaluator and Loop both read globals from their global
    environment.  This boundary is intentionally separate from the compact
    adapter, whose legacy model has no global field. -/
def loopStateOfCrepRuntimeStateForGlobals (state : CrepRuntimeState α σ) : LoopState α :=
  { locals := state.locals
    globals := state.globals
    memory := state.memory }

/-! A typed global-store adapter for the Loop-side state.  `LoopState` keeps
    its historical compact map for executable compatibility, so this wrapper
    projects a `CrepGlobalState` through `toCompact` after a Cake-typed store.
    In particular, all target-width addresses sharing a 5-bit key observe
    the same update; the adapter never replaces the source key with the raw
    target-width address used by `updateLoopGlobal`. -/
def loopStateWithTypedGlobalState
    (state : LoopState α) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) : LoopState α :=
  { state with globals := (typedState.toCompact key).globals }

def loopStateWithTypedGlobalStore [BEq α]
    (state : LoopState α) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address value : α) : LoopState α :=
  loopStateWithTypedGlobalState state key
    (storeCrepTypedGlobal key typedState address value)

/-! A typed Loop-side state for the global operations that are source
    `StoreGlob`/`LoadGlob` boundaries.  The legacy `LoopState` is retained as
    the executable projection; only the global field is supplied by the typed
    Cake state when that projection is requested. -/
structure LoopTypedGlobalState (α : Type u) where
  legacy : LoopState α
  globals : CrepGlobalState α

namespace LoopTypedGlobalState

def toLoopState (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) : LoopState α :=
  loopStateWithTypedGlobalState state.legacy key state.globals

def store [BEq α] (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (address value : α) :
    LoopTypedGlobalState α :=
  { state with globals := storeCrepTypedGlobal key state.globals address value }

def load [BEq α] (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (address : α) : Option α :=
  evalCrepTypedLoad key state.globals address

def evalExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α] (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (expression : LoopExp α) : Option α :=
  evalLoopExp (state.toLoopState key) expression

/-! Target-word Loop expressions must use Cake's complete `word_sh` rule.  Keep
    the historical evaluator above for compatibility, while exposing the
    typed-global projection through the full evaluator for RISC-V callers. -/
def evalExpFull [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α] [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [Complement α] (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (expression : LoopExp α) : Option α :=
  evalLoopExpFull (state.toLoopState key) expression

def setGlobal [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α] (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (address : α) (expression : LoopExp α) :
    Option (LoopTypedGlobalState α) := do
  let value ← state.evalExp key expression
  pure (state.store key address value)

def setGlobalFull [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α] [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [Complement α] (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (address : α) (expression : LoopExp α) :
    Option (LoopTypedGlobalState α) := do
  let value ← state.evalExpFull key expression
  pure (state.store key address value)

theorem toLoopState_store [BEq α]
    (state : LoopTypedGlobalState α) (key : α → CrepGlobalAddress)
    (address value : α) :
    (state.store key address value).toLoopState key =
      loopStateWithTypedGlobalStore state.legacy key state.globals address value := by
  rfl

theorem evalExp_lookup [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α] (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (address : α) :
    state.evalExp key (.lookup address) = state.load key address := by
  rfl

theorem setGlobal_load_alias [BEq α] [LawfulBEq α]
    [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α] (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (address value loadAddress : α) :
    (state.setGlobal key address (.const value)).bind
        (fun next => next.load key loadAddress) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.globals address value) loadAddress := by
  simp [setGlobal, evalExp, load, store, evalLoopExp,
    evalCrepTypedLoad, storeCrepTypedGlobal, storeCrepGlobal]

theorem setGlobalFull_load_alias [BEq α] [LawfulBEq α]
    [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α] [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [Complement α] (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (address value loadAddress : α) :
    (state.setGlobalFull key address (.const value)).bind
        (fun next => next.load key loadAddress) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.globals address value) loadAddress := by
  simp [setGlobalFull, evalExpFull, load, store, evalLoopExpFull,
    evalCrepTypedLoad, storeCrepTypedGlobal, storeCrepGlobal]

/-! The legacy Loop projection can be used by executable callers without
    losing Cake's fixed-width global key.  This is the direct LoadGlob
    boundary after a typed StoreGlob; unlike `updateLoopGlobal`, it needs no
    no-alias premise because the store happens in the typed map first. -/
theorem store_toLoopState_load [BEq α]
    (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (address value loadAddress : α) :
    ((state.store key address value).toLoopState key).globals loadAddress =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.globals address value) loadAddress := by
  rfl

/-! The executable Loop expression evaluator can consume the typed store
    directly through its lookup constructor.  This is the evaluator-facing
    form of `store_toLoopState_load`; unlike raw `updateLoopGlobal`, the
    typed store preserves Cake's fixed-width key and therefore needs no
    injectivity premise. -/
theorem store_evalExp_lookup [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanCmp α]
    (state : LoopTypedGlobalState α)
    (key : α → CrepGlobalAddress) (address value loadAddress : α) :
    (state.store key address value).evalExp key (.lookup loadAddress) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.globals address value) loadAddress := by
  rw [LoopTypedGlobalState.evalExp_lookup]
  rfl

end LoopTypedGlobalState

theorem loopStateWithTypedGlobalStore_relation [BEq α]
    (state : LoopState α) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address value : α) :
    CrepGlobalKeyRelation key
      (loopStateWithTypedGlobalStore state key typedState address value).globals
      (storeCrepTypedGlobal key typedState address value).globals := by
  exact CrepGlobalState.relation_toCompact key
    (storeCrepTypedGlobal key typedState address value)

theorem loopStateWithTypedGlobalStore_load [BEq α]
    (state : LoopState α) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address loadAddress value : α) :
    (loopStateWithTypedGlobalStore state key typedState address value).globals
        loadAddress =
      (storeCrepTypedGlobal key typedState address value).globals
        (key loadAddress) := by
  rfl

theorem loopStateWithTypedGlobalStore_typed_load [BEq α]
    (state : LoopState α) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address loadAddress value : α) :
    evalCrepTypedLoad key
        (storeCrepTypedGlobal key typedState address value) loadAddress =
      (loopStateWithTypedGlobalStore state key typedState address value).globals
        loadAddress := by
  rfl

def crepRuntimeLocalProjection (name : Nat)
    (step : CrepRuntimeStep α σ ε) : Option α :=
  match step.1 with
  | .error => none
  | _ => step.2.locals name

def crepRuntimeLoopStateRel (source : CrepRuntimeState α σ)
    (target : LoopState α) : Prop :=
  source.locals = target.locals ∧
  source.globals = target.globals ∧
  source.memory = target.memory

theorem crepRuntimeLoopStateRel_adapter (state : CrepRuntimeState α σ) :
    crepRuntimeLoopStateRel state
      (loopStateOfCrepRuntimeStateForGlobals state) := by
  simp [crepRuntimeLoopStateRel, loopStateOfCrepRuntimeStateForGlobals]

/-! Typed global-state adapter.

`CrepRuntimeState` keeps the historical compact global map in its generic
runtime shape.  This adapter overlays that field with the source-shaped
`CrepGlobalState.toCompact` projection, so the existing runtime evaluator can
execute `LoadGlob`/`StoreGlob` while the typed key/value boundary remains in
`CrepeGlobalEvaluator`. -/

def CrepRuntimeState.withTypedGlobalState
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) : CrepRuntimeState α σ :=
  { state with globals := (typedState.toCompact key).globals }

/-! Explicitly relate the runtime's legacy target-width global map to Cake's
    source-shaped fixed-width map.  Keeping this relation separate from the
    runtime record lets the existing evaluator remain executable while making
    the key/value distinction part of every typed correctness boundary. -/

def crepRuntimeTypedGlobalRelation
    (key : α → CrepGlobalAddress) (state : CrepRuntimeState α σ)
    (typedState : CrepGlobalState α) : Prop :=
  CrepGlobalKeyRelation key state.globals typedState.globals

/-! Typed global-aware replacement for the legacy raw runtime/Loop relation.
    The executable fields remain related by equality, while globals are also
    related to Cake's fixed-width map explicitly.  This is the parameterized
    boundary callers can adopt without changing `CrepRuntimeState` itself. -/
def crepRuntimeLoopTypedGlobalRel
    (key : α → CrepGlobalAddress) (source : CrepRuntimeState α σ)
    (target : LoopState α) (typedState : CrepGlobalState α) : Prop :=
  source.locals = target.locals ∧
  source.memory = target.memory ∧
  source.globals = target.globals ∧
  crepRuntimeTypedGlobalRelation key source typedState

theorem crepRuntimeTypedGlobalRelation_adapter
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) :
    crepRuntimeTypedGlobalRelation key
      (state.withTypedGlobalState key typedState) typedState := by
  intro address
  rfl

theorem crepRuntimeLoopTypedGlobalRel_adapter
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) :
    crepRuntimeLoopTypedGlobalRel key
      (state.withTypedGlobalState key typedState)
      (loopStateOfCrepRuntimeStateForGlobals
        (state.withTypedGlobalState key typedState)) typedState := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact crepRuntimeTypedGlobalRelation_adapter state key typedState

/-! The Loop-side state produced by the typed runtime adapter retains the
    source-shaped global relation.  This is the explicit state boundary used
    by typed correctness bridges; the raw Loop store theorems below still
    require a no-alias premise because `updateLoopGlobal` is target-width
    keyed. -/
theorem crepRuntimeTypedGlobalRelation_loopState_adapter
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) :
    CrepGlobalKeyRelation key
      (loopStateOfCrepRuntimeStateForGlobals
        (state.withTypedGlobalState key typedState)).globals
      typedState.globals := by
  intro address
  rfl

/-! When the key re-encoding is injective on the addresses in scope, the
    existing Loop exact-address store is the same update as Cake's typed
    StoreGlob after projection.  This is the explicit premise needed by the
    raw Loop store bridge; aliases must use the typed evaluator adapter above.
    -/
theorem crepRuntimeTypedGlobalRelation_loopStore_of_noalias
    [BEq α] [LawfulBEq α]
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address value : α)
    (hnoalias : ∀ current, key current = key address → current = address) :
    CrepGlobalKeyRelation key
      (updateLoopGlobal
        (state.withTypedGlobalState key typedState).globals address value)
      (storeCrepTypedGlobal key typedState address value).globals := by
  have hcompact :
      CrepGlobalKeyRelation key
        (state.withTypedGlobalState key typedState).globals typedState.globals :=
    crepRuntimeTypedGlobalRelation_adapter state key typedState
  have hstore := CrepGlobalKeyRelation.store key hcompact address value
  have hupdate := updateCrepGlobalKeyedBy_eq_updateMemory_of_noalias
    key (state.withTypedGlobalState key typedState).globals address value hnoalias
  intro current
  calc
    (storeCrepTypedGlobal key typedState address value).globals (key current) =
        updateCrepGlobalKeyedBy key
          (state.withTypedGlobalState key typedState).globals address value current :=
      hstore current
    _ = updateMemory
          (state.withTypedGlobalState key typedState).globals address value current :=
      congrFun hupdate current
    _ = updateLoopGlobal
          (state.withTypedGlobalState key typedState).globals address value current := by
      by_cases h : address = current
      · subst current
        simp [updateMemory, updateLoopGlobal]
      · have h' : current ≠ address := Ne.symm h
        simp [updateMemory, updateLoopGlobal, h, h']

theorem crepRuntimeTypedGlobalRelation_store_of_noalias
    [BEq α] [LawfulBEq α]
    (key : α → CrepGlobalAddress) (state : CrepRuntimeState α σ)
    (typedState : CrepGlobalState α) (address value : α)
    (hrel : crepRuntimeTypedGlobalRelation key state typedState)
    (hnoalias : ∀ current, key current = key address → current = address) :
    crepRuntimeTypedGlobalRelation key
      { state with globals := updateMemory state.globals address value }
      (storeCrepTypedGlobal key typedState address value) := by
  unfold crepRuntimeTypedGlobalRelation at *
  have hstore := CrepGlobalKeyRelation.store key hrel address value
  have hupdate := updateCrepGlobalKeyedBy_eq_updateMemory_of_noalias
    key state.globals address value hnoalias
  simpa [storeCrepTypedGlobal, hupdate] using hstore

theorem crepRuntimeLoopTypedGlobalRel_store_of_noalias
    [BEq α] [LawfulBEq α]
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address value : α)
    (hnoalias : ∀ current, key current = key address → current = address) :
    crepRuntimeLoopTypedGlobalRel key
      { (state.withTypedGlobalState key typedState) with
        globals := updateMemory
          (state.withTypedGlobalState key typedState).globals address value }
      { (loopStateOfCrepRuntimeStateForGlobals
          (state.withTypedGlobalState key typedState)) with
        globals := updateLoopGlobal
          (state.withTypedGlobalState key typedState).globals address value }
      (storeCrepTypedGlobal key typedState address value) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · funext current
    by_cases h : address = current
    · subst current
      simp [updateMemory, updateLoopGlobal]
    · have h' : current ≠ address := Ne.symm h
      simp [updateMemory, updateLoopGlobal, h, h']
  · exact crepRuntimeTypedGlobalRelation_store_of_noalias key
      (state.withTypedGlobalState key typedState) typedState address value
      (crepRuntimeTypedGlobalRelation_adapter state key typedState) hnoalias

def storeCrepRuntimeTypedGlobalState [BEq α]
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address value : α) : CrepRuntimeState α σ :=
  state.withTypedGlobalState key
    (storeCrepTypedGlobal key typedState address value)

theorem loopStateWithTypedGlobalStore_runtime_adapter [BEq α]
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address value : α) :
    loopStateWithTypedGlobalStore
        (loopStateOfCrepRuntimeStateForGlobals state) key typedState address value =
      loopStateOfCrepRuntimeStateForGlobals
        (storeCrepRuntimeTypedGlobalState state key typedState address value) := by
  rfl

theorem crepRuntimeTypedGlobalRelation_store_adapter
    [BEq α]
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address value : α) :
    crepRuntimeTypedGlobalRelation key
      (storeCrepRuntimeTypedGlobalState state key typedState address value)
      (storeCrepTypedGlobal key typedState address value) := by
  exact crepRuntimeTypedGlobalRelation_adapter _ _ _

theorem evalCrepRuntimeExp_loadGlob_typedState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address : α) :
    evalCrepRuntimeExp (state.withTypedGlobalState key typedState)
        (.loadGlob address) =
      evalCrepTypedLoad key typedState address := by
  simp [CrepRuntimeState.withTypedGlobalState, evalCrepRuntimeExp,
    evalCrepTypedLoad, CrepGlobalState.toCompact]

theorem evalCrepRuntimeExp_loadGlob_after_store_typedState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address value loadAddress : α) :
    evalCrepRuntimeExp
        (storeCrepRuntimeTypedGlobalState state key typedState address value)
        (.loadGlob loadAddress) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key typedState address value) loadAddress := by
  simpa [storeCrepRuntimeTypedGlobalState] using
    (evalCrepRuntimeExp_loadGlob_typedState state key
      (storeCrepTypedGlobal key typedState address value) loadAddress)

/-! A raw-runtime wrapper carrying Cake's typed global map.

`CrepRuntimeState` remains the executable compatibility state, but its
`globals` field is target-width keyed.  This wrapper is the explicit raw
boundary for correctness statements: all runtime fields stay in the existing
state, while the source global map is carried at `CrepGlobalAddress` and is
projected only when the runtime evaluator is invoked. -/
structure CrepRuntimeTypedState (α σ : Type u) where
  runtime : CrepRuntimeState α σ
  globals : CrepGlobalAddress → Option α

namespace CrepRuntimeTypedState

def toGlobalState (state : CrepRuntimeTypedState α σ) : CrepGlobalState α :=
  { locals := state.runtime.locals
    memory := state.runtime.memory
    globals := state.globals }

def toRuntime (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) : CrepRuntimeState α σ :=
  state.runtime.withTypedGlobalState key state.toGlobalState

def store [BEq α] (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (address value : α) :
    CrepRuntimeTypedState α σ :=
  { state with globals := storeCrepGlobal state.globals (key address) value }

/-! Target-word expression evaluation for the typed runtime boundary.  The
    legacy `evalCrepRuntimeExp` remains available for compatibility, but a
    RISC-V caller carrying Cake's typed global map must use the complete
    `word_sh` semantics (including ASR/ROR and width checks).  This adapter
    keeps runtime locals/memory while routing globals through the fixed-width
    `CrepGlobalAddress` map. -/
def evalExpFull
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [PanShiftWidth α] [ArithmeticShiftRight α]
    [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (baseAddress topAddress : α) :
    CrepExp α → Option α :=
  evalCrepTypedExpFull key state.toGlobalState baseAddress topAddress

/-! Typed runtime `StoreGlob` boundary.  This adapter evaluates the value and
    updates Cake's fixed-width global map before projecting back to the legacy
    runtime shape; existing raw runtime callers remain unchanged. -/
def storeGlob
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [PanShiftWidth α] [ArithmeticShiftRight α]
    [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (baseAddress topAddress : α)
    (address : α) (expression : CrepExp α) :
    Option (CrepRuntimeTypedState α σ) := do
  let value ← state.evalExpFull key baseAddress topAddress expression
  pure (state.store key address value)

/-! Checked target-word evaluation for the same typed runtime boundary.  The
    memory state is supplied explicitly because the legacy runtime record is
    intentionally retained for compatibility; ordinary loads therefore use
    Cake's domain/alignment/endianness model instead of its raw memory field. -/
def evalExpCheckedFull
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [PanShiftWidth α] [ArithmeticShiftRight α]
    [RotateRightOp α] [OfNat α 2] [OfNat α 3] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (memoryState : CrepMemoryState α)
    (baseAddress topAddress : α) : CrepExp α → Option α :=
  evalCrepCheckedExpStateFull state.runtime.locals
    (fun address => state.globals (key address)) memoryState
    baseAddress topAddress

theorem toRuntime_relation (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) :
    crepRuntimeTypedGlobalRelation key (state.toRuntime key)
      state.toGlobalState := by
  exact crepRuntimeTypedGlobalRelation_adapter state.runtime key state.toGlobalState

theorem load_toRuntime [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (address : α) :
    evalCrepRuntimeExp (state.toRuntime key) (.loadGlob address) =
      evalCrepTypedLoad key state.toGlobalState address := by
  simpa [CrepRuntimeTypedState.toRuntime] using
    (evalCrepRuntimeExp_loadGlob_typedState state.runtime key
      state.toGlobalState address)

theorem store_toRuntime [BEq α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (address value : α) :
    (state.store key address value).toRuntime key =
      storeCrepRuntimeTypedGlobalState state.runtime key state.toGlobalState
        address value := by
  rfl

theorem storeGlob_load_alias
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [PanShiftWidth α] [ArithmeticShiftRight α]
    [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (baseAddress topAddress : α)
    (address value loadAddress : α) :
    (state.storeGlob key baseAddress topAddress address (.const value)).bind
        (fun next => next.evalExpFull key baseAddress topAddress
          (.loadGlob loadAddress)) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.toGlobalState address value) loadAddress := by
  simp [storeGlob, evalExpFull, store, evalCrepTypedExpFull,
    CrepRuntimeTypedState.toGlobalState, CrepGlobalState.toCompact,
    evalCrepFullExpStateFull, evalCrepTypedLoad, storeCrepTypedGlobal,
    storeCrepGlobal]

/-! The same StoreGlob/LoadGlob boundary for an arbitrary value expression.
    The premise is exactly the source evaluator result; no extra assumption is
    made about the expression's shape or about the target-width address key. -/
theorem storeGlob_load_alias_of_eval
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [PanShiftWidth α] [ArithmeticShiftRight α]
    [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (baseAddress topAddress : α)
    (address : α) (expression : CrepExp α) (value loadAddress : α)
    (heval : state.evalExpFull key baseAddress topAddress expression = some value) :
    (state.storeGlob key baseAddress topAddress address expression).bind
        (fun next => next.evalExpFull key baseAddress topAddress
          (.loadGlob loadAddress)) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.toGlobalState address value) loadAddress := by
  simp only [storeGlob, heval]
  simp [store, evalExpFull, evalCrepTypedExpFull,
    CrepRuntimeTypedState.toGlobalState, CrepGlobalState.toCompact,
    evalCrepFullExpStateFull, evalCrepTypedLoad, storeCrepTypedGlobal,
    storeCrepGlobal]

theorem load_after_store_toRuntime [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (address value loadAddress : α) :
    evalCrepRuntimeExp
        ((state.store key address value).toRuntime key) (.loadGlob loadAddress) =
    evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.toGlobalState address value) loadAddress := by
  rw [CrepRuntimeTypedState.store_toRuntime]
  exact
    (evalCrepRuntimeExp_loadGlob_after_store_typedState state.runtime key
      state.toGlobalState address value loadAddress)

theorem evalExpFull_load_after_store [BEq α]
    [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [PanShiftWidth α] [ArithmeticShiftRight α]
    [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress)
    (address value loadAddress : α) (baseAddress topAddress : α) :
    (state.store key address value).evalExpFull key baseAddress topAddress
        (.loadGlob loadAddress) =
      evalCrepTypedLoad key
        (storeCrepTypedGlobal key state.toGlobalState address value) loadAddress := by
  simp [evalExpFull, store, evalCrepTypedExpFull,
    CrepRuntimeTypedState.toGlobalState, CrepGlobalState.toCompact,
    evalCrepFullExpStateFull, evalCrepTypedLoad, storeCrepTypedGlobal]

theorem evalExpCheckedFull_loadGlob [BEq α]
    [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [PanShiftWidth α] [ArithmeticShiftRight α]
    [RotateRightOp α] [OfNat α 2] [OfNat α 3] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeTypedState α σ)
    (key : α → CrepGlobalAddress) (memoryState : CrepMemoryState α)
    (address baseAddress topAddress : α) :
    state.evalExpCheckedFull key memoryState baseAddress topAddress
        (.loadGlob address) =
      evalCrepTypedLoad key state.toGlobalState address := by
  simp [evalExpCheckedFull, evalCrepCheckedExpStateFull,
    CrepRuntimeTypedState.toGlobalState, evalCrepTypedLoad]

end CrepRuntimeTypedState

theorem crepRuntimeToLoop_loadGlob_assign_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ) (live : List Nat)
    (name : Nat) (address value : α)
    (hlocal : ∃ oldValue, state.locals name = some oldValue)
    (loop_lookup : lookupNatInfo name context.vars = some name)
    (hglobal : state.globals address = some value) :
    (evalCrepRuntimeResult handler primitive (fuel + 1) state
      (.assign name (.loadGlob address))).map
        (fun result => result.2.locals name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepRuntimeStateForGlobals state)
      (loopCompileProg context live
        (.assign name (.loadGlob address)))).map
    (fun result => (loopResultState result).locals name) := by
  rcases hlocal with ⟨oldValue, hlocal⟩
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
    loopStateOfCrepRuntimeStateForGlobals, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopResultState, updateLoopLocal, updateCrepLocal, hlocal, loop_lookup,
    hglobal]

theorem crepRuntimeToLoop_loadGlob_assign_failure_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ) (live : List Nat)
    (name : Nat) (address : α) :
    (hlocal : ∃ oldValue, state.locals name = some oldValue) →
    (loop_lookup : lookupNatInfo name context.vars = some name) →
    (evalCrepRuntimeResult handler primitive (fuel + 1) state
      (.assign name (.loadGlob address))).bind
        (crepRuntimeLocalProjection name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepRuntimeStateForGlobals state)
      (loopCompileProg context live
        (.assign name (.loadGlob address)))).map
    (fun result => (loopResultState result).locals name) := by
  intro hlocal loop_lookup
  rcases hlocal with ⟨oldValue, hlocal⟩
  cases hglobal : state.globals address with
  | none =>
      simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
        loopStateOfCrepRuntimeStateForGlobals, loopCompileProg, loopCompileExp,
        loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
        loopResultState, crepRuntimeLocalProjection, loop_lookup, hglobal]
  | some value =>
      simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
        loopStateOfCrepRuntimeStateForGlobals, loopCompileProg, loopCompileExp,
        loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
        loopResultState, crepRuntimeLocalProjection, updateCrepLocal,
        updateLoopLocal, loop_lookup, hglobal, hlocal]

theorem crepRuntimeToLoop_storeGlob_loadGlob_sequence_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ)
    (name : Nat) (address value : α)
    (hlocal : ∃ oldValue, state.locals name = some oldValue)
    (loop_lookup : lookupNatInfo name context.vars = some name) :
    (evalCrepRuntimeResult handler primitive (fuel + 2) state
      (.seq (.storeGlob address (.const value))
        (.assign name (.loadGlob address)))).map
        (fun result => result.2.globals address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 3)
      (loopStateOfCrepRuntimeStateForGlobals state)
      (loopCompileProg context []
        (.seq (.storeGlob address (.const value))
          (.assign name (.loadGlob address))))).map
    (fun result => (loopResultState result).globals address) := by
  rcases hlocal with ⟨oldValue, hlocal⟩
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
    loopStateOfCrepRuntimeStateForGlobals, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopResultState, updateLoopGlobal, updateMemory, fixCrepRuntimeClock,
    hlocal, loop_lookup]

theorem crepRuntimeToLoop_storeGlob_state_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ) (live : List Nat)
    (address value : α) :
    ∃ sourceTarget loopTarget,
      evalCrepRuntimeResult handler primitive (fuel + 1) state
        (.storeGlob address (.const value)) =
        some (.normal, sourceTarget) ∧
      evalLoopProgWithCallsAndFfi functions
        (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
        (loopStateOfCrepRuntimeStateForGlobals state)
        (loopCompileProg context live
          (.storeGlob address (.const value))) =
        some (.normal loopTarget) ∧
      crepRuntimeLoopStateRel sourceTarget loopTarget := by
  let sourceTarget : CrepRuntimeState α σ :=
    { state with globals := updateMemory state.globals address value }
  let loopTarget : LoopState α :=
    { loopStateOfCrepRuntimeStateForGlobals state with
      globals := updateLoopGlobal state.globals address value }
  have hglobals : updateMemory state.globals address value =
      updateLoopGlobal state.globals address value := by
    funext current
    by_cases h : address = current
    · subst current
      simp [updateMemory, updateLoopGlobal]
    · have h' : current ≠ address := Ne.symm h
      simp [updateMemory, updateLoopGlobal, h, h']
  refine ⟨sourceTarget, loopTarget, ?_, ?_, ?_⟩
  · simp [sourceTarget, evalCrepRuntimeResult, evalCrepRuntimeProg,
      evalCrepRuntimeExp]
  · simp [loopTarget, loopStateOfCrepRuntimeStateForGlobals,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
      loopCompileProg, loopCompileExp, loopNestedSeq]
  · simp [crepRuntimeLoopStateRel, sourceTarget, loopTarget,
      loopStateOfCrepRuntimeStateForGlobals, hglobals]

/-! The typed production wrappers use the source's fixed 5-bit global key at
    the runtime-to-loop bridge.  The compact evaluator is still the execution
    engine, but it is reached only through `CrepGlobalState.toCompact`; this
    prevents these correctness statements from silently treating a target
    word as a source global address. -/

theorem crepRuntimeToLoop_loadGlob_assign_agreement_typed
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ)
    (key : α → CrepGlobalAddress) (typedState : CrepGlobalState α)
    (live : List Nat) (name : Nat) (address value : α)
    (hlocal : ∃ oldValue, state.locals name = some oldValue)
    (loop_lookup : lookupNatInfo name context.vars = some name)
    (hglobal : typedState.globals (key address) = some value) :
    (evalCrepRuntimeResult handler primitive (fuel + 1)
      (state.withTypedGlobalState key typedState)
      (.assign name (.loadGlob address))).map
        (fun result => result.2.locals name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepRuntimeStateForGlobals
        (state.withTypedGlobalState key typedState))
      (loopCompileProg context live
        (.assign name (.loadGlob address)))).map
    (fun result => (loopResultState result).locals name) := by
  apply crepRuntimeToLoop_loadGlob_assign_agreement context functions handler
    primitive fuel (state.withTypedGlobalState key typedState) live name address
    value hlocal loop_lookup
  simpa [CrepRuntimeState.withTypedGlobalState,
    CrepGlobalState.toCompact] using hglobal

theorem crepRuntimeToLoop_loadGlob_assign_failure_agreement_typed
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ)
    (key : α → CrepGlobalAddress) (typedState : CrepGlobalState α)
    (live : List Nat) (name : Nat) (address : α)
    (hlocal : ∃ oldValue, state.locals name = some oldValue)
    (loop_lookup : lookupNatInfo name context.vars = some name) :
    (evalCrepRuntimeResult handler primitive (fuel + 1)
      (state.withTypedGlobalState key typedState)
      (.assign name (.loadGlob address))).bind
        (crepRuntimeLocalProjection name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepRuntimeStateForGlobals
        (state.withTypedGlobalState key typedState))
      (loopCompileProg context live
        (.assign name (.loadGlob address)))).map
    (fun result => (loopResultState result).locals name) := by
  exact crepRuntimeToLoop_loadGlob_assign_failure_agreement context functions
    handler primitive fuel (state.withTypedGlobalState key typedState) live name
    address hlocal loop_lookup

theorem crepRuntimeToLoop_storeGlob_loadGlob_sequence_agreement_typed
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ)
    (key : α → CrepGlobalAddress) (typedState : CrepGlobalState α)
    (name : Nat) (address value : α)
    (hlocal : ∃ oldValue, state.locals name = some oldValue)
    (loop_lookup : lookupNatInfo name context.vars = some name) :
    (evalCrepRuntimeResult handler primitive (fuel + 2)
      (state.withTypedGlobalState key typedState)
      (.seq (.storeGlob address (.const value))
        (.assign name (.loadGlob address)))).map
        (fun result => result.2.globals address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 3)
      (loopStateOfCrepRuntimeStateForGlobals
        (state.withTypedGlobalState key typedState))
      (loopCompileProg context []
        (.seq (.storeGlob address (.const value))
          (.assign name (.loadGlob address))))).map
    (fun result => (loopResultState result).globals address) := by
  exact crepRuntimeToLoop_storeGlob_loadGlob_sequence_agreement context
    functions handler primitive fuel (state.withTypedGlobalState key typedState)
    name address value hlocal loop_lookup

theorem crepRuntimeToLoop_storeGlob_state_agreement_typed
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ)
    (key : α → CrepGlobalAddress) (typedState : CrepGlobalState α)
    (live : List Nat) (address value : α) :
    ∃ sourceTarget loopTarget,
      evalCrepRuntimeResult handler primitive (fuel + 1)
        (state.withTypedGlobalState key typedState)
        (.storeGlob address (.const value)) =
        some (.normal, sourceTarget) ∧
      evalLoopProgWithCallsAndFfi functions
        (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
        (loopStateOfCrepRuntimeStateForGlobals
          (state.withTypedGlobalState key typedState))
        (loopCompileProg context live
          (.storeGlob address (.const value))) =
        some (.normal loopTarget) ∧
      crepRuntimeLoopStateRel sourceTarget loopTarget := by
  exact crepRuntimeToLoop_storeGlob_state_agreement context functions handler
    primitive fuel (state.withTypedGlobalState key typedState) live address value

end Flapjack
