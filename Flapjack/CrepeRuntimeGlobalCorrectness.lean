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

def storeCrepRuntimeTypedGlobalState [BEq α]
    (state : CrepRuntimeState α σ) (key : α → CrepGlobalAddress)
    (typedState : CrepGlobalState α) (address value : α) : CrepRuntimeState α σ :=
  state.withTypedGlobalState key
    (storeCrepTypedGlobal key typedState address value)

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
    loopResultState, updateLoopLocal, updateCrepLocal, hlocal, hglobal]

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
    (evalCrepRuntimeResult handler primitive (fuel + 1) state
      (.assign name (.loadGlob address))).bind
        (crepRuntimeLocalProjection name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepRuntimeStateForGlobals state)
      (loopCompileProg context live
        (.assign name (.loadGlob address)))).map
    (fun result => (loopResultState result).locals name) := by
  intro hlocal
  rcases hlocal with ⟨oldValue, hlocal⟩
  cases hglobal : state.globals address with
  | none =>
      simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
        loopStateOfCrepRuntimeStateForGlobals, loopCompileProg, loopCompileExp,
        loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
        loopResultState, crepRuntimeLocalProjection, hglobal]
  | some value =>
      simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
        loopStateOfCrepRuntimeStateForGlobals, loopCompileProg, loopCompileExp,
        loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
        loopResultState, crepRuntimeLocalProjection, updateCrepLocal,
        updateLoopLocal, hglobal, hlocal]

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
    (hlocal : ∃ oldValue, state.locals name = some oldValue) :
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
    hlocal]

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

end Flapjack
