import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Proofs.CrepArith

/-!
# Crep arithmetic proof-script state updates

The `mapc` overload and its `FLOOKUP_mapc` equation are local to
`crep_arithProofScript.sml:109`. They live under the `CrepArith` counterpart,
while the carrier itself remains in `Semantics.CrepSem.HOLState`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Flapjack-only record extensionality for the evaluator-state carrier. -/
private theorem crepHolState_eq_of_fields {α σ : Type}
    {left right : CrepHolState α σ}
    (hLocals : left.locals = right.locals)
    (hGlobals : left.globals = right.globals)
    (hCode : left.code = right.code)
    (hMemory : left.memory = right.memory)
    (hMemaddrs : left.memaddrs = right.memaddrs)
    (hShMemaddrs : left.shMemaddrs = right.shMemaddrs)
    (hClock : left.clock = right.clock)
    (hBigEndian : left.bigEndian = right.bigEndian)
    (hFfi : left.ffi = right.ffi)
    (hBaseAddress : left.baseAddress = right.baseAddress)
    (hTopAddress : left.topAddress = right.topAddress) :
    left = right := by
  cases left
  cases right
  simp_all

/-- HOL's local `mapc f` state update, using `FMAP_MAP2` on the code map. -/
def CrepSemHOLState.mapc {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  { state with code := state.code.map2 f }

@[simp] theorem CrepSemHOLState.FLOOKUP_mapc {width : Nat} [NeZero width]
    {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (name : MlString) :
    (state.mapc f).code.lookup name =
      (state.code.lookup name).map (fun entry => f (name, entry)) := rfl

@[simp] theorem CrepSemHOLState.toExpressionEvaluatorState_mapc
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) :
    (state.mapc f).toExpressionEvaluatorState =
      state.toExpressionEvaluatorState := by
  rfl

@[simp] theorem CrepSemHOLState.toBitVecEvaluatorState_mapc
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) :
    (state.mapc f).toBitVecEvaluatorState = state.toBitVecEvaluatorState := rfl

/-- HOL's proof-script-local `mapc` update on an arbitrary-index finite state.
This only uses the finite-map `FMAP_MAP2` encoding; it makes no claim about
the code-entry representation. -/
def CrepSemHOLFiniteState.mapc {ι β σ : Type}
    (f : MlString × β → β) (state : CrepSemHOLFiniteState ι β σ) :
    CrepSemHOLFiniteState ι β σ :=
  { state with code := state.code.map2 f }

@[simp] theorem CrepSemHOLFiniteState.toSourceEvaluatorState_mapc
    {ι β σ : Type} (f : MlString × β → β)
    (state : CrepSemHOLFiniteState ι β σ) :
    (state.mapc f).toSourceEvaluatorState = state.toSourceEvaluatorState := rfl

/-- Changing only the HOL code map cannot alter expression evaluation after
projection into the source evaluator. This is Flapjack support for the
`simp_exp_correct1` dependency; the evaluator correspondence to native HOL
remains unproved. -/
theorem evalCrepHolFiniteWordSourceExp_mapc_projection
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        (state.mapc f).toExpressionEvaluatorState expression =
      evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        state.toExpressionEvaluatorState expression := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]

/-- The `memory` field in the all-width expression projection agrees with the
direct BitVec projection after the canonical finite-index conversion. This
representation equation is Flapjack support; it does not identify HOL's
arbitrary `finite_index` type with `Fin width`. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memory
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).memory =
    state.toBitVecEvaluatorState.memory := by
  funext address
  have hAddress : holWordBitsToBitVec
      (bitVecToHolWord (instFinHolFiniteDimension (width := width)) address) =
      address := by
    change holWordBitsToBitVec
      (holWordToFinBits (instFinHolFiniteDimension (width := width))
        (finBitsToHolWord (instFinHolFiniteDimension (width := width))
          (bitVecToHolWordBits address))) = address
    rw [holWordToFinBits_finBitsToHolWord]
    exact holWordBitsToBitVec_bitVecToHolWordBits address
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  rw [hAddress]
  cases hCell : state.memory address with
  | word value =>
      simp [CrepSemHOLState.toBitVecEvaluatorState,
        mapCrepHolWordLab, holWordLabToBits_word,
        instFinHolFiniteDimension, hCell]
      change holWordToBitVec
        (instFinHolFiniteDimension (width := width))
        (bitVecToHolWordBits value) = value
      change holWordBitsToBitVec (bitVecToHolWordBits value) = value
      exact holWordBitsToBitVec_bitVecToHolWordBits value

/-- The address-domain field in the expression projection agrees with the
direct BitVec projection after the canonical finite-index conversion. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memaddrs
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).memaddrs =
    state.toBitVecEvaluatorState.memaddrs := by
  funext address
  have hAddress : holWordBitsToBitVec
      (bitVecToHolWord (instFinHolFiniteDimension (width := width)) address) =
      address := by
    change holWordBitsToBitVec
      (holWordToFinBits (instFinHolFiniteDimension (width := width))
        (finBitsToHolWord (instFinHolFiniteDimension (width := width))
          (bitVecToHolWordBits address))) = address
    rw [holWordToFinBits_finBitsToHolWord]
    exact holWordBitsToBitVec_bitVecToHolWordBits address
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  rw [hAddress]
  rfl

/-- Finite-map locals survive the expression projection and canonical
finite-index transport unchanged in the direct BitVec view. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_locals
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).locals =
    state.toBitVecEvaluatorState.locals := by
  funext name
  cases hLocal : state.locals.lookup name with
  | none =>
      simp [CrepSemHOLState.toExpressionEvaluatorState,
        CrepSemHOLState.toBitVecEvaluatorState,
        CrepHolState.toHolFiniteBitVecState, hLocal]
  | some cell =>
      cases cell with
      | word value =>
          dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
            CrepSemHOLState.toBitVecEvaluatorState,
            CrepHolState.toHolFiniteBitVecState]
          rw [hLocal]
          simp only [Option.map_some, holWordLabToBits_word, mapCrepHolWordLab,
            HolWordLab.toPanWordLab]
          apply congrArg some
          change PanWordLab.word
            (holWordToBitVec (instFinHolFiniteDimension (width := width))
              (bitVecToHolWordBits value)) = PanWordLab.word value
          congr 1
          change holWordToBitVec
            (instFinHolFiniteDimension (width := width))
            (bitVecToHolWordBits value) = value
          change holWordBitsToBitVec (bitVecToHolWordBits value) = value
          exact holWordBitsToBitVec_bitVecToHolWordBits value

/-- Finite-map globals survive the expression projection and canonical
finite-index transport unchanged in the direct BitVec view. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_globals
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).globals =
    state.toBitVecEvaluatorState.globals := by
  funext name
  cases hGlobal : state.globals.lookup name with
  | none =>
      simp [CrepSemHOLState.toExpressionEvaluatorState,
        CrepSemHOLState.toBitVecEvaluatorState,
        CrepHolState.toHolFiniteBitVecState, hGlobal]
  | some cell =>
      cases cell with
      | word value =>
          dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
            CrepSemHOLState.toBitVecEvaluatorState,
            CrepHolState.toHolFiniteBitVecState]
          rw [hGlobal]
          simp only [Option.map_some, holWordLabToBits_word, mapCrepHolWordLab,
            HolWordLab.toPanWordLab]
          apply congrArg some
          change PanWordLab.word
            (holWordToBitVec (instFinHolFiniteDimension (width := width))
              (bitVecToHolWordBits value)) = PanWordLab.word value
          congr 1
          change holWordToBitVec
            (instFinHolFiniteDimension (width := width))
            (bitVecToHolWordBits value) = value
          change holWordBitsToBitVec (bitVecToHolWordBits value) = value
          exact holWordBitsToBitVec_bitVecToHolWordBits value

/-- The shared-memory domain field also survives the expression projection
and canonical finite-index transport. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_shMemaddrs
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).shMemaddrs =
    state.toBitVecEvaluatorState.shMemaddrs := by
  funext address
  have hAddress : holWordBitsToBitVec
      (bitVecToHolWord (instFinHolFiniteDimension (width := width)) address) =
      address := by
    change holWordBitsToBitVec
      (holWordToFinBits (instFinHolFiniteDimension (width := width))
        (finBitsToHolWord (instFinHolFiniteDimension (width := width))
          (bitVecToHolWordBits address))) = address
    rw [holWordToFinBits_finBitsToHolWord]
    exact holWordBitsToBitVec_bitVecToHolWordBits address
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  rw [hAddress]
  rfl

/-- The base-address word in the canonical finite-index conversion agrees
with the direct BitVec view. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_baseAddress
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).baseAddress =
    state.toBitVecEvaluatorState.baseAddress := by
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepSemHOLState.toBitVecEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  change holWordToBitVec (instFinHolFiniteDimension (width := width))
    (bitVecToHolWordBits state.baseAddr) = state.baseAddr
  change holWordBitsToBitVec (bitVecToHolWordBits state.baseAddr) = state.baseAddr
  exact holWordBitsToBitVec_bitVecToHolWordBits state.baseAddr

/-- The top-address word in the canonical finite-index conversion agrees
with the direct BitVec view. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_topAddress
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).topAddress =
    state.toBitVecEvaluatorState.topAddress := by
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepSemHOLState.toBitVecEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  change holWordToBitVec (instFinHolFiniteDimension (width := width))
    (bitVecToHolWordBits state.topAddr) = state.topAddr
  change holWordBitsToBitVec (bitVecToHolWordBits state.topAddr) = state.topAddr
  exact holWordBitsToBitVec_bitVecToHolWordBits state.topAddr

/-- The expression projection followed by the canonical finite-index
transport equals the direct BitVec projection of the same exact state. This
is representation support for all-width evaluator proofs; arbitrary HOL
`finite_index` isomorphism remains a separate requirement. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    (state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width)) =
    state.toBitVecEvaluatorState := by
  apply crepHolState_eq_of_fields
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_locals state
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_globals state
  · rfl
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memory state
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memaddrs state
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_shMemaddrs state
  · rfl
  · rfl
  · rfl
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_baseAddress state
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_topAddress state

/-- The canonical `Fin width` finite-word runtime adapter is definitionally
the existing HOL-word-bits runtime adapter on this exact state. -/
theorem CrepSemHOLState.toHolFiniteWordRuntime_instFin_eq_toHolWordBitsRuntime
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepHolState (Fin width → Bool) σ) :
    state.toHolFiniteWordRuntime (instFinHolFiniteDimension (width := width)) =
    state.toHolWordBitsRuntime := by
  rfl

/-- Full all-width evaluator transport from the exact-state expression
projection to production `evalCrepRuntimeExp`, related to the direct BitVec
HOL-state evaluator. This still uses canonical `Fin width`; it does not claim
the arbitrary HOL `finite_index` instance has been reindexed. -/
theorem evalCrepRuntimeExp_exactCrepSemHOLState_projection
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepRuntimeExp
      (state.toExpressionEvaluatorState.toHolWordBitsRuntime) expression =
    (evalCrepHolExp state.toBitVecEvaluatorState
      (mapCrepExpWord
        (holWordToBitVec (instFinHolFiniteDimension (width := width)))
        expression)).map
      (bitVecToHolWord (instFinHolFiniteDimension (width := width))) := by
  rw [← CrepSemHOLState.toHolFiniteWordRuntime_instFin_eq_toHolWordBitsRuntime]
  calc
    _ = evalCrepHolFiniteDimensionExp
          (instFinHolFiniteDimension (width := width))
          state.toExpressionEvaluatorState expression :=
      evalCrepRuntimeExp_finiteDimension_eq
        (dimension := instFinHolFiniteDimension (width := width))
        (state := state.toExpressionEvaluatorState)
        (expression := expression)
    _ = _ := by
      simp [evalCrepHolFiniteDimensionExp,
        CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState]

/-- The all-width finite-word source `Load32` clause over the exact HOL-shaped
state reduces to the tagged HOL `mem_load_32_def` port on its direct BitVec
projection. This isolates the memory cell, domain, and endian fields from the
recursive `eval_def` proof. It remains untagged: the enclosing evaluator still
uses Flapjack's explicit finite-index projection. -/
theorem evalCrepSemHOLStateSource_load32_eq_memLoad32HOL
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (addressExpression : CrepExp (Fin width → Bool))
    (address : Fin width → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState addressExpression = some address) :
    (evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState (.load32 addressExpression)).map
        (holWordToBitVec (instFinHolFiniteDimension (width := width))) =
    (panMemLoad32HOL
        (fun bitAddress =>
          (state.toBitVecEvaluatorState.memory bitAddress).toHolWordLab)
        (fun bitAddress => state.toBitVecEvaluatorState.memaddrs bitAddress = true)
        state.toBitVecEvaluatorState.bigEndian
        (holWordToBitVec (instFinHolFiniteDimension (width := width)) address)).map
          (fun value => BitVec.ofNat width value.toNat) := by
  classical
  rw [evalCrepHolFiniteWordSourceExp_load32_eq_panMemLoad32HOL
    (dimension := instFinHolFiniteDimension (width := width))
    (state := state.toExpressionEvaluatorState)
    (addressExpression := addressExpression) (address := address) hAddress]
  rw [CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memory,
    CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memaddrs]
  rfl

/-- All-positive-width `simp_exp_correct1` support over the HOL-shaped Crep
state carrier and the proof-script-local `mapc` update. The statement keeps
the unused word_lab result binder, a successful full word_lab evaluation
premise, the exact code-map update, the `n2w` simplifier image, and the full
optional word_lab equality. It remains untagged because evaluation is through
the explicit finite-width source projection after translating exact
`CrepExpHOL` syntax to the evaluator carrier, rather than native HOL
`crepSem$eval`; this theorem does not establish the finite-index instance or
recursive evaluator correspondence. -/
theorem crepSimpExpCorrect1CrepSemHOLStateSource
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState (crepExpHOLToSourceBits expression) ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (state.mapc update).toExpressionEvaluatorState
      (crepSimpExp
        (fun n => bitVecToHolWord
          (instFinHolFiniteDimension (width := width))
          (BitVec.ofNat
            (HolFiniteDimension.width (Fin width)) n))
        (crepExpHOLToSourceBits expression)) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState (crepExpHOLToSourceBits expression) := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]
  letI : HolFiniteDimension (Fin width) :=
    instFinHolFiniteDimension (width := width)
  have hCodeId :
      crepArithHolFiniteDimensionMapCode
        (fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
        state.toExpressionEvaluatorState = state.toExpressionEvaluatorState := by
    cases state.toExpressionEvaluatorState
    simp [crepArithHolFiniteDimensionMapCode]
  have hSource := crepSimpExpCorrect1HolFiniteWordSourceWordLab
    (dimension := instFinHolFiniteDimension (width := width))
    (f := fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
    state.toExpressionEvaluatorState (crepExpHOLToSourceBits expression)
    (PanWordLab.word (fun _ => false)) h
  rw [hCodeId] at hSource
  exact hSource

/-- All-width `simp_exp_correct1` support over a finite-map state with an
arbitrary finite-index word carrier. The input retains locals, globals, code,
memory, memory domains, clock/endian fields, FFI, and base/top words; its code
update is the actual `FMAP_MAP2`-shaped operation. The unused result binder,
successful full `word_lab` premise, `n2w`-shaped simplifier image, and optional
`word_lab` equality follow HOL's statement shape.

This remains untagged because evaluation is still the explicit-dimension
source projection: the generic code-entry representation and FFI projection
are not identified with HOL's program and FFI carriers, and the recursive
operation clauses have not been proved as a relation to native HOL
`crepSem$eval`. This theorem narrows the state/finite-index gap but does not
close the native evaluator correspondence. -/
theorem crepSimpExpCorrect1CrepSemHOLFiniteStateSource
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (update : MlString × β → β)
    (state : CrepSemHOLFiniteState ι β σ)
    (expression : CrepExp (ι → Bool))
    (_result : PanWordLab (ι → Bool))
    (h : evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState expression ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (state.mapc update).toSourceEvaluatorState
      (crepSimpExp
        (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) expression) =
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState expression := by
  rw [CrepSemHOLFiniteState.toSourceEvaluatorState_mapc]
  let projected := state.toSourceEvaluatorState
  let codeId := fun pair : FunName × (List Nat × CrepProg (ι → Bool)) => pair.2
  have hCodeId : crepArithHolFiniteDimensionMapCode codeId projected = projected := by
    cases projected
    simp [crepArithHolFiniteDimensionMapCode, codeId]
  have hPres := crepSimpExpCorrect1HolFiniteWordSourceWordLab
    (dimension := dimension) (f := codeId) projected expression
    (PanWordLab.word (fun _ => false)) h
  rw [hCodeId] at hPres
  exact hPres

/-- Arbitrary-index finite-state `Load` clause for the source evaluator,
matching the `Load` branch of HOL `crepSem$eval_def`
(`crepSemScript.sml:93-98`) and its `mem_load_def` dependency. It retains the
recursive address evaluation, exact total-memory field, address-domain test,
and complete `Option word_lab` result. It stays untagged because evaluation is
still transported through the explicit `HolFiniteDimension` source adapter;
the complete native HOL evaluator/state relation remains open. -/
theorem evalCrepHolFiniteStateSource_load
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState addressExpression = some address) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.load addressExpression) =
    if state.toSourceEvaluatorState.memaddrs address then
      some (state.memory address) else none := by
  let projected := state.toSourceEvaluatorState
  change (evalCrepHolFiniteWordSourceExp dimension projected
      (.load addressExpression)).map PanWordLab.word =
    if projected.memaddrs address then some (state.memory address) else none
  rw [evalCrepHolFiniteWordSourceExp, hAddress]
  simp [panTheWord, projected,
    CrepSemHOLFiniteState.toSourceEvaluatorState]
  cases hMemory : state.memory address with
  | word value =>
      by_cases hDomain : decide (state.memaddrs address) = true <;>
        simp [hDomain]

/-- Production-runtime all-positive-width `simp_exp_correct1` support over the
HOL-shaped state carrier and exact HOL expression syntax. The evaluator in
the premise and conclusion is `evalCrepRuntimeExp`; the source state is
projected to its expression-observable fields and then represented by the
canonical `Fin width` word model. This remains untagged because that
projection fixes code/FFI observations and does not establish the native HOL
state/evaluator or arbitrary `finite_index` correspondence. -/
theorem crepSimpExpCorrect1CrepSemHOLStateRuntime
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : (evalCrepRuntimeExp
      state.toExpressionEvaluatorState.toHolWordBitsRuntime
      (crepExpHOLToSourceBits expression)).map PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp
      (state.mapc update).toExpressionEvaluatorState.toHolWordBitsRuntime
      (crepSimpExp
        (fun n => bitVecToHolWordBits (BitVec.ofNat width n))
        (crepExpHOLToSourceBits expression))).map PanWordLab.word =
    (evalCrepRuntimeExp
      state.toExpressionEvaluatorState.toHolWordBitsRuntime
      (crepExpHOLToSourceBits expression)).map PanWordLab.word := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]
  let projected := state.toExpressionEvaluatorState
  have hCodeId :
      crepArithHolWordBitsMapCode
        (fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
        projected = projected := by
    cases projected
    simp [crepArithHolWordBitsMapCode]
  have hPres := crepSimpExpCorrect1HolWordBits
    (f := fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
    projected (crepExpHOLToSourceBits expression) h
  rw [hCodeId] at hPres
  exact hPres

/-- Direct BitVec production-runtime support for all-positive-width
`crepSemHOLState`. It takes HOL's exact `CrepExpHOL` input and `HolWordLab`
result carrier, and applies the actual HOL-shaped `mapc` update. The evaluator
uses the production RISC-V runtime on a direct word-cell projection, so no
`Fin width → Bool` conversion occurs here. It remains untagged: code/FFI are
fixed in the expression-only projection, and the generic HOL
finite-index/eval_def relation is not established. -/
theorem crepSimpExpCorrect1CrepSemHOLStateBitVecRuntime
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : ((evalCrepRuntimeExp
      (riscvCrepWordTarget state.toBitVecEvaluatorState.toRuntime)
      (crepExpOfHOL expression)).map PanWordLab.word).map
        PanWordLab.toHolWordLab ≠ none) :
    ((evalCrepRuntimeExp
      (riscvCrepWordTarget
        (state.mapc update).toBitVecEvaluatorState.toRuntime)
      (crepSimpExp (BitVec.ofNat width) (crepExpOfHOL expression))).map
        PanWordLab.word).map PanWordLab.toHolWordLab =
    ((evalCrepRuntimeExp
      (riscvCrepWordTarget state.toBitVecEvaluatorState.toRuntime)
      (crepExpOfHOL expression)).map PanWordLab.word).map
        PanWordLab.toHolWordLab := by
  rw [CrepSemHOLState.toBitVecEvaluatorState_mapc]
  let projected := state.toBitVecEvaluatorState
  let productionExpression := crepExpOfHOL expression
  have hRuntime :
      (evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
        productionExpression).map PanWordLab.word ≠ none := by
    have hWrapped := h
    change ((evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
      productionExpression).map PanWordLab.word).map PanWordLab.toHolWordLab ≠ none
      at hWrapped
    intro hnone
    rw [hnone] at hWrapped
    simp at hWrapped
  have hSource :
      evalCrepHolExpWordLab projected productionExpression ≠ none := by
    rw [evalCrepHolExpWordLab, ← evalCrepRuntimeExp_toRuntime_eq]
    exact hRuntime
  have hCodeId :
      crepArithHolMapCode
        (fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
        projected = projected := by
    cases projected
    simp [crepArithHolMapCode]
  have hPres := crepSimpExpCorrect1BitVec
    (f := fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
    projected productionExpression hSource
  rw [hCodeId] at hPres
  have hRuntimePreserved :
      (evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
        (crepSimpExp (BitVec.ofNat width) productionExpression)).map
          PanWordLab.word =
      (evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
        productionExpression).map PanWordLab.word := by
    calc
      _ = evalCrepHolExpWordLab projected
            (crepSimpExp (BitVec.ofNat width) productionExpression) := by
              simp only [evalCrepHolExpWordLab]
              rw [evalCrepRuntimeExp_toRuntime_eq]
      _ = evalCrepHolExpWordLab projected productionExpression := hPres
      _ = _ := by
            simp only [evalCrepHolExpWordLab]
            rw [evalCrepRuntimeExp_toRuntime_eq]
  exact congrArg (Option.map PanWordLab.toHolWordLab) hRuntimePreserved

/-- Native production-evaluator `Var` case against the exact finite-map local
field in `CrepSemHOLState`, corresponding to HOL `crepSem$eval_def`
(`crepSemScript.sml:91`). The production runtime state remains arbitrary,
including its code, FFI, memory model, and byte configuration; the only
premise relates the queried local observation to this state's finite-map
lookup. No state projection or successful-evaluation premise is used, so the
equation covers both a lookup hit and a miss. This stays untagged: the HOL
state uses the positive-width `BitVec` encoding rather than an arbitrary HOL
`finite_index`, and the local observation premise is only one component of the
full state/evaluator correspondence. -/
theorem evalCrepRuntimeExp_crepSemHOLState_var
    {width : Nat} [NeZero width] {σ ρ : Type}
    (holState : CrepSemHOLState width σ)
    (runtimeState : CrepRuntimeState (RiscV.Word width) ρ)
    (name : Nat)
    (hLocal : runtimeState.locals name =
      (holState.locals.lookup name).map HolWordLab.toPanWordLab) :
    ((evalCrepRuntimeExp runtimeState (.var name)).map PanWordLab.word).map
      PanWordLab.toHolWordLab = holState.locals.lookup name := by
  simp only [evalCrepRuntimeExp]
  rw [hLocal]
  cases h : holState.locals.lookup name with
  | none => simp
  | some cell => cases cell <;> simp [HolWordLab.toPanWordLab,
      PanWordLab.toHolWordLab, panTheWord]

/-- Native production-evaluator `LoadGlob` case against the exact finite-map
global field in `CrepSemHOLState`, corresponding to HOL
`crepSem$eval_def` (`crepSemScript.sml:111`). The production runtime state
remains arbitrary, including its code, FFI, memory model, and byte
configuration; the only premise relates the queried global observation to
this state's finite-map lookup. No state projection or successful-evaluation
premise is used, so the equation covers both a lookup hit and a miss. The
direct HOL rows are `eval_global_hit` and `eval_global_miss` in
`scripts/hol-probes/crep_eval_probe.out`. This stays untagged: the HOL state
uses the positive-width `BitVec` encoding rather than an arbitrary HOL
`finite_index`, and the local observation premise is only one component of the
full state/evaluator correspondence. -/
theorem evalCrepRuntimeExp_crepSemHOLState_loadGlob
    {width : Nat} [NeZero width] {σ ρ : Type}
    (holState : CrepSemHOLState width σ)
    (runtimeState : CrepRuntimeState (RiscV.Word width) ρ)
    (address : BitVec 5)
    (hGlobal : runtimeState.globals address =
      (holState.globals.lookup address).map HolWordLab.toPanWordLab) :
    ((evalCrepRuntimeExp runtimeState (.loadGlob address)).map
      PanWordLab.word).map PanWordLab.toHolWordLab =
        holState.globals.lookup address := by
  simp only [evalCrepRuntimeExp]
  rw [hGlobal]
  cases h : holState.globals.lookup address with
  | none => simp
  | some cell => cases cell <;> simp [HolWordLab.toPanWordLab,
      PanWordLab.toHolWordLab, panTheWord]

/-- Exact finite-map `Var` case for the production evaluator instantiated at
the direct BitVec projection of one `CrepSemHOLState`. This is the positive
width Lean carrier's `eval_def` case; it remains untagged because the state
word is represented by BitVec rather than HOL's arbitrary `finite_index`. -/
theorem evalCrepRuntimeExp_toBitVecEvaluatorState_var
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (name : Nat) :
    ((evalCrepRuntimeExp (state.toBitVecEvaluatorState.toRuntime)
      (.var name)).map PanWordLab.word).map PanWordLab.toHolWordLab =
      state.locals.lookup name := by
  apply evalCrepRuntimeExp_crepSemHOLState_var
  change state.toBitVecEvaluatorState.locals name = _
  rfl

/-- Exact finite-map `LoadGlob` case for the production evaluator at the
direct BitVec projection of one `CrepSemHOLState`; kept untagged for the same
arbitrary-`finite_index` reason as the `Var` case. -/
theorem evalCrepRuntimeExp_toBitVecEvaluatorState_loadGlob
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (address : BitVec 5) :
    ((evalCrepRuntimeExp (state.toBitVecEvaluatorState.toRuntime)
      (.loadGlob address)).map PanWordLab.word).map PanWordLab.toHolWordLab =
      state.globals.lookup address := by
  apply evalCrepRuntimeExp_crepSemHOLState_loadGlob
  change state.toBitVecEvaluatorState.globals address = _
  rfl

end Flapjack
