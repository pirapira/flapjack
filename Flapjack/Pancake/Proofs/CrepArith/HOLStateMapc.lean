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

/-- All-dimension `Var` constructor correspondence from the explicit
finite-index source evaluator to the exact BitVec state evaluator. This uses
the state's actual local lookup and transports the complete `Option word`
result; it introduces no successful-evaluation premise. It is Flapjack
evaluator support, not a standalone HOL declaration: the selected
`HolFiniteDimension` remains a representation witness. -/
theorem evalCrepHolFiniteWordSourceExp_var_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (name : Nat) :
    ((evalCrepHolFiniteWordSourceExp dimension state (.var name)).map
        PanWordLab.word).map (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension) (.var name) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  cases hLocal : state.locals name with
  | none => simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
      evalCrepHolExp, CrepHolState.toHolFiniteBitVecState, hLocal]
  | some cell => cases cell with
      | word value => simp [evalCrepHolFiniteWordSourceExp,
          evalCrepHolExpWordLab, evalCrepHolExp,
          CrepHolState.toHolFiniteBitVecState, hLocal, mapCrepHolWordLab,
          panTheWord]

/-- List evaluation preserves the pointwise finite-word/BitVec evaluator
relation. This is the recursion needed by the HOL `Op` clause's `OPT_MMAP`;
it retains both list failure and successful result order. -/
theorem evalCrepHolFiniteWordSourceExps_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expressions : List (CrepExp (ι → Bool)))
    (hEach : ∀ expression, expression ∈ expressions →
      (evalCrepHolFiniteWordSourceExp dimension state expression).map
        (holWordToBitVec dimension) =
      evalCrepHolExp (state.toHolFiniteBitVecState dimension)
        (mapCrepExpWord (holWordToBitVec dimension) expression)) :
    ((expressions.mapM (evalCrepHolFiniteWordSourceExp dimension state)).map
      (List.map (holWordToBitVec dimension))) =
    (expressions.map (mapCrepExpWord (holWordToBitVec dimension))).mapM
      (evalCrepHolExp (state.toHolFiniteBitVecState dimension)) := by
  induction expressions with
  | nil => simp
  | cons head tail ih =>
      have hHead := hEach head (by simp)
      have hTail : ∀ expression, expression ∈ tail →
          (evalCrepHolFiniteWordSourceExp dimension state expression).map
            (holWordToBitVec dimension) =
          evalCrepHolExp (state.toHolFiniteBitVecState dimension)
            (mapCrepExpWord (holWordToBitVec dimension) expression) := by
        intro expression hmem
        exact hEach expression (by simp [hmem])
      cases hSource : evalCrepHolFiniteWordSourceExp dimension state head with
      | none =>
          have hNative : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
              (mapCrepExpWord (holWordToBitVec dimension) head) = none := by
            simpa [hSource] using hHead.symm
          simp [List.mapM_cons, hSource, hNative]
      | some value =>
          have hNative : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
              (mapCrepExpWord (holWordToBitVec dimension) head) =
                some (holWordToBitVec dimension value) := by
            simpa [hSource] using hHead.symm
          calc
            _ = Option.map
                  (fun values => holWordToBitVec dimension value ::
                    List.map (holWordToBitVec dimension) values)
                  (tail.mapM (evalCrepHolFiniteWordSourceExp dimension state)) := by
                    cases hSourceTailEval :
                      tail.mapM (evalCrepHolFiniteWordSourceExp dimension state) <;>
                      simp [List.mapM_cons, hSource, hSourceTailEval]
            _ = Option.map
                  (fun values => holWordToBitVec dimension value :: values)
                  (Option.map (List.map (holWordToBitVec dimension))
                    (tail.mapM
                      (evalCrepHolFiniteWordSourceExp dimension state))) := by
                    simp [Option.map_map, Function.comp_def]
            _ = Option.map
                  (fun values => holWordToBitVec dimension value :: values)
                  ((tail.map (mapCrepExpWord (holWordToBitVec dimension))).mapM
                    (evalCrepHolExp
                      (state.toHolFiniteBitVecState dimension))) := by
                    rw [ih hTail]
            _ = _ := by
              cases hTailEval :
                  ((tail.map (mapCrepExpWord (holWordToBitVec dimension))).mapM
                    (evalCrepHolExp
                      (state.toHolFiniteBitVecState dimension))) <;>
                simp [hTailEval, hNative]

/-- All-dimension recursive `Op` constructor correspondence. The sole
recursive hypothesis relates each operand evaluation; the list helper above
preserves `mapM` failure/order and the source clause then routes through the
same tagged HOL `word_op` primitive as the direct evaluator. -/
theorem evalCrepHolFiniteWordSourceExp_op_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : BinOp)
    (expressions : List (CrepExp (ι → Bool)))
    (hChildren : ∀ expression, expression ∈ expressions →
      (evalCrepHolFiniteWordSourceExp dimension state expression).map
        (holWordToBitVec dimension) =
      evalCrepHolExp (state.toHolFiniteBitVecState dimension)
        (mapCrepExpWord (holWordToBitVec dimension) expression)) :
    ((evalCrepHolFiniteWordSourceExp dimension state (.op operator expressions)).map
        PanWordLab.word).map (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension)
        (.op operator (expressions.map (mapCrepExpWord (holWordToBitVec dimension)))) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  have hMapM := evalCrepHolFiniteWordSourceExps_toHolEval
    dimension state expressions hChildren
  cases hSourceValues :
      expressions.mapM (evalCrepHolFiniteWordSourceExp dimension state) with
  | none =>
      have hNativeValues :
          (expressions.map (mapCrepExpWord (holWordToBitVec dimension))).mapM
            (evalCrepHolExp (state.toHolFiniteBitVecState dimension)) = none := by
        simpa [hSourceValues] using hMapM.symm
      simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
        evalCrepHolExp, hSourceValues, hNativeValues]
  | some values =>
      have hNativeValues :
          (expressions.map (mapCrepExpWord (holWordToBitVec dimension))).mapM
            (evalCrepHolExp (state.toHolFiniteBitVecState dimension)) =
              some (values.map (holWordToBitVec dimension)) := by
        simpa [hSourceValues] using hMapM.symm
      calc
        ((evalCrepHolFiniteWordSourceExp dimension state
          (.op operator expressions)).map PanWordLab.word).map
            (mapCrepHolWordLab (holWordToBitVec dimension)) =
          (wordOpHOL operator (values.map (holWordToBitVec dimension))).map
            PanWordLab.word :=
              evalCrepHolFiniteWordSourceExpWordLab_op_eq_wordOpHOL
                dimension state operator expressions values hSourceValues
        _ = evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension)
              (.op operator
                (expressions.map (mapCrepExpWord (holWordToBitVec dimension)))) := by
              simp [evalCrepHolExpWordLab, evalCrepHolExp, hNativeValues]

/-- All-dimension recursive `Cmp` constructor correspondence. The two child
evaluations are related individually; source `word_cmp` then agrees with the
direct evaluator's comparison result. This is Flapjack support, not a claim
about the complete native HOL `eval_def` relation. -/
theorem evalCrepHolFiniteWordSourceExp_cmp_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : Cmp)
    (left right : CrepExp (ι → Bool))
    (hLeft : (evalCrepHolFiniteWordSourceExp dimension state left).map
      (holWordToBitVec dimension) =
        evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) left))
    (hRight : (evalCrepHolFiniteWordSourceExp dimension state right).map
      (holWordToBitVec dimension) =
        evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) right)) :
    ((evalCrepHolFiniteWordSourceExp dimension state
      (.cmp operator left right)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension)
        (.cmp operator (mapCrepExpWord (holWordToBitVec dimension) left)
          (mapCrepExpWord (holWordToBitVec dimension) right)) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  cases hSourceLeft : evalCrepHolFiniteWordSourceExp dimension state left with
  | none =>
      have hNativeLeft : evalCrepHolExp
          (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) left) = none := by
        simpa [hSourceLeft] using hLeft.symm
      simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
        evalCrepHolExp, hSourceLeft, hNativeLeft]
  | some leftValue =>
      have hNativeLeft : evalCrepHolExp
          (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) left) =
            some (holWordToBitVec dimension leftValue) := by
        simpa [hSourceLeft] using hLeft.symm
      cases hSourceRight : evalCrepHolFiniteWordSourceExp dimension state right with
      | none =>
          have hNativeRight : evalCrepHolExp
              (state.toHolFiniteBitVecState dimension)
              (mapCrepExpWord (holWordToBitVec dimension) right) = none := by
            simpa [hSourceRight] using hRight.symm
          simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
            evalCrepHolExp, hSourceLeft, hSourceRight, hNativeLeft,
            hNativeRight]
      | some rightValue =>
          have hNativeRight : evalCrepHolExp
              (state.toHolFiniteBitVecState dimension)
              (mapCrepExpWord (holWordToBitVec dimension) right) =
                some (holWordToBitVec dimension rightValue) := by
            simpa [hSourceRight] using hRight.symm
          calc
            _ = some (PanWordLab.word
                  (Compiler.Encoders.Asm.wordCmpResultHOL operator
                    (holWordToBitVec dimension leftValue)
                    (holWordToBitVec dimension rightValue))) :=
              evalCrepHolFiniteWordSourceExpWordLab_cmp_eq_wordCmpHOL
                dimension state operator left right leftValue rightValue
                hSourceLeft hSourceRight
            _ = _ := by
              simp [evalCrepHolExpWordLab, evalCrepHolExp, hNativeLeft,
                hNativeRight, wordCmpResultHOL_eq_evalPanCmp]

/-- All-dimension recursive `Shift` constructor correspondence, including
out-of-range failure in the complete `Option word_lab` result. Its only
premises are the two recursive child relations. -/
theorem evalCrepHolFiniteWordSourceExp_shift_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : Shift)
    (left right : CrepExp (ι → Bool))
    (hLeft : (evalCrepHolFiniteWordSourceExp dimension state left).map
      (holWordToBitVec dimension) =
        evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) left))
    (hRight : (evalCrepHolFiniteWordSourceExp dimension state right).map
      (holWordToBitVec dimension) =
        evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) right)) :
    ((evalCrepHolFiniteWordSourceExp dimension state
      (.shift operator left right)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension)
        (.shift operator (mapCrepExpWord (holWordToBitVec dimension) left)
          (mapCrepExpWord (holWordToBitVec dimension) right)) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  cases hSourceLeft : evalCrepHolFiniteWordSourceExp dimension state left with
  | none =>
      have hNativeLeft : evalCrepHolExp
          (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) left) = none := by
        simpa [hSourceLeft] using hLeft.symm
      simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
        evalCrepHolExp, hSourceLeft, hNativeLeft]
  | some leftValue =>
      have hNativeLeft : evalCrepHolExp
          (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) left) =
            some (holWordToBitVec dimension leftValue) := by
        simpa [hSourceLeft] using hLeft.symm
      cases hSourceRight : evalCrepHolFiniteWordSourceExp dimension state right with
      | none =>
          have hNativeRight : evalCrepHolExp
              (state.toHolFiniteBitVecState dimension)
              (mapCrepExpWord (holWordToBitVec dimension) right) = none := by
            simpa [hSourceRight] using hRight.symm
          simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
            evalCrepHolExp, hSourceLeft, hSourceRight, hNativeLeft,
            hNativeRight]
      | some rightValue =>
          have hNativeRight : evalCrepHolExp
              (state.toHolFiniteBitVecState dimension)
              (mapCrepExpWord (holWordToBitVec dimension) right) =
                some (holWordToBitVec dimension rightValue) := by
            simpa [hSourceRight] using hRight.symm
          calc
            _ = (wordShiftHOL operator
                  (holWordToBitVec dimension leftValue)
                  (holWordToBitVec dimension rightValue).toNat).map
                    PanWordLab.word :=
              evalCrepHolFiniteWordSourceExpWordLab_shift_eq_wordShiftHOL
                dimension state operator left right leftValue rightValue
                hSourceLeft hSourceRight
            _ = _ := by
              simp [evalCrepHolExpWordLab, evalCrepHolExp, hNativeLeft,
                hNativeRight, wordShiftHOL_eq_evalPanShiftFull]

/-- All-dimension recursive `CrepOp.mul` constructor correspondence. The
source primitive is routed through the tagged `crep_op_def`; the direct
evaluator computes the same wrapped product after the two child relations.
This does not by itself establish the native HOL state/evaluator relation. -/
theorem evalCrepHolFiniteWordSourceExp_crepOpMul_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (left right : CrepExp (ι → Bool))
    (hLeft : (evalCrepHolFiniteWordSourceExp dimension state left).map
      (holWordToBitVec dimension) =
        evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) left))
    (hRight : (evalCrepHolFiniteWordSourceExp dimension state right).map
      (holWordToBitVec dimension) =
        evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) right)) :
    ((evalCrepHolFiniteWordSourceExp dimension state
      (.crepOp .mul [left, right])).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension)
        (.crepOp .mul [mapCrepExpWord (holWordToBitVec dimension) left,
          mapCrepExpWord (holWordToBitVec dimension) right]) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  cases hSourceLeft : evalCrepHolFiniteWordSourceExp dimension state left with
  | none =>
      have hNativeLeft : evalCrepHolExp
          (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) left) = none := by
        simpa [hSourceLeft] using hLeft.symm
      simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
        evalCrepHolExp, hSourceLeft, hNativeLeft]
  | some leftValue =>
      have hNativeLeft : evalCrepHolExp
          (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) left) =
            some (holWordToBitVec dimension leftValue) := by
        simpa [hSourceLeft] using hLeft.symm
      cases hSourceRight : evalCrepHolFiniteWordSourceExp dimension state right with
      | none =>
          have hNativeRight : evalCrepHolExp
              (state.toHolFiniteBitVecState dimension)
              (mapCrepExpWord (holWordToBitVec dimension) right) = none := by
            simpa [hSourceRight] using hRight.symm
          simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
            evalCrepHolExp, hSourceLeft, hSourceRight, hNativeLeft,
            hNativeRight]
      | some rightValue =>
          have hNativeRight : evalCrepHolExp
              (state.toHolFiniteBitVecState dimension)
              (mapCrepExpWord (holWordToBitVec dimension) right) =
                some (holWordToBitVec dimension rightValue) := by
            simpa [hSourceRight] using hRight.symm
          calc
            _ = (crepOpCrepWord (width := dimension.width) .mul
                  [holWordToBitVec dimension leftValue,
                   holWordToBitVec dimension rightValue]).map PanWordLab.word :=
              evalCrepHolFiniteWordSourceExpWordLab_crepOp_eq_crepOpCrepWord
                dimension state left right leftValue rightValue
                hSourceLeft hSourceRight
            _ = _ := by
              simp [crepOpCrepWord, evalCrepHolExpWordLab,
                evalCrepHolExp, hNativeLeft, hNativeRight]

/-- All-dimension `LoadGlob` constructor correspondence to the direct BitVec
state evaluator. This preserves the exact global lookup, including misses,
under the finite-word-to-BitVec representation. It is Flapjack support, not a
standalone HOL theorem: the whole recursive evaluator and selected HOL
`finite_index` instance are not identified here. -/
theorem evalCrepHolFiniteWordSourceExp_loadGlob_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (address : BitVec 5) :
    ((evalCrepHolFiniteWordSourceExp dimension state (.loadGlob address)).map
        PanWordLab.word).map (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension)
        (.loadGlob address) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  cases hGlobal : state.globals address with
  | none => simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
      evalCrepHolExp, CrepHolState.toHolFiniteBitVecState, hGlobal]
  | some cell => cases cell with
      | word value => simp [evalCrepHolFiniteWordSourceExp,
          evalCrepHolExpWordLab, evalCrepHolExp,
          CrepHolState.toHolFiniteBitVecState, hGlobal, mapCrepHolWordLab,
          panTheWord]

/-- All-dimension `BaseAddr` source/BitVec evaluator clause correspondence.
This state-independent leaf is Flapjack support and carries no HOL tag while
the enclosing arbitrary-index evaluator relation remains open. -/
theorem evalCrepHolFiniteWordSourceExp_baseAddr_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    ((evalCrepHolFiniteWordSourceExp dimension state .baseAddr).map
        PanWordLab.word).map (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension) .baseAddr := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
    evalCrepHolExp, CrepHolState.toHolFiniteBitVecState,
    mapCrepHolWordLab]

/-- All-dimension `TopAddr` source/BitVec evaluator clause correspondence.
This state-independent leaf is Flapjack support and carries no HOL tag while
the enclosing arbitrary-index evaluator relation remains open. -/
theorem evalCrepHolFiniteWordSourceExp_topAddr_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    ((evalCrepHolFiniteWordSourceExp dimension state .topAddr).map
        PanWordLab.word).map (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension) .topAddr := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
    evalCrepHolExp, CrepHolState.toHolFiniteBitVecState,
    mapCrepHolWordLab]

/-- All-dimension `Const` constructor correspondence to the direct BitVec
state evaluator, preserving the full `Option word_lab` result. -/
theorem evalCrepHolFiniteWordSourceExp_const_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (value : ι → Bool) :
    ((evalCrepHolFiniteWordSourceExp dimension state (.const value)).map
      PanWordLab.word).map (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension)
        (.const (holWordToBitVec dimension value)) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab,
    evalCrepHolExp, CrepHolState.toHolFiniteBitVecState,
    mapCrepHolWordLab]

/-- Recursive all-dimension `Load` constructor correspondence. The single
premise is the evaluator relation for its address subexpression, as supplied
by induction; after that, both sides consult the same original state memory
and address-domain fields, and preserve the complete `Option word_lab` result.
This is Flapjack support only: it does not assert the arbitrary finite-index
instance or complete native `eval_def` relation. -/
theorem evalCrepHolFiniteWordSourceExp_load_toHolEval
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (addressExpression : CrepExp (ι → Bool))
    (hAddress : (evalCrepHolFiniteWordSourceExp dimension state
      addressExpression).map (holWordToBitVec dimension) =
        evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) addressExpression)) :
    ((evalCrepHolFiniteWordSourceExp dimension state
      (.load addressExpression)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
      evalCrepHolExpWordLab (state.toHolFiniteBitVecState dimension)
        (.load (mapCrepExpWord (holWordToBitVec dimension) addressExpression)) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  cases hEval : evalCrepHolFiniteWordSourceExp dimension state addressExpression with
  | none =>
      have hNative : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) addressExpression) = none := by
        simpa [hEval] using hAddress.symm
      simp only [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab, hEval]
      rw [evalCrepHolExp]
      simp [hNative]
  | some address =>
      have hNative : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) addressExpression) =
            some (holWordToBitVec dimension address) := by
        simpa [hEval] using hAddress.symm
      simp only [evalCrepHolFiniteWordSourceExp, evalCrepHolExpWordLab, hEval]
      rw [evalCrepHolExp]
      rw [hNative]
      simp [CrepHolState.toHolFiniteBitVecState, mapCrepHolWordLab,
        panTheWord, bitVecToHolWord_holWordToBitVec]

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

/-- The ordinary `Load` constructor over an exact finite-support Crep state
reduces to the source HOL `mem_load` observation (`crepSemScript.sml:48-52`)
after the address expression succeeds. The result is transported through the
canonical `Fin width`/BitVec representation and back to `HolWordLab`; both the
memory function and address-domain predicate are those of the exact state.
This remains untagged because the proof uses the explicit finite-index
dictionary and a single evaluator clause, not the full arbitrary-index
`crepSem$eval` correspondence needed by `simp_exp_correct1`. -/
theorem evalCrepSemHOLStateSource_load_eq_memLoad
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (addressExpression : CrepExp (Fin width → Bool))
    (address : Fin width → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState addressExpression = some address) :
    (state.memaddrs
        (holWordToBitVec (instFinHolFiniteDimension (width := width)) address) →
    (((evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState (.load addressExpression)).map
        PanWordLab.word).map
        (mapCrepHolWordLab
          (holWordToBitVec (instFinHolFiniteDimension (width := width))))).map
        PanWordLab.toHolWordLab =
      some (state.memory
        (holWordToBitVec (instFinHolFiniteDimension (width := width)) address))) ∧
    (¬ state.memaddrs
        (holWordToBitVec (instFinHolFiniteDimension (width := width)) address) →
     (((evalCrepHolFiniteWordSourceExp
       (instFinHolFiniteDimension (width := width))
       state.toExpressionEvaluatorState (.load addressExpression)).map
         PanWordLab.word).map
         (mapCrepHolWordLab
           (holWordToBitVec (instFinHolFiniteDimension (width := width))))).map
         PanWordLab.toHolWordLab = none) := by
  classical
  constructor
  · intro hDomain
    rw [evalCrepHolFiniteWordSourceExpWordLab_load_eq_memLoadCrepHolW
      (dimension := instFinHolFiniteDimension (width := width))
      (state := state.toExpressionEvaluatorState)
      (addressExpression := addressExpression) (address := address) hAddress]
    rw [CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState]
    simp [memLoadCrepHolW, CrepSemHOLState.toBitVecEvaluatorState,
      hDomain]
  · intro hDomain
    rw [evalCrepHolFiniteWordSourceExpWordLab_load_eq_memLoadCrepHolW
      (dimension := instFinHolFiniteDimension (width := width))
      (state := state.toExpressionEvaluatorState)
      (addressExpression := addressExpression) (address := address) hAddress]
    rw [CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState]
    simp [memLoadCrepHolW, CrepSemHOLState.toBitVecEvaluatorState,
      hDomain]

/-- The direct `evalCrepHolExp` Load clause over the exact finite-support
Crep state has the native HOL `mem_load` branches (`crepSemScript.sml:91-93,
48-52`): after a successful address evaluation, it returns exactly the stored
`HolWordLab` iff the address belongs to `memaddrs`, and otherwise returns
`NONE`. This is a positive-width BitVec rendering of one source evaluator
clause; arbitrary HOL `finite_index` and the recursive all-constructor
correspondence are still required before any `simp_exp_correct1` tag. -/
theorem evalCrepSemHOLStateHolEval_load_eq_memLoad
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (addressExpression : CrepExpHOL width)
    (address : BitVec width)
    (hAddress : evalCrepHolExp state.toBitVecEvaluatorState
      (crepExpOfHOL addressExpression) = some address) :
    (state.memaddrs address →
      (evalCrepHolExpWordLab state.toBitVecEvaluatorState
        (.load (crepExpOfHOL addressExpression))).map
        PanWordLab.toHolWordLab = some (state.memory address)) ∧
    (¬ state.memaddrs address →
      (evalCrepHolExpWordLab state.toBitVecEvaluatorState
        (.load (crepExpOfHOL addressExpression))).map
        PanWordLab.toHolWordLab = none) := by
  constructor
  · intro hDomain
    simp only [evalCrepHolExpWordLab, evalCrepHolExp,
      Option.bind_eq_bind, hAddress]
    cases hCell : state.memory address <;>
      simp [CrepSemHOLState.toBitVecEvaluatorState, hDomain, hCell,
        HolWordLab.toPanWordLab, PanWordLab.toHolWordLab, panTheWord]
  · intro hDomain
    simp only [evalCrepHolExpWordLab, evalCrepHolExp,
      Option.bind_eq_bind, hAddress]
    simp [CrepSemHOLState.toBitVecEvaluatorState, hDomain,
      HolWordLab.toPanWordLab, panTheWord]

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

/-- Arbitrary-index finite-state `Const` case from HOL
`crepSem$eval_def` (`crepSemScript.sml:91`). The entire word_lab wrapper is
preserved. This remains untagged with the enclosing evaluator because its
word type is interpreted through the explicit finite-dimension adapter. -/
theorem evalCrepHolFiniteStateSource_const
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (value : ι → Bool) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.const value) =
    some (.word value) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp]

/-- Arbitrary-index finite-state `Var` case from HOL
`crepSem$eval_def` (`crepSemScript.sml:92`). It returns the exact finite-map
lookup, including lookup failure, with no success premise. It remains untagged
because the enclosing evaluator still uses an explicit finite-dimension
projection. -/
theorem evalCrepHolFiniteStateSource_var
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (name : Nat) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.var name) =
    state.locals.lookup name := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp,
    CrepSemHOLFiniteState.toSourceEvaluatorState,
    panTheWord, Function.comp_def]

/-- Arbitrary-index finite-state `LoadGlob` case from HOL
`crepSem$eval_def` (`crepSemScript.sml:111`). It returns the exact finite-map
global lookup, including a miss. This stays untagged because the enclosing
evaluator/state still use the explicit finite-dimension projection. -/
theorem evalCrepHolFiniteStateSource_loadGlob
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (address : BitVec 5) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.loadGlob address) =
    state.globals.lookup address := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp,
    CrepSemHOLFiniteState.toSourceEvaluatorState,
    panTheWord, Function.comp_def]

/-- Arbitrary-index finite-state `BaseAddr` case of HOL `eval_def`. The full
`word_lab` value comes directly from the corresponding state field. This
case remains untagged as part of the source evaluator because the explicit
finite-index projection is not yet identified with native HOL `eval`. -/
theorem evalCrepHolFiniteStateSource_baseAddr
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState .baseAddr =
    some (.word state.baseAddr) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp,
    CrepSemHOLFiniteState.toSourceEvaluatorState]

/-- Arbitrary-index finite-state `TopAddr` case of HOL `eval_def`, with the
complete `word_lab` wrapper. The enclosing evaluator is still the explicit
finite-dimension source projection, so the case does not carry a HOL tag. -/
theorem evalCrepHolFiniteStateSource_topAddr
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState .topAddr =
    some (.word state.topAddr) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp,
    CrepSemHOLFiniteState.toSourceEvaluatorState]

/-- Arbitrary-index finite-state `Load32` case of HOL `eval_def`, expressed
through the tagged `mem_load_32_def` port after transporting the exact memory
cells to the canonical `BitVec` view. The recursive address hypothesis is the
case induction hypothesis; memory and domains are read from the finite-state
carrier. This remains untagged because the outer source evaluator and
finite-index state relation are not yet native HOL `eval`. -/
theorem evalCrepHolFiniteStateSource_load32
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState addressExpression = some address) :
    (evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.load32 addressExpression)).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (panMemLoad32HOL
      (fun bitAddress =>
        ((state.toSourceEvaluatorState.toHolFiniteBitVecState dimension).memory
          bitAddress).toHolWordLab)
      (fun bitAddress =>
        (state.toSourceEvaluatorState.toHolFiniteBitVecState dimension).memaddrs
          bitAddress = true)
      state.be (holWordToBitVec dimension address)).map
        (fun value => PanWordLab.word
          (BitVec.ofNat dimension.width value.toNat)) := by
  exact evalCrepHolFiniteWordSourceExpWordLab_load32_eq_panMemLoad32HOL
    dimension state.toSourceEvaluatorState addressExpression address hAddress

/-- Arbitrary-index finite-state `LoadByte` case of HOL `eval_def`, with its
recursive address hypothesis and the complete `word_lab` result transported
to the tagged `mem_load_byte_def` port. The explicit finite-index source
evaluator relation remains open, so this case is not tagged as `eval_def`. -/
theorem evalCrepHolFiniteStateSource_loadByte
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState addressExpression = some address) :
    (evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.loadByte addressExpression)).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (panMemLoadByteHOL
      (fun bitAddress =>
        ((state.toSourceEvaluatorState.toHolFiniteBitVecState dimension).memory
          bitAddress).toHolWordLab)
      (fun bitAddress =>
        (state.toSourceEvaluatorState.toHolFiniteBitVecState dimension).memaddrs
          bitAddress = true)
      state.be (holWordToBitVec dimension address)).map
        (fun byte => PanWordLab.word
          (BitVec.ofNat dimension.width byte.toNat)) := by
  exact evalCrepHolFiniteWordSourceExpWordLab_loadByte_eq_panMemLoadByteHOL
    dimension state.toSourceEvaluatorState addressExpression address hAddress

/-- Arbitrary-index finite-state `Op` case of HOL `eval_def`. The successful
`mapM` result is the recursive induction information; the result is exactly
the tagged `word_op_def` operation after the word-index conversion and keeps
the full `word_lab` wrapper. The enclosing evaluator still uses the explicit
dimension projection, so this case is not tagged as native `eval_def`. -/
theorem evalCrepHolFiniteStateSource_op
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (operator : BinOp)
    (expressions : List (CrepExp (ι → Bool))) (values : List (ι → Bool))
    (hValues : expressions.mapM
      (evalCrepHolFiniteWordSourceExp dimension
        state.toSourceEvaluatorState) = some values) :
    (evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.op operator expressions)).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (wordOpHOL operator (values.map (holWordToBitVec dimension))).map
      PanWordLab.word := by
  exact evalCrepHolFiniteWordSourceExpWordLab_op_eq_wordOpHOL
    dimension state.toSourceEvaluatorState operator expressions values hValues

/-- Arbitrary-index finite-state `CrepOp.mul` case of HOL `eval_def`. Its
successful child premises reproduce the recursive evaluator case, and the
result is the tagged `crep_op_def` operation with the complete `word_lab`
wrapper. This remains untagged because it is still a clause of the explicit
dimension source evaluator, not the complete native HOL evaluator. -/
theorem evalCrepHolFiniteStateSource_crepOpMul
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState left = some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState right = some rightValue) :
    (evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.crepOp .mul [left, right])).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (crepOpCrepWord (width := dimension.width) .mul
      [holWordToBitVec dimension leftValue,
       holWordToBitVec dimension rightValue]).map PanWordLab.word := by
  exact evalCrepHolFiniteWordSourceExpWordLab_crepOp_eq_crepOpCrepWord
    dimension state.toSourceEvaluatorState left right leftValue rightValue
    hLeft hRight

/-- Arbitrary-index finite-state `Cmp` case of HOL `eval_def`. The recursive
operand results feed the exact tagged HOL `word_cmp` operation; the result
retains both finite-dimension transport and the complete `word_lab` wrapper.
This remains untagged because it is a case of the explicit-dimension source
evaluator, not yet a theorem about native HOL `crepSem$eval`. -/
theorem evalCrepHolFiniteStateSource_cmp
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (operator : Cmp)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState left = some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState right = some rightValue) :
    ((evalCrepHolFiniteWordSourceExp dimension state.toSourceEvaluatorState
      (.cmp operator left right)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    some (PanWordLab.word
      (Compiler.Encoders.Asm.wordCmpResultHOL operator
        (holWordToBitVec dimension leftValue)
        (holWordToBitVec dimension rightValue))) := by
  exact evalCrepHolFiniteWordSourceExpWordLab_cmp_eq_wordCmpHOL
    dimension state.toSourceEvaluatorState operator left right leftValue rightValue
    hLeft hRight

/-- Arbitrary-index finite-state `Shift` case of HOL `eval_def`. It exposes
the exact tagged `word_sh` option result, including out-of-range failure, and
keeps the `word_lab` constructor around any successful result. It is not
tagged as native `eval_def` while the explicit-dimension evaluator relation is
still unproved. -/
theorem evalCrepHolFiniteStateSource_shift
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (operator : Shift)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState left = some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState right = some rightValue) :
    ((evalCrepHolFiniteWordSourceExp dimension state.toSourceEvaluatorState
      (.shift operator left right)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (wordShiftHOL operator
      (holWordToBitVec dimension leftValue)
      (holWordToBitVec dimension rightValue).toNat).map PanWordLab.word := by
  exact evalCrepHolFiniteWordSourceExpWordLab_shift_eq_wordShiftHOL
    dimension state.toSourceEvaluatorState operator left right leftValue rightValue
    hLeft hRight

/-- Exact-state, arbitrary-index source support for HOL's local
`simp_exp_correct1` statement shape. Both the expression words and state words
use the same `ι → Bool` carrier; the implicit dimension witness is used only
by the evaluator's word operations. The HOL `mapc` update remains on the exact
MlString-keyed state, and the proof derives any induction result from the
original non-NONE premise. This remains untagged until this source evaluator is
identified with native `crepSem$eval` for the selected `finite_index`. -/
theorem crepSimpExpCorrect1CrepSemHOLFiniteStateSourceWordLab
    {ι codeEntry σ : Type} [dimension : HolFiniteDimension ι]
    (update : MlString × codeEntry → codeEntry)
    (state : CrepSemHOLFiniteState ι codeEntry σ)
    (expression : CrepExp (ι → Bool))
    (h : evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState expression ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (state.mapc update).toSourceEvaluatorState
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression) =
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState expression := by
  obtain ⟨result, _hResult⟩ := Option.ne_none_iff_exists'.mp h
  let source := state.toSourceEvaluatorState
  have hSourceUpdate :
      crepArithHolFiniteDimensionMapCode
        (fun pair : FunName × (List Nat × CrepProg (ι → Bool)) => pair.2)
        source = source := by
    cases source with
    | mk locals globals code memory memaddrs shMemaddrs clock bigEndian ffi
        baseAddress topAddress =>
      simp [crepArithHolFiniteDimensionMapCode]
  have hPreserved := crepSimpExpCorrect1HolFiniteWordSourceWordLab
    (dimension := dimension)
    (f := fun pair : FunName × (List Nat × CrepProg (ι → Bool)) => pair.2)
    source expression result h
  rw [hSourceUpdate] at hPreserved
  rw [CrepSemHOLFiniteState.toSourceEvaluatorState_mapc]
  exact hPreserved

/-- The production expression evaluator, run over the state-derived source
memory adapter, agrees for every constructor with the explicit finite-word
source evaluator. This isolates the evaluator implementation bridge on the
HOL-shaped finite-map state before invoking the simp theorem. It remains
Flapjack-only: the source evaluator's operation interpretation and
`HolFiniteDimension` encoding have not yet been proved identical to native HOL
`crepSem$eval` and its implicit `finite_index` instance. -/
theorem evalCrepRuntimeExp_CrepSemHOLFiniteStateSourceWordLab
    {ι codeEntry σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι codeEntry σ)
    (expression : CrepExp (ι → Bool)) :
    (evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      expression).map PanWordLab.word =
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState expression := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepRuntimeExp_sourceWord_eq]

/-- All-width production-runtime support for HOL `eval_mul_const`. The
successful premise and complete `Option word_lab` conclusion match the source
theorem's evaluation shape. Locals/globals use finite maps, while the code
entry carrier is abstract because expression evaluation does not read code;
the source-runtime projection also erases code and FFI observations. The
implicit dimension dictionary represents a chosen finite index. This remains
untagged because these projections and the source-memory word operations have
not been proved identical to native HOL `crepSem$eval` for that finite index. -/
theorem crepEvalMulConstCrepSemHOLFiniteStateSourceRuntimeWordLab
    {ι codeEntry σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι codeEntry σ)
    (expression : CrepExp (ι → Bool)) (constant value : ι → Bool)
    (h : (evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      expression).map PanWordLab.word = some (.word value)) :
    (evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      (crepMulConst
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression constant)).map PanWordLab.word =
      some (.word (value * constant)) := by
  have hSource : (evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState expression).map PanWordLab.word =
      some (.word value) := by
    simpa [evalCrepHolFiniteWordSourceExpWordLab] using
      (evalCrepRuntimeExp_CrepSemHOLFiniteStateSourceWordLab
        state expression).symm.trans h
  have hSourceMul := crepEvalMulConstHolFiniteWordSourceEval dimension
    state.toSourceEvaluatorState expression constant value hSource
  exact (evalCrepRuntimeExp_CrepSemHOLFiniteStateSourceWordLab state _).trans
    hSourceMul

/-- Exact-syntax corollary of the all-width `eval_mul_const` support theorem.
It keeps HOL's `CrepExpHOL` input and the state code-entry type, while
transporting the expression into the arbitrary-index word carrier selected by
`HolFiniteDimension`. It remains untagged for the same native evaluator gap as
the underlying source-runtime theorem. -/
theorem crepEvalMulConstCrepSemHOLFiniteStateSourceRuntimeHOLExp
    {ι σ : Type} [dimension : HolFiniteDimension ι]
    [NeZero dimension.width]
    (state : CrepSemHOLFiniteState ι
      (List Nat × CrepProgHOL dimension.width) σ)
    (expression : CrepExpHOL dimension.width)
    (constant value : ι → Bool)
    (h : (evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      (mapCrepExpWord (bitVecToHolWord dimension)
        (crepExpOfHOL expression))).map PanWordLab.word = some (.word value)) :
    (evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      (crepMulConst
        (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n))
        (mapCrepExpWord (bitVecToHolWord dimension)
          (crepExpOfHOL expression)) constant)).map PanWordLab.word =
      some (.word (value * constant)) := by
  exact crepEvalMulConstCrepSemHOLFiniteStateSourceRuntimeWordLab state
    (mapCrepExpWord (bitVecToHolWord dimension) (crepExpOfHOL expression))
    constant value h

/-- Production-evaluator view of the arbitrary-index exact-state theorem
above. The adapter is constructed solely from the HOL-observable state fields
and the explicit word-dimension representation; it uses the source memory
model, not the canonical RISC-V target. Thus the theorem has no target-success
or target-operation premise and preserves the complete `Option word_lab`
result at every positive width. It remains untagged until this state-derived
runtime adapter is proved identical to native HOL `crepSem$eval`. -/
theorem crepSimpExpCorrect1CrepSemHOLFiniteStateSourceRuntimeWordLab
    {ι codeEntry σ : Type} [dimension : HolFiniteDimension ι]
    (update : MlString × codeEntry → codeEntry)
    (state : CrepSemHOLFiniteState ι codeEntry σ)
    (expression : CrepExp (ι → Bool))
    (h : (evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      expression).map PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp
      ((state.mapc update).toSourceEvaluatorState.toHolFiniteWordSourceRuntime
        dimension)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression)).map PanWordLab.word =
    (evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      expression).map PanWordLab.word := by
  have hSource : evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState expression ≠ none := by
    simpa [evalCrepRuntimeExp_CrepSemHOLFiniteStateSourceWordLab] using h
  calc
    (evalCrepRuntimeExp
        ((state.mapc update).toSourceEvaluatorState.toHolFiniteWordSourceRuntime
          dimension)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension
            (BitVec.ofNat dimension.width n)) expression)).map PanWordLab.word =
      evalCrepHolFiniteWordSourceExpWordLab dimension
        (state.mapc update).toSourceEvaluatorState
        (crepSimpExp
          (fun n => bitVecToHolWord dimension
            (BitVec.ofNat dimension.width n)) expression) :=
          evalCrepRuntimeExp_CrepSemHOLFiniteStateSourceWordLab
            (state.mapc update) _
    _ = evalCrepHolFiniteWordSourceExpWordLab dimension
          state.toSourceEvaluatorState expression :=
        crepSimpExpCorrect1CrepSemHOLFiniteStateSourceWordLab
          update state expression hSource
    _ = (evalCrepRuntimeExp
          (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
          expression).map PanWordLab.word :=
        (evalCrepRuntimeExp_CrepSemHOLFiniteStateSourceWordLab
          state expression).symm

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

/-- All-positive-width `simp_exp_correct1` support over the exact
`CrepSemHOLState` and `CrepExpHOL` carriers, using the source-shaped
`evalCrepHolExp` translation of `crepSem$eval_def` in the premise and result.
The code update has HOL's exact `MlString`/`CrepProgHOL` type and the result
preserves the complete `HolWordLab`-backed word result through the evaluator's
word-lab projection. This stays untagged because the source evaluator still
uses canonical `BitVec width` rather than an arbitrary HOL finite_index
carrier; the adjacent production-runtime theorem separately connects this
result to the executed evaluator. -/
theorem crepSimpExpCorrect1CrepSemHOLStateHolEval
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : evalCrepHolExpWordLab state.toBitVecEvaluatorState
      (crepExpOfHOL expression) ≠ none) :
    evalCrepHolExpWordLab
      (state.mapc update).toBitVecEvaluatorState
      (crepSimpExp (BitVec.ofNat width) (crepExpOfHOL expression)) =
    evalCrepHolExpWordLab state.toBitVecEvaluatorState
      (crepExpOfHOL expression) := by
  rw [CrepSemHOLState.toBitVecEvaluatorState_mapc]
  let projected := state.toBitVecEvaluatorState
  have hCodeId :
      crepArithHolMapCode
        (fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
        projected = projected := by
    cases projected
    simp [crepArithHolMapCode]
  have hPres := crepSimpExpCorrect1BitVec
    (f := fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
    projected (crepExpOfHOL expression) h
  rw [hCodeId] at hPres
  exact hPres

/-- Arbitrary finite-index support over the exact HOL-shaped state/code
carriers. The state retains finite-map locals/globals/code, the HOL
`MlString`/`CrepProgHOL` code-entry type, total memory and set domains, and
`HolFfiState`; the implicit `HolFiniteDimension` instance supplies the
finite-index enumeration.
Expressions and word-lab results are transported between the exact
`CrepExpHOL`/`BitVec` syntax and the dimension-indexed `ι → Bool` source
evaluator. This remains untagged because that source evaluator's dimension
and word-operation adapters have not yet been proved identical to HOL's
implicit `finite_index` instances and native `crepSem$eval`. -/
theorem crepSimpExpCorrect1CrepSemHOLFiniteStateSourceEval
    {ι : Type} [dimension : HolFiniteDimension ι] {σ : Type}
    (update : MlString ×
      (List Nat × CrepProgHOL dimension.width) →
      List Nat × CrepProgHOL dimension.width)
    (state : CrepSemHOLFiniteState ι
      (List Nat × CrepProgHOL dimension.width) σ)
    (expression : CrepExpHOL dimension.width)
    (h : evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState
      (mapCrepExpWord (bitVecToHolWord dimension) (crepExpOfHOL expression)) ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (state.mapc update).toSourceEvaluatorState
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (mapCrepExpWord (bitVecToHolWord dimension) (crepExpOfHOL expression))) =
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState
      (mapCrepExpWord (bitVecToHolWord dimension) (crepExpOfHOL expression)) := by
  obtain ⟨result, _hResult⟩ := Option.ne_none_iff_exists'.mp h
  let source := state.toSourceEvaluatorState
  let sourceExpression :=
    mapCrepExpWord (bitVecToHolWord dimension) (crepExpOfHOL expression)
  have hSourceUpdate :
      crepArithHolFiniteDimensionMapCode
        (fun pair : FunName × (List Nat × CrepProg (ι → Bool)) => pair.2)
        source = source := by
    cases source with
    | mk locals globals code memory memaddrs shMemaddrs clock bigEndian ffi
        baseAddress topAddress =>
      simp [crepArithHolFiniteDimensionMapCode]
  have hPreserved := crepSimpExpCorrect1HolFiniteWordSourceEvalClass
    (dimension := dimension)
    (f := fun pair : FunName × (List Nat × CrepProg (ι → Bool)) => pair.2)
    source sourceExpression result h
  rw [hSourceUpdate] at hPreserved
  rw [CrepSemHOLFiniteState.toSourceEvaluatorState_mapc]
  exact hPreserved

/-- All-dimension production-runtime support for the complete HOL-shaped
`simp_exp_correct1` state and code update. The state retains exact finite maps,
`MlString` code keys, `CrepProgHOL` entries, `HolFfiState`, total memory,
address domains, and the full `Option word_lab` result. Evaluation uses
`evalCrepRuntimeExp` after projecting the expression-observable fields into
the explicit `HolFiniteDimension` runtime adapter; the HOL `mapc` update is
preserved in the input state and erased by that projection, as expression
evaluation does not inspect code. This remains untagged because the adapter's
explicit dimension/word operations and its inert FFI projection have not yet
been identified with native HOL `crepSem$eval` for the selected implicit
`finite_index` instance. -/
theorem crepSimpExpCorrect1CrepSemHOLFiniteStateRuntime
    {ι : Type} [dimension : HolFiniteDimension ι] {σ : Type}
    (update : MlString ×
      (List Nat × CrepProgHOL dimension.width) →
      List Nat × CrepProgHOL dimension.width)
    (state : CrepSemHOLFiniteState ι
      (List Nat × CrepProgHOL dimension.width) σ)
    (expression : CrepExpHOL dimension.width)
    (h : (evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      (mapCrepExpWord (bitVecToHolWord dimension)
        (crepExpOfHOL expression))).map PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp
      ((state.mapc update).toSourceEvaluatorState.toHolFiniteWordSourceRuntime
        dimension)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n))
        (mapCrepExpWord (bitVecToHolWord dimension)
          (crepExpOfHOL expression)))).map PanWordLab.word =
    (evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      (mapCrepExpWord (bitVecToHolWord dimension)
        (crepExpOfHOL expression))).map PanWordLab.word := by
  have hRaw : evalCrepRuntimeExp
      (state.toSourceEvaluatorState.toHolFiniteWordSourceRuntime dimension)
      (mapCrepExpWord (bitVecToHolWord dimension)
        (crepExpOfHOL expression)) ≠ none := by
    intro hNone
    simp [hNone] at h
  have hPreserved := crepSimpExpEvalPreservesHolFiniteWordSource
    dimension state.toSourceEvaluatorState
    (mapCrepExpWord (bitVecToHolWord dimension)
      (crepExpOfHOL expression)) hRaw
  rw [CrepSemHOLFiniteState.toSourceEvaluatorState_mapc]
  exact congrArg (Option.map PanWordLab.word) hPreserved

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

/-- Exact positive-width state projection for the production `BaseAddr`
    evaluator clause. It returns the source state's address unchanged, without
    assumptions about evaluation success, code, FFI, or the runtime word
    model. Kept untagged because this width-indexed `BitVec` representation
    has not been related to every HOL `finite_index` word carrier. -/
theorem evalCrepRuntimeExp_toBitVecEvaluatorState_baseAddr
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((evalCrepRuntimeExp (state.toBitVecEvaluatorState.toRuntime)
      .baseAddr).map PanWordLab.word).map PanWordLab.toHolWordLab =
      some (.word state.baseAddr) := by
  simp [evalCrepRuntimeExp, CrepSemHOLState.toBitVecEvaluatorState,
    CrepHolState.toRuntime, PanWordLab.toHolWordLab]

/-- Exact positive-width state projection for the production `TopAddr`
    evaluator clause. It returns the source state's address unchanged, without
    assumptions about evaluation success, code, FFI, or the runtime word
    model. Kept untagged because this width-indexed `BitVec` representation
    has not been related to every HOL `finite_index` word carrier. -/
theorem evalCrepRuntimeExp_toBitVecEvaluatorState_topAddr
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((evalCrepRuntimeExp (state.toBitVecEvaluatorState.toRuntime)
      .topAddr).map PanWordLab.word).map PanWordLab.toHolWordLab =
      some (.word state.topAddr) := by
  simp [evalCrepRuntimeExp, CrepSemHOLState.toBitVecEvaluatorState,
    CrepHolState.toRuntime, PanWordLab.toHolWordLab]

/-- Flapjack support for the Const branch of HOL's local `simp_exp_correct1`
(`cakeml/pancake/proofs/crep_arithProofScript.sml:111`). The constant branch
reduces to the expected equality over the width-indexed BitVec evaluator. This
helper is untagged: its evaluator passes through
`CrepSemHOLState.toBitVecEvaluatorState`, whose relation to native arbitrary-
index HOL `crepSem$eval` has not been proved, and its result uses
`PanWordLab (BitVec width)` instead of HOL's `HolWordLab width`. It does not
claim even the isolated case as a port of the native evaluator theorem. -/
theorem crepSimpExpCorrect1ConstCaseBitVecSupport
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (constant : BitVec width) (_result : PanWordLab (BitVec width))
    (_h : evalCrepHolExpWordLab state.toBitVecEvaluatorState
      (.const constant) ≠ none) :
    evalCrepHolExpWordLab (state.mapc update).toBitVecEvaluatorState
        (crepSimpExp (BitVec.ofNat width) (.const constant)) =
      evalCrepHolExpWordLab state.toBitVecEvaluatorState (.const constant) := by
  rw [CrepSemHOLState.toBitVecEvaluatorState_mapc]
  simp [evalCrepHolExpWordLab, evalCrepHolExp, crepSimpExp.eq_11]

end Flapjack
