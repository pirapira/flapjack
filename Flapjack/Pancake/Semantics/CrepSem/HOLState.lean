import Flapjack.FiniteMap.Basic
import Flapjack.Basis.Pure.MlString
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.Pancake.Semantics.PanSem

/-!
# Exact state carriers for Crep expression proofs

This file records the field carriers from `crepSem$state` independently of
the executable runtime adapter. Its finite maps carry an explicit finite
support witness, code names use `MlString`, code entries use `CrepProgHOL`,
and memory domains are Lean sets. The word dimension is represented by the
canonical `BitVec width` model for each positive HOL dimension.

The expression-evaluator projection below deliberately forgets `code` and
`ffi`: `crepSem$eval` for expressions never reads either field. It maps only
the expression-observable fields into the all-width source evaluator state.
This is a state-carrier prerequisite, not a port of the evaluator itself.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- A total lookup function with a proof that its defined domain is finite,
matching the observable representation of HOL `fmap`. -/
structure HolFiniteMapExact (α β : Type) where
  lookup : α → Option β
  finiteSupport : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys

namespace HolFiniteMapExact

/-- HOL `FMAP_MAP2`: preserve keys and map each present value with the key
available to the callback. -/
def map2 (f : α × β → γ) (map : HolFiniteMapExact α β) :
    HolFiniteMapExact α γ where
  lookup key := (map.lookup key).map (fun value => f (key, value))
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨keys, ?_⟩
    intro key hlookup
    apply hkeys key
    cases hsource : map.lookup key <;> simp [hsource] at hlookup ⊢

@[simp] theorem lookup_map2 (f : α × β → γ)
    (map : HolFiniteMapExact α β) (key : α) :
    (map.map2 f).lookup key = (map.lookup key).map (fun value => f (key, value)) := rfl

end HolFiniteMapExact

/-- The `crepSem$state` record (`crepSemScript.sml:19-32`) with its HOL
carriers: finite maps for locals/globals/code, a total word-to-word_lab memory
function, set-valued memory domains, clock/endian fields, arbitrary FFI state,
and base/top words. `width` represents the positive cardinality of the HOL
word index. -/
structure CrepSemHOLState (width : Nat) [NeZero width] (ffiState : Type) where
  locals : HolFiniteMapExact Nat (HolWordLab width)
  globals : HolFiniteMapExact (BitVec 5) (HolWordLab width)
  code : HolFiniteMapExact MlString (List Nat × CrepProgHOL width)
  memory : BitVec width → HolWordLab width
  memaddrs : BitVec width → Prop
  shMemaddrs : BitVec width → Prop
  clock : Nat
  be : Bool
  ffi : ffiState
  baseAddr : BitVec width
  topAddr : BitVec width

/-- HOL's local `mapc f` state update, defined with the same `FMAP_MAP2` value
mapping on the code map. -/
def CrepSemHOLState.mapc {width : Nat} [NeZero width] {ffiState : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width ffiState) : CrepSemHOLState width ffiState :=
  { state with code := state.code.map2 f }

@[simp] theorem CrepSemHOLState.FLOOKUP_mapc {width : Nat} [NeZero width]
    {ffiState : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width ffiState) (name : MlString) :
    (state.mapc f).code.lookup name =
      (state.code.lookup name).map (fun entry => f (name, entry)) := rfl

private def crepExpressionProjectionFfi : FfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed
    state := ()
    ioEvents := [] }

private def holWordLabToBits {width : Nat} (cell : HolWordLab width) :
    PanWordLab (Fin width → Bool) :=
  match cell with
  | .word word => .word (bitVecToHolWordBits word)

/-- Project just the observable fields to the existing all-width source
evaluator. Code is empty and FFI is a fixed witness because expression `eval`
does not inspect either field; memory domains are converted from HOL sets to
their Boolean characteristic functions. -/
noncomputable def CrepSemHOLState.toExpressionEvaluatorState
    {width : Nat} [NeZero width] {ffiState : Type}
    (state : CrepSemHOLState width ffiState) :
    CrepHolState (Fin width → Bool) Unit := by
  classical
  exact
    { locals := fun name => (state.locals.lookup name).map holWordLabToBits
      globals := fun name => (state.globals.lookup name).map holWordLabToBits
      code := fun _ => none
      memory := fun address => holWordLabToBits
        (state.memory (holWordBitsToBitVec address))
      memaddrs := fun address => decide
        (state.memaddrs (holWordBitsToBitVec address))
      shMemaddrs := fun address => decide
        (state.shMemaddrs (holWordBitsToBitVec address))
      clock := state.clock
      bigEndian := state.be
      ffi := crepExpressionProjectionFfi
      baseAddress := bitVecToHolWordBits state.baseAddr
      topAddress := bitVecToHolWordBits state.topAddr }

@[simp] theorem CrepSemHOLState.toExpressionEvaluatorState_mapc
    {width : Nat} [NeZero width] {ffiState : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width ffiState) :
    (state.mapc f).toExpressionEvaluatorState =
      state.toExpressionEvaluatorState := by
  rfl

/-- Changing only the HOL code map cannot alter expression evaluation after
projection into the existing source evaluator. This is the state-side mapc
fact used by the `simp_exp_correct1` dependency; evaluator correspondence to
native HOL is still handled separately. -/
theorem evalCrepHolFiniteWordSourceExp_mapc_projection
    {width : Nat} [NeZero width] {ffiState : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width ffiState)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        (state.mapc f).toExpressionEvaluatorState expression =
      evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        state.toExpressionEvaluatorState expression := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]

end Flapjack
