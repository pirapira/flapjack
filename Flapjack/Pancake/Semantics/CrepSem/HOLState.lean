import Flapjack.FiniteMap.Basic
import Flapjack.Basis.Pure.MlString
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.FfiHOL

/-!
# HOL-shaped state carriers for Crep expression proofs

This file records the field carriers from `crepSem$state` independently of
the executable runtime adapter. Its finite maps carry an explicit finite
support witness, code names use `MlString`, code entries use `CrepProgHOL`,
and memory domains are Lean sets. The word dimension is represented by the
canonical `BitVec width` model for each positive HOL dimension.

These declarations are Flapjack representation infrastructure and carry no
`@[hol]` tags: the word index is represented by its positive cardinality and
`BitVec width`, rather than by an arbitrary HOL `finite_index` type together
with an explicit carrier equivalence. The expression-evaluator projection
below also deliberately forgets `code` and `ffi`, which expression `eval`
does not read. It maps only the expression-observable fields into the
all-width source evaluator state. This is a state-carrier prerequisite, not a
port of the evaluator itself.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Flapjack finite-support map infrastructure: a total lookup function with a
proof that its defined domain is finite. This models HOL `fmap` observations
but is not separately tagged as the generic finite-map type declaration. -/
structure HolFiniteMapExact (α β : Type) where
  lookup : α → Option β
  finiteSupport : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys

namespace HolFiniteMapExact

/-- Flapjack encoding of HOL `FMAP_MAP2`: preserve keys and map each present
value with the key available to the callback. -/
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

/-- Flapjack's HOL-shaped encoding of `crepSem$state`
(`crepSemScript.sml:19-32`): finite maps for locals/globals/code, a total
word-to-word_lab memory function, set-valued memory domains, clock/endian
fields, an exact `HolFfiState σ`, and base/top words. It is untagged because its
word index is represented by positive `width`/`BitVec width`; the explicit
equivalence to each arbitrary HOL `finite_index` instance is not carried here. -/
structure CrepSemHOLState (width : Nat) [NeZero width] (ffiState : Type) where
  locals : HolFiniteMapExact Nat (HolWordLab width)
  globals : HolFiniteMapExact (BitVec 5) (HolWordLab width)
  code : HolFiniteMapExact MlString (List Nat × CrepProgHOL width)
  memory : BitVec width → HolWordLab width
  memaddrs : BitVec width → Prop
  shMemaddrs : BitVec width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState ffiState
  baseAddr : BitVec width
  topAddr : BitVec width

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

end Flapjack
