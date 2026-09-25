import Flapjack.FfiHOL
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.Semantics.PanSem

/-!
# Width-indexed Crep state model

This support record follows the field order of `crepSem$state`
(`cakeml/pancake/semantics/crepSemScript.sml:19-30`), but is not tagged as that
HOL datatype. It fixes the word dimension to `Nat`, while its finite-map fields
now enforce finite support. The remaining state-carrier gap is HOL's
polymorphic finite index type versus the width parameter. The code map uses
HOL `mlstring` names and `CrepProgHOL`, and `ffi` uses `HolFfiState`. It is kept
separate from `CrepHolState`, whose String-keyed code and executable `FfiState`
are runtime adapters rather than the HOL state fields.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Finite-support partial map used by the width-indexed Crep state model.
    This keeps the HOL `fmap` domain invariant; `toLookup` is the extensional
    view consumed by the existing evaluator adapters. -/
structure CrepHOLFiniteMap (α β : Type) where
  lookup : α → Option β
  support : List α
  lookup_supported : ∀ key, lookup key ≠ none → key ∈ support

namespace CrepHOLFiniteMap

def empty : CrepHOLFiniteMap α β := ⟨fun _ => none, [], by simp⟩

def toLookup (map : CrepHOLFiniteMap α β) : FiniteMap α β := map.lookup

@[simp] theorem lookup_empty (key : α) :
    (empty : CrepHOLFiniteMap α β).lookup key = none := rfl

theorem lookup_eq_none_of_not_mem_support (map : CrepHOLFiniteMap α β)
    {key : α} (hkey : key ∉ map.support) : map.lookup key = none := by
  cases hlookup : map.lookup key with
  | none => rfl
  | some value =>
      exact False.elim (hkey (map.lookup_supported key (by simp [hlookup])))

end CrepHOLFiniteMap

/-- Flapjack state-shape support for a fixed positive word width. It is not
    tagged as HOL `crepSem$state`, because this record indexes words by a width
    rather than by HOL's polymorphic finite index type. Its map fields enforce
    the finite-support invariant. -/
structure CrepSemStateWidthModel (width : Nat) (σ : Type) [NeZero width] where
  locals : CrepHOLFiniteMap Nat (HolWordLab width)
  globals : CrepHOLFiniteMap (BitVec 5) (HolWordLab width)
  code : CrepHOLFiniteMap MlString (List Nat × CrepProgHOL width)
  memory : BitVec width → HolWordLab width
  memaddrs : BitVec width → Prop
  shMemaddrs : BitVec width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState σ
  baseAddr : BitVec width
  topAddr : BitVec width

end Flapjack
