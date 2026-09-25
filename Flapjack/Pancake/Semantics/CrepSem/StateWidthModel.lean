import Flapjack.FfiHOL
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.Semantics.PanSem

/-!
# Width-indexed Crep state model

This support record follows the field order of `crepSem$state`
(`cakeml/pancake/semantics/crepSemScript.sml:19-30`), but is not tagged as that
HOL datatype. It fixes the word dimension to `Nat` and currently represents
finite maps as unrestricted lookup functions, so it does not retain HOL's
polymorphic index type or finite-support invariant. The code map uses HOL
`mlstring` names and `CrepProgHOL`, and `ffi` uses `HolFfiState`. It is kept
separate from `CrepHolState`, whose String-keyed code and executable `FfiState`
are runtime adapters rather than the HOL state fields.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Flapjack state-shape support for a fixed positive word width. It is not
    HOL `crepSem$state`: `FiniteMap` is an unrestricted lookup function rather
    than a finite-support map, and this record indexes words by a width rather
    than by HOL's polymorphic finite index type. -/
structure CrepSemStateWidthModel (width : Nat) (σ : Type) [NeZero width] where
  locals : FiniteMap Nat (HolWordLab width)
  globals : FiniteMap (BitVec 5) (HolWordLab width)
  code : FiniteMap MlString (List Nat × CrepProgHOL width)
  memory : BitVec width → HolWordLab width
  memaddrs : BitVec width → Prop
  shMemaddrs : BitVec width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState σ
  baseAddr : BitVec width
  topAddr : BitVec width

end Flapjack
