/-!
# Pancake `ext`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:625-642`.
The source record update replaces only the FFI field and clock.  The remaining
record fields are represented by the incoming state, while the two projected
updates are explicit callbacks so this boundary remains independent of a
backend-specific bstate representation.
-/

namespace Flapjack

def panExt (sourceState : σ) (clock : Nat) (ffi : τ)
    (setFfi : σ → τ → σ) (setClock : σ → Nat → σ) : σ :=
  setClock (setFfi sourceState ffi) clock

end Flapjack
