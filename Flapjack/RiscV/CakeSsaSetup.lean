import Flapjack.RiscV.Allocator

/-! Small source-shaped adapters for the CakeML allocator entry boundary.

`setup_ssa` takes an explicit fresh-name limit and is independent of the body
being renamed.  The main allocator entry points compute that limit from the
Word program; this helper preserves the source-level setup operation for
oracle-backed tests and later IRC composition. -/

namespace Flapjack.RiscV.CakeRegAlloc

open Flapjack

def cakeEvenList (count : Nat) : List Nat :=
  (List.range count).map (fun index => 2 * index)

def cakeSetupSsa {α : Type u} (parameterCount limit : Nat)
    (_program : WordProg α) :
    WordProg α × (WordSsaState × Nat) :=
  let arguments := cakeEvenList parameterCount
  let (state, renamed) := wordSsaFreshList
    ({ current := [], next := limit } : WordSsaState) arguments
  (.move 1 (renamed.zip arguments), (state, state.next))

end Flapjack.RiscV.CakeRegAlloc
