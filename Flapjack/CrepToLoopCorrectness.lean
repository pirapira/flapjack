import Flapjack.CorrectnessFfi
import Flapjack.CrepeSemantics
import Flapjack.CrepeRuntime
import Flapjack.CrepToLoop

namespace Flapjack

def crepControlGlobalAt (address : α) : CrepControlResult α → Option α
  | .normal state => state.globals address
  | .returned state _ => state.globals address
  | .raised state _ => state.globals address
  | .broke state _ => state.globals address
  | .continued state _ => state.globals address
  | .finalFfi state _ => state.globals address

/-!
The former contents of this module were generic identity-map witnesses for
Crep-to-Loop evaluation.  They became false when `compile` was made faithful
to Cake's context lookup: `Assign`, `ShMem`, and expression variables now use
the mapped slot, while an absent `find_var` lookup still yields register 0.

Keep this module as a small source-backed sanity boundary for clients that
still import its historical path.  Context-sensitive correctness belongs in
the source-shaped bridges, where the required lookup relation is explicit.
-/

theorem crepFindVar_missing_is_cake_zero
    (context : LoopContext α) (name : Nat)
    (hmissing : lookupNatInfo name context.vars = none) :
    crepFindVar context name = 0 := by
  simp [crepFindVar, findLoopVar, hmissing]

theorem crepFindVar_hit_is_cake_lookup
    (context : LoopContext α) (name mapped : Nat)
    (hlookup : lookupNatInfo name context.vars = some mapped) :
    crepFindVar context name = mapped := by
  simp [crepFindVar, findLoopVar, hlookup]

end Flapjack
