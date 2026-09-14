import Flapjack.CrepToLoop

/-!
Direct parity for `crep_to_loop$prog_if` (`crep_to_loopScript.sml:34`).
The HOL fixture observes both the statement-list order and the canonical
ascending live set produced by CakeML's `list_insert`.
-/
namespace Flapjack.Test.CrepProgIfParity

def originalProgIf : List (LoopProg Nat) :=
  [.skip, .tick,
   .assign 3 (.const 2),
   .assign 4 (.const 3),
   .ite .notEqual 3 (.reg 4)
     (.assign 3 (.const 1))
     (.assign 3 (.const 0))
     [1, 2, 3, 4]]

def leanProgIf : List (LoopProg Nat) :=
  progIf .notEqual [.skip] [.tick] (.const 2) (.const 3) 3 4 [1, 2]

def parityGuard : Bool :=
  match leanProgIf with
  | [.skip, .tick,
     .assign 3 (.const 2),
     .assign 4 (.const 3),
     .ite .notEqual 3 (.reg 4)
       (.assign 3 (.const 1))
       (.assign 3 (.const 0))
       [1, 2, 3, 4]] => true
  | _ => false

#eval leanProgIf
#guard parityGuard

end Flapjack.Test.CrepProgIfParity
