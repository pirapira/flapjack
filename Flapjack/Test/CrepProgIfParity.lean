import Flapjack.Pancake.CrepToLoop

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

/-- Width-indexed exact port `progIfW` (`@[hol ... "prog_if_def"]`) reproduces
    the same HOL oracle row `prog_if_basic`
    (`scripts/hol-probes/prog_if_probe.out`) at `BitVec 8`. -/
example :
    progIfW .notEqual [.skip] [.tick]
        (.const (2 : BitVec 8)) (.const (3 : BitVec 8)) 3 4 [1, 2] =
      ([.skip, .tick,
        .assign 3 (.const (2 : BitVec 8)),
        .assign 4 (.const (3 : BitVec 8)),
        .ite .notEqual 3 (.reg 4)
          (.assign 3 (.const (1 : BitVec 8)))
          (.assign 3 (.const (0 : BitVec 8)))
          [1, 2, 3, 4]] : List (LoopProg (BitVec 8))) := rfl

#eval leanProgIf
#guard parityGuard

end Flapjack.Test.CrepProgIfParity
