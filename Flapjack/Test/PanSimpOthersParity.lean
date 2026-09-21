import Flapjack.PanSimpOthers

namespace Flapjack.Test.PanSimpOthersParity

open Flapjack

/-! `compile_Others` parity: the program constructs that Cake's `compile`
    (`pan_simpProofScript.sml:667-1015`) leaves unchanged are also left
    unchanged by `panSimpProg`, and therefore evaluate identically. -/

example : panSimpProg (.return (.var .local "x") : Prog Nat) =
    .return (.var .local "x") :=
  panSimpProg_return _

example : panSimpProg (.assign .local "x" (.const 1) : Prog Nat) =
    .assign .local "x" (.const 1) :=
  panSimpProg_assign _ _ _

example : panSimpProg (.raise "E" (.const 1) : Prog Nat) =
    .raise "E" (.const 1) :=
  panSimpProg_raise _ _

example : panSimpProg (.store (.const 0) (.const 1) : Prog Nat) =
    .store (.const 0) (.const 1) :=
  panSimpProg_store _ _

example : panSimpProg (.break : Prog Nat) = .break := panSimpProg_break

example : panSimpProg (.tick : Prog Nat) = .tick := panSimpProg_tick

example : panSimpProg (.shMemStore .op32 (.const 0) (.const 1) : Prog Nat) =
    .shMemStore .op32 (.const 0) (.const 1) :=
  panSimpProg_shMemStore _ _ _

def returnUnchangedParity : Bool :=
  match panSimpProg (.return (.var .local "x") : Prog Nat) with
  | .return (.var .local "x") => true
  | _ => false

def breakUnchangedParity : Bool :=
  match panSimpProg (.break : Prog Nat) with
  | .break => true
  | _ => false

#eval returnUnchangedParity
#eval breakUnchangedParity
#guard returnUnchangedParity
#guard breakUnchangedParity

end Flapjack.Test.PanSimpOthersParity
