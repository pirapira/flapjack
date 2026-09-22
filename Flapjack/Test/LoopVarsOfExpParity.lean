import Flapjack.LoopAnalysis

/-! Direct parity for `loop_live$vars_of_exp_def` at
`cakeml/pancake/loop_liveScript.sml:11`.  The expected lists are the printed
HOL `num_set` results from `vars_of_exp_probe.out`. -/
namespace Flapjack.Test.LoopVarsOfExpParity

def parityGuard : Bool :=
  varsOfExp (.var 3 : LoopExp Nat) [] == [3] &&
  varsOfExp (.const 7 : LoopExp Nat) [9] == [9] &&
  varsOfExp (.load (.var 4) : LoopExp Nat) [9] == [4, 9] &&
  varsOfExp
      (.op .add [.var 3, .const 1, .var 2] : LoopExp Nat) [] == [2, 3] &&
  varsOfExp
      (.shift .lsl (.var 6) (.load (.var 1)) : LoopExp Nat) [8] == [1, 6, 8]

#eval parityGuard
#guard parityGuard

/-! Counterparts of CakeML's `vars_of_exp_acc`
    (`cakeml/pancake/proofs/loop_liveProofScript.sml:339`) and
    `vars_of_exp_mono` (`cakeml/pancake/proofs/loop_liveProofScript.sml:400`). -/

theorem varsOfExp_acc_fixture :
    (3 : Nat) ∈ varsOfExp (.var 3 : LoopExp Nat) [] ↔
      (3 : Nat) ∈ varsOfExp (.var 3 : LoopExp Nat) [] ∨
        (3 : Nat) ∈ ([] : List Nat) :=
  varsOfExp_acc (.var 3) [] 3

theorem varsOfExp_mono_fixture :
    (9 : Nat) ∈ varsOfExp (.const 7 : LoopExp Nat) [9] :=
  varsOfExp_mono (.const 7) [9] 9 (by simp)

def varsAccGuard : Bool :=
  (varsOfExp (.op .add [.var 3, .const 1, .var 2] : LoopExp Nat) [9]).contains 9 &&
    (varsOfExp (.op .add [.var 3, .const 1, .var 2] : LoopExp Nat) [9]).contains 3 &&
    (varsOfExp (.op .add [.var 3, .const 1, .var 2] : LoopExp Nat) [9]).contains 2

#eval varsAccGuard
#guard varsAccGuard

end Flapjack.Test.LoopVarsOfExpParity
