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

/-! Counterpart of CakeML's `domain_list_delete`
    (`cakeml/pancake/proofs/loop_liveProofScript.sml:561`). -/

theorem deleteNatSorted_mem_fixture :
    (2 : Nat) ∈ deleteNatSorted 3 [2, 3, 4] ↔
      (2 : Nat) ∈ ([2, 3, 4] : List Nat) ∧ (2 : Nat) ≠ 3 :=
  deleteNatSorted_mem 3 [2, 3, 4] 2

theorem loopListDeleteSorted_mem_fixture :
    (2 : Nat) ∈ loopListDeleteSorted [3] [2, 3, 4] ↔
      (2 : Nat) ∈ ([2, 3, 4] : List Nat) ∧ (2 : Nat) ∉ [3] :=
  loopListDeleteSorted_mem [3] [2, 3, 4] 2

def deleteSortedGuard : Bool :=
  (deleteNatSorted 3 [2, 3, 4]).contains 2 &&
    !(deleteNatSorted 3 [2, 3, 4]).contains 3 &&
    (loopListDeleteSorted [3, 4] [2, 3, 4, 5]).contains 2 &&
    !(loopListDeleteSorted [3, 4] [2, 3, 4, 5]).contains 4

#eval deleteSortedGuard
#guard deleteSortedGuard

/-! Counterpart of CakeML's `eval_lemma`
    (`cakeml/pancake/proofs/loop_liveProofScript.sml:443`). -/

def liveState : LoopState Nat :=
  { locals := fun n => if n == 3 then some 5 else none,
    globals := fun _ => none,
    memory := fun _ => none }

def liveLocals : Nat → Option Nat :=
  fun n => if n == 3 then some 5 else some 99

theorem evalLoopExp_locals_congr_fixture :
    evalLoopExp { liveState with locals := liveLocals } (.var 3 : LoopExp Nat) =
      some 5 :=
  evalLoopExp_locals_congr liveState liveLocals (.var 3) 5
    (by
      intro name hmem
      simp [loopVarsOfExp] at hmem
      subst hmem
      simp [liveState, liveLocals])
    (by simp [evalLoopExp, liveState])

def evalLocalsGuard : Bool :=
  evalLoopExp { liveState with locals := liveLocals } (.var 3 : LoopExp Nat) == some 5 &&
    evalLoopExp { liveState with locals := liveLocals }
      (.op .add [.var 3, .const 1] : LoopExp Nat) == some 6

#eval evalLocalsGuard
#guard evalLocalsGuard

/-! Counterpart of CakeML's `eval_lemma'`
    (`cakeml/pancake/proofs/loop_liveProofScript.sml:416`): extending the local
    state preserves the value of an expression. -/

def extendedLocals : Nat → Option Nat :=
  fun n => if n == 3 then some 5 else if n == 4 then some 7 else none

theorem evalLoopExp_locals_extend_fixture :
    evalLoopExp { liveState with locals := extendedLocals } (.var 3 : LoopExp Nat) =
      some 5 :=
  evalLoopExp_locals_extend liveState extendedLocals (.var 3) 5
    (by
      intro name v hname
      simp [liveState] at hname
      obtain ⟨rfl, rfl⟩ := hname
      simp [extendedLocals])
    (by simp [evalLoopExp, liveState])

def evalExtendGuard : Bool :=
  evalLoopExp { liveState with locals := extendedLocals } (.var 3 : LoopExp Nat) ==
      some 5 &&
    evalLoopExp { liveState with locals := extendedLocals }
      (.op .add [.var 3, .const 1] : LoopExp Nat) == some 6

#eval evalExtendGuard
#guard evalExtendGuard

end Flapjack.Test.LoopVarsOfExpParity
