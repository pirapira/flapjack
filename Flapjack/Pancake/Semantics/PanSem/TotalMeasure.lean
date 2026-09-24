import Flapjack.Pancake.Semantics.PanSem

/-!
# Well-founded measure for total Pancake `evaluate`

HOL `evaluate_def` recurses on syntactic subprograms at the same clock in
`Dec`, `Seq`, and `If`, and recurses on a clock-decreased state for `While`,
`Call`, and `DecCall`.  The lexicographic measure below records those two
dimensions over the complete source state and syntax.  It is termination
infrastructure only: it does not define an evaluator or assert that a partial
or restricted evaluator is the HOL function.
-/

namespace Flapjack

universe u v

variable {α : Type u} {ffi : Type v}

/-- Lexicographic recursion measure for an exact total evaluator over
    `PanSemState` and `Prog`: the HOL source clock decreases before the
    structural source-program cost is consulted. The second coordinate is the
    already-defined `panSemProgFuel`, so this file does not add a competing
    syntax-size function. -/
def panSemEvalMeasure (state : PanSemState α ffi) (program : Prog α) : Nat × Nat :=
  (state.clock, panSemProgFuel program)

/-- Relation induced by `panSemEvalMeasure`; both coordinates use the natural
    strict order and the clock is the primary coordinate. -/
def panSemEvalMeasureRel (next current : PanSemState α ffi × Prog α) : Prop :=
  InvImage (Prod.Lex Nat.lt Nat.lt)
    (fun input : PanSemState α ffi × Prog α =>
      panSemEvalMeasure input.1 input.2) next current

/-- The clock/size relation is well-founded, including transitions to an
    arbitrary callee body after a strict source-clock decrement. -/
theorem panSemEvalMeasureRel_wf :
    WellFounded (@panSemEvalMeasureRel α ffi) := by
  have hproduct : WellFounded (Prod.Lex Nat.lt Nat.lt) :=
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  exact InvImage.wf
    (fun input : PanSemState α ffi × Prog α => panSemEvalMeasure input.1 input.2)
    hproduct

/-- Any recursive call at a strictly smaller source clock decreases the full
    measure, regardless of the callee program's size. This covers the
    `While`, `Call`, and `DecCall` transitions in `evaluate_def`. -/
theorem panSemEvalMeasureRel_of_clock_lt
    {nextState currentState : PanSemState α ffi}
    {nextProgram currentProgram : Prog α}
    (hclock : nextState.clock < currentState.clock) :
    panSemEvalMeasureRel (nextState, nextProgram) (currentState, currentProgram) := by
  change Prod.Lex Nat.lt Nat.lt
    (panSemEvalMeasure nextState nextProgram)
    (panSemEvalMeasure currentState currentProgram)
  unfold panSemEvalMeasure
  exact Prod.Lex.left _ _ hclock

/-- Every post-state whose clock is bounded by the source `dec_clock` value
    has lower measure than the source state, for any recursively evaluated
    body. This is the common `While`, `Call`, and `DecCall` clock transition. -/
theorem panSemEvalMeasureRel_of_clock_le_decPanClock
    {nextState currentState : PanSemState α ffi}
    {nextProgram currentProgram : Prog α}
    (hclock : currentState.clock ≠ 0)
    (hpostClock : nextState.clock ≤ decPanClock currentState.clock) :
    panSemEvalMeasureRel (nextState, nextProgram) (currentState, currentProgram) := by
  apply panSemEvalMeasureRel_of_clock_lt
  have hpositive : 0 < currentState.clock := Nat.pos_of_ne_zero hclock
  have hdecrement : decPanClock currentState.clock < currentState.clock := by
    simp [decPanClock]
    omega
  exact Nat.lt_of_le_of_lt hpostClock hdecrement

/-- A recursive call on a proper syntactic subprogram decreases the measure
    when it preserves the source clock. -/
theorem panSemEvalMeasureRel_of_same_clock_cost_lt
    {nextState currentState : PanSemState α ffi}
    {nextProgram currentProgram : Prog α}
    (hclock : nextState.clock = currentState.clock)
    (hsize : panSemProgFuel nextProgram < panSemProgFuel currentProgram) :
    panSemEvalMeasureRel (nextState, nextProgram) (currentState, currentProgram) := by
  change Prod.Lex Nat.lt Nat.lt
    (panSemEvalMeasure nextState nextProgram)
    (panSemEvalMeasure currentState currentProgram)
  unfold panSemEvalMeasure
  rw [hclock]
  exact Prod.Lex.right _ hsize

/-- A recursive call on a proper subprogram remains decreasing when an
    intervening state update can only preserve or lower the source clock. This
    is the shape required by the `Seq` continuation after `fix_clock`. -/
theorem panSemEvalMeasureRel_of_clock_le_cost_lt
    {nextState currentState : PanSemState α ffi}
    {nextProgram currentProgram : Prog α}
    (hclock : nextState.clock ≤ currentState.clock)
    (hsize : panSemProgFuel nextProgram < panSemProgFuel currentProgram) :
    panSemEvalMeasureRel (nextState, nextProgram) (currentState, currentProgram) := by
  rcases Nat.lt_or_eq_of_le hclock with hlt | heq
  · exact panSemEvalMeasureRel_of_clock_lt hlt
  · exact panSemEvalMeasureRel_of_same_clock_cost_lt heq hsize

/-- `If`'s selected source branch is structurally smaller than the enclosing
    conditional, so evaluating it at the unchanged state decreases the
    measure. -/
theorem panSemEvalMeasureRel_ite_branch
    (state : PanSemState α ffi) (condition : Exp α)
    (thenBranch elseBranch branch : Prog α)
    (hbranch : branch = thenBranch ∨ branch = elseBranch) :
    panSemEvalMeasureRel (state, branch)
      (state, Prog.ite condition thenBranch elseBranch) := by
  apply panSemEvalMeasureRel_of_same_clock_cost_lt rfl
  rcases hbranch with rfl | rfl <;> simp [panSemProgFuel] <;> omega

/-- Either direct command of a `Seq` is structurally smaller than its parent.
    In particular, the second command remains decreasing after `fix_clock`
    because that operation never raises the source clock. -/
theorem panSemEvalMeasureRel_seq_branch
    (nextState currentState : PanSemState α ffi)
    (first second branch : Prog α)
    (hclock : nextState.clock ≤ currentState.clock)
    (hbranch : branch = first ∨ branch = second) :
    panSemEvalMeasureRel (nextState, branch)
      (currentState, Prog.seq first second) := by
  apply panSemEvalMeasureRel_of_clock_le_cost_lt hclock
  rcases hbranch with rfl | rfl <;> simp [panSemProgFuel] <;> omega

/-- `Dec`, `While`, and `DecCall` body syntax is a proper subprogram. The
    lemma leaves clock behavior explicit so callers must establish whether
    their source clause preserves or decreases it. -/
theorem panSemEvalMeasureRel_decCallBody
    (nextState currentState : PanSemState α ffi)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (hclock : nextState.clock ≤ currentState.clock) :
    panSemEvalMeasureRel (nextState, body)
      (currentState, Prog.decCall name shape function arguments body) := by
  apply panSemEvalMeasureRel_of_clock_le_cost_lt hclock
  simp [panSemProgFuel] <;> omega

/-- `Dec` evaluates its nested body at the same source clock, and the body has
    strictly less structural cost than the complete command. -/
theorem panSemEvalMeasureRel_decBody
    (state : PanSemState α ffi)
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α) :
    panSemEvalMeasureRel (state, body)
      (state, Prog.dec name shape value body) := by
  apply panSemEvalMeasureRel_of_same_clock_cost_lt rfl
  simp [panSemProgFuel] <;> omega

/-- `While`'s body is a strict subprogram. Its evaluator call uses a lower
    clock when the loop condition is true; the generic clock-decrease lemma
    handles that call even though the body's cost need not be smaller than
    every unrelated caller. -/
theorem panSemEvalMeasureRel_whileBody
    (state : PanSemState α ffi) (condition : Exp α) (body : Prog α) :
    panSemEvalMeasureRel (state, body) (state, Prog.while condition body) := by
  apply panSemEvalMeasureRel_of_same_clock_cost_lt rfl
  simp [panSemProgFuel] <;> omega

end Flapjack
