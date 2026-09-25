import Flapjack.Pancake.Semantics.CrepSem.Eval

/-!
# Total HOL-shaped Crep evaluator fragment

This module ports the leaf clauses `Skip`, `Break`, `Continue`, and `Tick`,
plus the `Assign`, `Store`, `If`, `Seq`, `While`, `Return`, `Raise`, and `Dec`
clauses over its restricted recursive syntax, from `crepSem$evaluate_def` to
the 11-field `CrepHolState`. The restricted syntax makes the implemented
domain explicit: this is not a
whole-program evaluator and assigns no behavior to the remaining `CrepProg`
constructors. The result carrier is `option crepSem$result`, so ordinary
completion is `none` and control results retain their HOL constructors.
-/

namespace Flapjack

/-- The four nonrecursive `evaluate_def` forms handled by this first total
    Crep evaluator slice. `toCrepProg` records their exact source constructors. -/
inductive CrepClockLeaf where
  | skip
  | breakAt (label : Nat)
  | continueAt (label : Nat)
  | tick
  deriving DecidableEq, Repr

/-- Embed a clock leaf into the production Crep syntax. -/
def CrepClockLeaf.toCrepProg {width : Nat} :
    CrepClockLeaf → CrepProg (BitVec width)
  | .skip => .skip
  | .breakAt label => .break label
  | .continueAt label => .continue label
  | .tick => .tick

/-- Recursive program fragment for the total clock/control evaluator. Its
    `Assign`, `Store`, and `If` nodes evaluate source `CrepExp` terms in the
    current HOL state, and its `Seq` nodes use the HOL `fix_clock` boundary
    between recursively evaluated programs. `While` uses clock decrease and
    the same `fix_clock` boundary between iterations. Return nodes evaluate
    their expression list in the current HOL state. -/
inductive CrepClockProg (width : Nat) where
  | leaf (value : CrepClockLeaf)
  | raiseException (value : BitVec width)
  | assignLocal (name : Nat) (value : CrepExp (BitVec width))
  | store (destination source : CrepExp (BitVec width))
  | decLocal (name : Nat) (value : CrepExp (BitVec width))
      (body : CrepClockProg width)
  | seq (first second : CrepClockProg width)
  | returnValues (values : List (CrepExp (BitVec width)))
  | ite (condition : CrepExp (BitVec width))
      (thenBranch elseBranch : CrepClockProg width)
  | whileLoop (condition : CrepExp (BitVec width))
      (body : CrepClockProg width)

/-- Embed the restricted recursive syntax into production Crep syntax. -/
def CrepClockProg.toCrepProg {width : Nat} :
  CrepClockProg width → CrepProg (BitVec width)
  | .leaf value => value.toCrepProg
  | .raiseException value => .raise value
  | .assignLocal name value => .assign name value
  | .store destination source => .store destination source
  | .decLocal name value body => .dec name value body.toCrepProg
  | .seq first second => .seq first.toCrepProg second.toCrepProg
  | .returnValues values => .return values
  | .ite condition thenBranch elseBranch =>
      .ite condition thenBranch.toCrepProg elseBranch.toCrepProg
  | .whileLoop condition body => .while condition body.toCrepProg

/-- HOL `exit_loop` on an optional control result: propagate other outcomes,
    while decrementing the nesting label of Break and Continue. -/
def exitCrepClockLoopResult {width : Nat} :
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) →
      Option (CrepResultHOL (BitVec width) FfiFinalEvent)
  | some (.break label) => some (.break (label - 1))
  | some (.continue label) => some (.continue (label - 1))
  | result => result

/-- Total result/state equations for the matching HOL `evaluate_def` leaves,
    `Assign`, `Store`, `If`, `Seq`, `While`, `Return`, `Raise`, and `Dec`. This
    restricted function deliberately has no `Option` fuel wrapper and does
    not depend on `evalCrepRuntimeResult`. -/
def evalCrepClockLeaf {width : Nat} {σ : Type _}
    (leaf : CrepClockLeaf) (state : CrepHolState (BitVec width) σ) :
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) ×
      CrepHolState (BitVec width) σ :=
  match leaf with
  | .skip => (none, state)
  | .breakAt label => (some (.break label), state)
  | .continueAt label => (some (.continue label), state)
  | .tick =>
      if state.clock = 0 then
        (some .timeOut, emptyCrepHolLocals state)
      else
        (none, decCrepHolClock state)

/-- Total recursive evaluator for the implemented source-shaped Crep fragment.
    `Assign` requires an existing destination and uses HOL `set_var` on success;
    expression and destination errors preserve the input state. `If` selects
    the then branch for nonzero words and the else branch for zero. `Seq`
    applies HOL `fix_clock` between recursively evaluated programs. `While`
    recurs only after the HOL clock decrease and handles loop-control labels.
    No fuel,
    partial result, or branch-run assumption is exposed. Remaining constructors
    are not assigned behavior by this restricted evaluator. -/
def evalCrepClockProg [NeZero width] {σ : Type _}
  : CrepClockProg width → CrepHolState (BitVec width) σ →
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) ×
      CrepHolState (BitVec width) σ
  | .leaf value, state => evalCrepClockLeaf value state
  | .raiseException value, state =>
      (some (.exception value), emptyCrepHolLocals state)
  | .assignLocal name value, state =>
      match evalCrepHolExpWordLab state value with
      | none => (some .error, state)
      | some value =>
          match state.locals name with
          | none => (some .error, state)
          | some _ => (none, setCrepHolVarW name value state)
  | .store destination source, state =>
      match evalCrepHolExp state destination, evalCrepHolExp state source with
      | some address, some value =>
          if state.memaddrs address then
            (none, { state with memory := fun current =>
              if current = address then .word value else state.memory current })
          else (some .error, state)
      | _, _ => (some .error, state)
  | .decLocal name value body, state =>
      match evalCrepHolExpWordLab state value with
      | none => (some .error, state)
      | some value =>
          let oldValue := state.locals name
          let (result, bodyState) := evalCrepClockProg body
            (setCrepHolVarW name value state)
          (result, { bodyState with
            locals := resVarW bodyState.locals (name, oldValue) })
  | .seq first second, state =>
      match evalCrepClockProg first state with
      | (none, firstState) =>
          evalCrepClockProg second
            (fixCrepHolClockW state
              ((none : Option (CrepResultHOL (BitVec width) FfiFinalEvent)),
                firstState)).2
      | (some result, firstState) =>
          (some result, (fixCrepHolClockW state (some result, firstState)).2)
  | .returnValues values, state =>
      match values.mapM (evalCrepHolExpWordLab state) with
      | some words => (some (.return words), emptyCrepHolLocals state)
      | none => (some .error, state)
  | .ite condition thenBranch elseBranch, state =>
      match evalCrepHolExp state condition with
      | some value =>
          if value = 0 then evalCrepClockProg elseBranch state
          else evalCrepClockProg thenBranch state
      | none => (some .error, state)
  | .whileLoop condition body, state =>
      match evalCrepHolExp state condition with
      | none => (some .error, state)
      | some value =>
          if value = 0 then (none, state)
          else if hclock : state.clock = 0 then
            (some .timeOut, emptyCrepHolLocals state)
          else
            let decState := decCrepHolClockW state
            let step := evalCrepClockProg body decState
            let fixed := fixCrepHolClockW decState step
            match hfixed : fixed with
            | (none, loopState) =>
                have hbound : loopState.clock ≤ decState.clock := by
                  have h := fixCrepHolClock_IMP_LESS_EQW decState step none loopState
                  exact h (by simpa [fixed] using hfixed)
                have hlt : loopState.clock < state.clock := by
                  simp [decState, decCrepHolClockW] at hbound
                  have hsub : state.clock - 1 < state.clock :=
                    Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega)
                  exact Nat.lt_of_le_of_lt hbound hsub
                evalCrepClockProg (.whileLoop condition body) loopState
            | (some (.continue 0), loopState) =>
                have hbound : loopState.clock ≤ decState.clock := by
                  have h := fixCrepHolClock_IMP_LESS_EQW decState step
                    (some (.continue 0)) loopState
                  exact h (by simpa [fixed] using hfixed)
                have hlt : loopState.clock < state.clock := by
                  simp [decState, decCrepHolClockW] at hbound
                  have hsub : state.clock - 1 < state.clock :=
                    Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega)
                  exact Nat.lt_of_le_of_lt hbound hsub
                evalCrepClockProg (.whileLoop condition body) loopState
            | (some (.break 0), loopState) => (none, loopState)
            | (result, loopState) => (exitCrepClockLoopResult result, loopState)
termination_by program state => (sizeOf program, state.clock)
decreasing_by
  all_goals
    simp_wf
    first | decreasing_trivial | omega
  all_goals
    simp_wf
    omega

theorem evalCrepClockProg_return_success [NeZero width] {σ : Type _}
    (values : List (CrepExp (BitVec width)))
    (words : List (PanWordLab (BitVec width)))
    (state : CrepHolState (BitVec width) σ)
    (heval : values.mapM (evalCrepHolExpWordLab state) = some words) :
    evalCrepClockProg (.returnValues values) state =
      (some (.return words), emptyCrepHolLocals state) := by
  simp [evalCrepClockProg, heval]

theorem evalCrepClockProg_raise [NeZero width] {σ : Type _}
  (value : BitVec width) (state : CrepHolState (BitVec width) σ) :
    evalCrepClockProg (.raiseException value) state =
      (some (.exception value), emptyCrepHolLocals state) := by
  simp [evalCrepClockProg]

theorem evalCrepClockProg_assign_error [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (hvalue : evalCrepHolExpWordLab state value = none) :
    evalCrepClockProg (.assignLocal name value) state = (some .error, state) := by
  simp [evalCrepClockProg, hvalue]

theorem evalCrepClockProg_assign_missing [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (wordLab : PanWordLab (BitVec width))
    (hvalue : evalCrepHolExpWordLab state value = some wordLab)
    (hmissing : state.locals name = none) :
    evalCrepClockProg (.assignLocal name value) state = (some .error, state) := by
  simp [evalCrepClockProg, hvalue, hmissing]

theorem evalCrepClockProg_assign_success [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (wordLab : PanWordLab (BitVec width))
    (hvalue : evalCrepHolExpWordLab state value = some wordLab)
    (hbound : ∃ old, state.locals name = some old) :
    evalCrepClockProg (.assignLocal name value) state =
      (none, setCrepHolVarW name wordLab state) := by
  obtain ⟨old, hold⟩ := hbound
  simp [evalCrepClockProg, hvalue, hold]

theorem evalCrepClockProg_store_address_error [NeZero width] {σ : Type _}
    (destination source : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (haddress : evalCrepHolExp state destination = none) :
    evalCrepClockProg (.store destination source) state = (some .error, state) := by
  simp [evalCrepClockProg, haddress]

theorem evalCrepClockProg_store_value_error [NeZero width] {σ : Type _}
    (destination source : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ) (address : BitVec width)
    (haddress : evalCrepHolExp state destination = some address)
    (hsource : evalCrepHolExp state source = none) :
    evalCrepClockProg (.store destination source) state = (some .error, state) := by
  simp [evalCrepClockProg, haddress, hsource]

theorem evalCrepClockProg_store_domain_error [NeZero width] {σ : Type _}
    (destination source : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (address value : BitVec width)
    (haddress : evalCrepHolExp state destination = some address)
    (hsource : evalCrepHolExp state source = some value)
    (hdomain : state.memaddrs address = false) :
    evalCrepClockProg (.store destination source) state = (some .error, state) := by
  simp [evalCrepClockProg, haddress, hsource, hdomain]

theorem evalCrepClockProg_store_success [NeZero width] {σ : Type _}
    (destination source : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (address value : BitVec width)
    (haddress : evalCrepHolExp state destination = some address)
    (hsource : evalCrepHolExp state source = some value)
    (hdomain : state.memaddrs address = true) :
    evalCrepClockProg (.store destination source) state =
      (none, { state with memory := fun current =>
        if current = address then .word value else state.memory current }) := by
  simp [evalCrepClockProg, haddress, hsource, hdomain]

theorem evalCrepClockProg_dec_error [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (body : CrepClockProg width) (state : CrepHolState (BitVec width) σ)
    (hvalue : evalCrepHolExpWordLab state value = none) :
    evalCrepClockProg (.decLocal name value body) state = (some .error, state) := by
  simp [evalCrepClockProg, hvalue]

theorem evalCrepClockProg_dec_success [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (body : CrepClockProg width) (state : CrepHolState (BitVec width) σ)
    (wordLab : PanWordLab (BitVec width))
    (hvalue : evalCrepHolExpWordLab state value = some wordLab) :
    evalCrepClockProg (.decLocal name value body) state =
      let oldValue := state.locals name
      let (result, bodyState) :=
        evalCrepClockProg body (setCrepHolVarW name wordLab state)
      (result, { bodyState with locals := resVarW bodyState.locals (name, oldValue) }) := by
  simp [evalCrepClockProg, hvalue]

theorem evalCrepClockProg_return_error [NeZero width] {σ : Type _}
    (values : List (CrepExp (BitVec width)))
    (state : CrepHolState (BitVec width) σ)
    (heval : values.mapM (evalCrepHolExpWordLab state) = none) :
    evalCrepClockProg (.returnValues values) state = (some .error, state) := by
  simp [evalCrepClockProg, heval]

theorem evalCrepClockProg_seq_normal [NeZero width] {σ : Type _}
    (first second : CrepClockProg width)
    (state firstState : CrepHolState (BitVec width) σ)
    (hfirst : evalCrepClockProg first state = (none, firstState)) :
    evalCrepClockProg (.seq first second) state =
      evalCrepClockProg second
        (fixCrepHolClockW state
          ((none : Option (CrepResultHOL (BitVec width) FfiFinalEvent)),
            firstState)).2 := by
  simp [evalCrepClockProg, hfirst]

theorem evalCrepClockProg_seq_control [NeZero width] {σ : Type _}
    (first second : CrepClockProg width)
    (state firstState : CrepHolState (BitVec width) σ)
    (result : CrepResultHOL (BitVec width) FfiFinalEvent)
    (hfirst : evalCrepClockProg first state = (some result, firstState)) :
    evalCrepClockProg (.seq first second) state =
      (some result, (fixCrepHolClockW state (some result, firstState)).2) := by
  simp [evalCrepClockProg, hfirst]

theorem evalCrepClockProg_seq_skip_break [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (label : Nat) :
    evalCrepClockProg (.seq (.leaf .skip) (.leaf (.breakAt label))) state =
      (some (.break label), state) := by
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW]

theorem evalCrepClockProg_seq_break_stops [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (label nextLabel : Nat) :
    evalCrepClockProg
        (.seq (.leaf (.breakAt label)) (.leaf (.breakAt nextLabel))) state =
      (some (.break label), state) := by
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW]

theorem evalCrepClockProg_seq_tick_zero [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock = 0) :
    evalCrepClockProg (.seq (.leaf .tick) (.leaf .skip)) state =
      (some .timeOut, emptyCrepHolLocals state) := by
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW,
    emptyCrepHolLocals, hclock]

theorem evalCrepClockProg_seq_tick_positive [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock ≠ 0) :
    evalCrepClockProg (.seq (.leaf .tick) (.leaf .skip)) state =
      (none, decCrepHolClock state) := by
  have hnot : ¬ state.clock < state.clock - 1 := by omega
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW,
    decCrepHolClock, hclock, hnot]

@[simp] theorem evalCrepClockLeaf_skip {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) :
    evalCrepClockLeaf .skip state = (none, state) := rfl

@[simp] theorem evalCrepClockLeaf_break {width : Nat} {σ : Type _}
    (label : Nat) (state : CrepHolState (BitVec width) σ) :
    evalCrepClockLeaf (.breakAt label) state = (some (.break label), state) := rfl

@[simp] theorem evalCrepClockLeaf_continue {width : Nat} {σ : Type _}
    (label : Nat) (state : CrepHolState (BitVec width) σ) :
    evalCrepClockLeaf (.continueAt label) state =
      (some (.continue label), state) := rfl

theorem evalCrepClockLeaf_tick_zero {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock = 0) :
    evalCrepClockLeaf .tick state =
      (some .timeOut, emptyCrepHolLocals state) := by
  simp [evalCrepClockLeaf, hclock]

theorem evalCrepClockLeaf_tick_positive {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock ≠ 0) :
    evalCrepClockLeaf .tick state = (none, decCrepHolClock state) := by
  simp [evalCrepClockLeaf, hclock]

theorem evalCrepClockProg_ite_zero [NeZero width] {σ : Type _}
    (condition : CrepExp (BitVec width)) (thenBranch elseBranch : CrepClockProg width)
    (state : CrepHolState (BitVec width) σ)
    (hcondition : evalCrepHolExp state condition = some 0) :
    evalCrepClockProg (.ite condition thenBranch elseBranch) state =
      evalCrepClockProg elseBranch state := by
  simp [evalCrepClockProg, hcondition]

theorem evalCrepClockProg_ite_nonzero [NeZero width] {σ : Type _}
    (condition : CrepExp (BitVec width)) (thenBranch elseBranch : CrepClockProg width)
    (state : CrepHolState (BitVec width) σ) (value : BitVec width)
    (hcondition : evalCrepHolExp state condition = some value) (hnonzero : value ≠ 0) :
    evalCrepClockProg (.ite condition thenBranch elseBranch) state =
      evalCrepClockProg thenBranch state := by
  simp only [evalCrepClockProg, hcondition]
  by_cases hzero : value = 0
  · exact False.elim (hnonzero hzero)
  · rw [if_neg hzero]

theorem evalCrepClockProg_ite_error [NeZero width] {σ : Type _}
    (condition : CrepExp (BitVec width)) (thenBranch elseBranch : CrepClockProg width)
    (state : CrepHolState (BitVec width) σ)
    (hcondition : evalCrepHolExp state condition = none) :
    evalCrepClockProg (.ite condition thenBranch elseBranch) state =
      (some .error, state) := by
  simp [evalCrepClockProg, hcondition]

end Flapjack
