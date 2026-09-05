import Flapjack.CrepToLoop

/-!
Executable semantics for the first Loop fragment.

The HOL semantics carries a large machine state and a rich result datatype.
This port starts with the same control distinctions (normal completion,
return, break, continue, and raise) while keeping the value state abstract:
locals, globals, and memory are finite-map-shaped functions.  Fuel makes loop
execution total and gives later preservation proofs a structurally recursive
induction principle.

The base evaluator intentionally returns `none` for operations whose state
model is not ported yet, such as calls and FFI. Shared memory is modeled
against the executable memory map below, while call-aware and FFI environment
bridges are provided separately so their external state contracts remain
explicit. Division follows the HOL rule and fails on a zero divisor.
-/

namespace Flapjack

structure LoopState (α : Type u) where
  locals : Nat → Option α
  globals : α → Option α
  memory : α → Option α
inductive LoopResult (α : Type u) where
  | normal (state : LoopState α)
  | returned (state : LoopState α) (values : List α)
  | broke (state : LoopState α) (label : Nat)
  | continued (state : LoopState α) (label : Nat)
  | raised (state : LoopState α) (exception : α)

def loopResultState : LoopResult α → LoopState α
  | .normal state => state
  | .returned state _ => state
  | .broke state _ => state
  | .continued state _ => state
  | .raised state _ => state

theorem option_bind_result_state_globals
    (values : Option β) (continuation : β → Option (LoopResult α))
    (global : α → Option α)
    (hcontinuation : ∀ value result,
      continuation value = some result → (loopResultState result).globals = global)
    (result : LoopResult α)
    (heval : values.bind continuation = some result) :
    (loopResultState result).globals = global := by
  cases hvalues : values with
  | none => simp [hvalues] at heval
  | some value =>
      apply hcontinuation value result
      simpa [hvalues] using heval

/-- Syntactic approximation of Loop programs that do not update globals. -/
def loopNoGlobalWrites : LoopProg α → Bool
  | .setGlobal _ _ => false
  | .seq first second => loopNoGlobalWrites first && loopNoGlobalWrites second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopNoGlobalWrites thenBranch && loopNoGlobalWrites elseBranch
  | .loop _ body _ => loopNoGlobalWrites body
  | .mark body => loopNoGlobalWrites body
  | _ => true

/-- Syntactic approximation of Loop programs that do not update memory. -/
def loopNoMemoryWrites : LoopProg α → Bool
  | .store _ _ | .store32 _ _ | .storeByte _ _ => false
  | .shMem operator _ _ =>
      match operator with
      | .store | .store8 | .store16 | .store32 => false
      | .load | .load8 | .load16 | .load32 => true
  | .seq first second => loopNoMemoryWrites first && loopNoMemoryWrites second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopNoMemoryWrites thenBranch && loopNoMemoryWrites elseBranch
  | .loop _ body _ => loopNoMemoryWrites body
  | .mark body => loopNoMemoryWrites body
  | _ => true

def loopResultValues : LoopResult α → List α
  | .returned _ values => values
  | _ => []
def updateLoopLocal (locals : Nat → Option α) (name : Nat) (value : α) :
    Nat → Option α :=
  fun current => if current = name then some value else locals current

def updateLoopMemory [BEq α] (memory : α → Option α) (address value : α) :
    α → Option α :=
  fun current => if address == current then some value else memory current

def updateLoopGlobal [BEq α] (globals : α → Option α) (address value : α) :
    α → Option α :=
  fun current => if address == current then some value else globals current

def loopReadLocals (locals : Nat → Option α) : List Nat → Option (List α)
  | [] => some []
  | name :: names => do
      let value ← locals name
      let values ← loopReadLocals locals names
      pure (value :: values)

theorem updateLoopLocal_same (locals : Nat → Option α) (name : Nat) (value : α) :
    updateLoopLocal locals name value name = some value := by
  simp [updateLoopLocal]

theorem updateLoopLocal_other (locals : Nat → Option α) (name current : Nat) (value : α)
    (different : current ≠ name) :
    updateLoopLocal locals name value current = locals current := by
  simp [updateLoopLocal, different]

theorem loopReadLocals_append (locals : Nat → Option α) (names rest : List Nat) :
    loopReadLocals locals (names ++ rest) = (do
      let values ← loopReadLocals locals names
      let suffix ← loopReadLocals locals rest
      pure (values ++ suffix)) := by
  induction names with
  | nil => simp [loopReadLocals]
  | cons name names ih =>
      simp [loopReadLocals, ih, List.cons_append, Option.bind_assoc]

def evalLoopBinOp [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    (operator : BinOp) (left right : α) : α :=
  match operator with
  | .add => left + right
  | .sub => left - right
  | .and => AndOp.and left right
  | .or => OrOp.or left right
  | .xor => HXor.hXor left right

def evalLoopShift [ShiftLeft α] [ShiftRight α]
    (operator : Shift) (left right : α) : Option α :=
  match operator with
  | .lsl => some (ShiftLeft.shiftLeft left right)
  | .lsr => some (ShiftRight.shiftRight left right)
  | .asr | .ror => none

def evalLoopCmp [BEq α] [OfNat α 0] [OfNat α 1] [AndOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (operator : Cmp) (left right : α) : α :=
  match operator with
  | .equal => if left == right then 1 else 0
  | .notEqual => if left == right then 0 else 1
  | .lower | .less => if left < right then 1 else 0
  | .notLower | .notLess => if left < right then 0 else 1
  | .test => if AndOp.and left right == 0 then 1 else 0
  | .notTest => if AndOp.and left right == 0 then 0 else 1

def evalLoopExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (expression : LoopExp α) : Option α :=
  match expression with
  | .const value => some value
  | .var name => state.locals name
  | .lookup address => state.globals address
  | .load address => do
      let address ← evalLoopExp state address
      state.memory address
  | .op operator [left, right] => do
      let left ← evalLoopExp state left
      let right ← evalLoopExp state right
      pure (evalLoopBinOp operator left right)
  | .crepOp .mul [left, right] => do
      let left ← evalLoopExp state left
      let right ← evalLoopExp state right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalLoopExp state left
      let right ← evalLoopExp state right
      pure (evalLoopCmp operator left right)
  | .shift operator left right => do
      let left ← evalLoopExp state left
      let right ← evalLoopExp state right
      evalLoopShift operator left right
  | _ => none
termination_by structural expression

def evalLoopCondition [BEq α] [OfNat α 0] [AndOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (operator : Cmp) (left right : α) : Option Bool :=
  match operator with
  | .equal => some (left == right)
  | .notEqual => some (left != right)
  | .lower | .less => some (decide (left < right))
  | .notLower | .notLess => some (decide (¬ left < right))
  | .test => some (AndOp.and left right == 0)
  | .notTest => some (AndOp.and left right != 0)

mutual
  def evalLoopProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      : Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, .skip => some (.normal state)
    | fuel + 1, state, .assign name expression => do
        let value ← evalLoopExp state expression
        pure (.normal { state with
          locals := updateLoopLocal state.locals name value })
    | fuel + 1, state, .arith (.longMul left right sourceLeft sourceRight) =>
        if left = right then do
          let sourceLeft ← state.locals sourceLeft
          let sourceRight ← state.locals sourceRight
          let value := sourceLeft * sourceRight
          pure (.normal { state with
            locals := updateLoopLocal state.locals left value })
        else none
    | fuel + 1, state, .arith (.div destination dividend divisor) => do
        let dividend ← state.locals dividend
        let divisor ← state.locals divisor
        if divisor == 0 then none
        else pure (.normal { state with
          locals := updateLoopLocal state.locals destination (dividend / divisor) })
    | fuel + 1, state, .load32 address destination => do
        let address ← state.locals address
        let value ← state.memory address
        pure (.normal { state with
          locals := updateLoopLocal state.locals destination value })
    | fuel + 1, state, .loadByte address destination => do
        let address ← state.locals address
        let value ← state.memory address
        pure (.normal { state with
          locals := updateLoopLocal state.locals destination value })
    | fuel + 1, state, .store address value => do
        let address ← evalLoopExp state address
        let value ← state.locals value
        pure (.normal { state with
          memory := updateLoopMemory state.memory address value })
    | fuel + 1, state, .setGlobal address value => do
        let value ← evalLoopExp state value
        pure (.normal { state with
          globals := updateLoopGlobal state.globals address value })
    | fuel + 1, state, .store32 address value => do
        let address ← state.locals address
        let value ← state.locals value
        pure (.normal { state with
          memory := updateLoopMemory state.memory address value })
    | fuel + 1, state, .storeByte address value => do
        let address ← state.locals address
        let value ← state.locals value
        pure (.normal { state with
          memory := updateLoopMemory state.memory address value })
    | fuel + 1, state, .seq first second => do
        let result ← evalLoopProg fuel state first
        match result with
        | .normal state => evalLoopProg fuel state second
        | result => pure result
    | fuel + 1, state, .ite operator condition right thenBranch elseBranch _ => do
        let left ← state.locals condition
        let right ← match right with
          | .imm value => some value
          | .reg name => state.locals name
        let choose ← evalLoopCondition operator left right
        if choose then evalLoopProg fuel state thenBranch
        else evalLoopProg fuel state elseBranch
    | fuel + 1, state, .loop _ body _ =>
        evalLoopRepeat fuel state body
    | fuel + 1, state, .break label => some (.broke state label)
    | fuel + 1, state, .continue label => some (.continued state label)
    | fuel + 1, state, .raise exception => do
        let exception ← state.locals exception
        pure (.raised state exception)
    | fuel + 1, state, .return values => do
        let values ← loopReadLocals state.locals values
        pure (.returned state values)
    | fuel + 1, state, .locValue destination source => do
        let value ← state.locals source
        pure (.normal { state with
          locals := updateLoopLocal state.locals destination value })
    | fuel + 1, state, .shMem operator name address => do
        let address ← evalLoopExp state address
        match operator with
        | .load | .load8 | .load16 | .load32 => do
            let value ← state.memory address
            pure (.normal { state with
              locals := updateLoopLocal state.locals name value })
        | .store | .store8 | .store16 | .store32 => do
            let value ← state.locals name
            pure (.normal { state with
              memory := updateLoopMemory state.memory address value })
    | fuel + 1, state, .tick => some (.normal state)
    | fuel + 1, state, .mark body => evalLoopProg fuel state body
    | _, _, .fail => none
    | _, _, .primitive _ _ _
    | _, _, .arith (.longDiv _ _ _ _ _)
    | _, _, .call _ _ _ _
    | _, _, .ffi _ _ _ _ _ _ => none

  def evalLoopRepeat [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      : Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, body => do
        let result ← evalLoopProg fuel state body
        match result with
        | .normal state => evalLoopRepeat fuel state body
        | .continued state 0 => evalLoopRepeat fuel state body
        | .broke state 0 => pure (.normal state)
        | result => pure result
end

/-!
At one unit of fuel, every executable Loop instruction either leaves the
global map unchanged or produces no result.  The syntactic side condition
rules out the one constructor that can update globals.  Stating the result as
a projection equality makes it compose cleanly with `Option.map` and later
fuel-inductive proofs.
-/
theorem evalLoopProg_one_global_projection [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (program : LoopProg α)
    (hprogram : loopNoGlobalWrites program = true) :
    (evalLoopProg 1 state program).map
        (fun result => (loopResultState result).globals) =
      (evalLoopProg 1 state program).map (fun _ => state.globals) := by
  cases program with
  | arith operation =>
      cases operation with
      | longMul left right sourceLeft sourceRight =>
          by_cases h : left = right <;>
            simp [evalLoopProg, loopResultState, Function.comp_def, h]
      | longDiv left right sourceLeft sourceRight quotient =>
          simp [evalLoopProg, loopResultState]
      | div destination dividend divisor =>
          cases hdividend : state.locals dividend with
          | none => simp [evalLoopProg, loopResultState, hdividend]
          | some dividendValue =>
              cases hdivisor : state.locals divisor with
              | none => simp [evalLoopProg, loopResultState, hdividend, hdivisor]
              | some divisorValue =>
                  by_cases hzero : (divisorValue == 0) = true
                  · simp [evalLoopProg, loopResultState, hdividend, hdivisor, hzero]
                  · simp [evalLoopProg, loopResultState, hdividend, hdivisor, hzero]
  | ite operator condition right thenBranch elseBranch live =>
      cases right <;>
        simp [evalLoopProg, loopNoGlobalWrites, loopResultState, Function.comp_def]
  | loop liveIn body liveOut =>
      simp [evalLoopProg, evalLoopRepeat, loopNoGlobalWrites, loopResultState,
        Function.comp_def]
  | shMem operator name address =>
      cases operator <;>
        simp [evalLoopProg, loopNoGlobalWrites, loopResultState, Function.comp_def]
  | setGlobal address value =>
      simp [loopNoGlobalWrites] at hprogram
  | _ =>
      simp [evalLoopProg, loopNoGlobalWrites, loopResultState, Function.comp_def]

theorem evalLoopProg_one_memory_projection [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (program : LoopProg α)
    (hprogram : loopNoMemoryWrites program = true) :
    (evalLoopProg 1 state program).map
        (fun result => (loopResultState result).memory) =
    (evalLoopProg 1 state program).map (fun _ => state.memory) := by
  cases program with
  | arith operation =>
      cases operation with
      | longMul left right sourceLeft sourceRight =>
          by_cases h : left = right
          · subst right
            cases hleft : state.locals sourceLeft with
            | none => simp [evalLoopProg, loopResultState, hleft]
            | some leftValue =>
                cases hright : state.locals sourceRight with
                | none => simp [evalLoopProg, loopResultState, hleft, hright]
                | some rightValue =>
                    simp [evalLoopProg, loopResultState, hleft, hright]
          · simp [evalLoopProg, loopResultState, h]
      | div destination dividend divisor =>
          cases hdividend : state.locals dividend with
          | none => simp [evalLoopProg, loopResultState, hdividend]
          | some dividendValue =>
              cases hdivisor : state.locals divisor with
              | none => simp [evalLoopProg, loopResultState, hdividend, hdivisor]
              | some divisorValue =>
                  by_cases hzero : (divisorValue == 0) = true
                  · simp [evalLoopProg, loopResultState, hdividend, hdivisor, hzero]
                  · simp [evalLoopProg, loopResultState, hdividend, hdivisor, hzero]
      | _ => simp [evalLoopProg, loopResultState, Function.comp_def]
  | ite operator condition right thenBranch elseBranch live =>
      cases right <;>
        simp [evalLoopProg, loopResultState, Function.comp_def]
  | loop liveIn body liveOut =>
      simp [evalLoopProg, evalLoopRepeat, loopResultState, Function.comp_def]
  | store address value =>
      simp [loopNoMemoryWrites] at hprogram
  | store32 address value =>
      simp [loopNoMemoryWrites] at hprogram
  | storeByte address value =>
      simp [loopNoMemoryWrites] at hprogram
  | shMem operator name address =>
      cases operator with
      | load | load8 | load16 | load32 =>
          simp [evalLoopProg, loopNoMemoryWrites, loopResultState,
            Function.comp_def]
      | store | store8 | store16 | store32 =>
          simp [loopNoMemoryWrites] at hprogram
  | _ =>
      simp [evalLoopProg, loopNoMemoryWrites, loopResultState, Function.comp_def]

theorem evalLoopProg_memory_projection [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (program : LoopProg α)
    (hprogram : loopNoMemoryWrites program = true) :
    (evalLoopProg fuel state program).map
        (fun result => (loopResultState result).memory) =
      (evalLoopProg fuel state program).map (fun _ => state.memory) := by
  induction fuel using Nat.strongRecOn generalizing state program with
  | _ fuel ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases program with
          | arith operation =>
              cases operation with
              | longMul left right sourceLeft sourceRight =>
                  by_cases h : left = right
                  · subst right
                    cases hleft : state.locals sourceLeft with
                    | none => simp [evalLoopProg, loopResultState, hleft]
                    | some leftValue =>
                        cases hright : state.locals sourceRight with
                        | none =>
                            simp [evalLoopProg, loopResultState, hleft, hright]
                        | some rightValue =>
                            simp [evalLoopProg, loopResultState, hleft, hright]
                  · simp [evalLoopProg, loopResultState, h]
              | longDiv left right sourceLeft sourceRight quotient =>
                  simp [evalLoopProg, loopResultState]
              | div destination dividend divisor =>
                  cases hdividend : state.locals dividend with
                  | none => simp [evalLoopProg, loopResultState, hdividend]
                  | some dividendValue =>
                      cases hdivisor : state.locals divisor with
                      | none =>
                          simp [evalLoopProg, loopResultState, hdividend, hdivisor]
                      | some divisorValue =>
                          by_cases hzero : (divisorValue == 0) = true
                          · simp [evalLoopProg, loopResultState, hdividend,
                              hdivisor, hzero]
                          · simp [evalLoopProg, loopResultState, hdividend,
                              hdivisor, hzero]
          | store address value =>
              simp [loopNoMemoryWrites] at hprogram
          | store32 address value =>
              simp [loopNoMemoryWrites] at hprogram
          | storeByte address value =>
              simp [loopNoMemoryWrites] at hprogram
          | setGlobal address value =>
              cases hvalue : evalLoopExp state value with
              | none => simp [evalLoopProg, hvalue]
              | some value => simp [evalLoopProg, loopResultState, hvalue]
          | seq first second =>
              have hseq : loopNoMemoryWrites first = true ∧
                  loopNoMemoryWrites second = true := by
                simpa [loopNoMemoryWrites] using hprogram
              cases hfirstEval : evalLoopProg fuel state first with
              | none => simp [evalLoopProg, hfirstEval]
              | some result =>
                  have hresult : (loopResultState result).memory = state.memory := by
                    have h := ih fuel (by omega) state first hseq.1
                    rw [hfirstEval] at h
                    simpa using h
                  cases result with
                  | normal nextState =>
                      have hnext := ih fuel (by omega) nextState second hseq.2
                      have hnormal : nextState.memory = state.memory := by
                        simpa [loopResultState] using hresult
                      simpa [evalLoopProg, hfirstEval, hnormal] using hnext
                  | returned nextState values =>
                      simp [evalLoopProg, hfirstEval, hresult]
                  | broke nextState label =>
                      simp [evalLoopProg, hfirstEval, hresult]
                  | continued nextState label =>
                      simp [evalLoopProg, hfirstEval, hresult]
                  | raised nextState exception =>
                      simp [evalLoopProg, hfirstEval, hresult]
          | ite operator condition right thenBranch elseBranch live =>
              have hbranches : loopNoMemoryWrites thenBranch = true ∧
                  loopNoMemoryWrites elseBranch = true := by
                simpa [loopNoMemoryWrites] using hprogram
              cases right with
              | imm right =>
                  cases hleft : state.locals condition with
                  | none => simp [evalLoopProg, hleft]
                  | some left =>
                      cases hchoose : evalLoopCondition operator left right with
                      | none => simp [evalLoopProg, hleft, hchoose]
                      | some choose =>
                          cases choose with
                          | false =>
                              have hbranch := ih fuel (by omega) state elseBranch hbranches.2
                              simpa [evalLoopProg, hleft, hchoose] using hbranch
                          | true =>
                              have hbranch := ih fuel (by omega) state thenBranch hbranches.1
                              simpa [evalLoopProg, hleft, hchoose] using hbranch
              | reg name =>
                  cases hleft : state.locals condition with
                  | none => simp [evalLoopProg, hleft]
                  | some left =>
                      cases hright : state.locals name with
                      | none => simp [evalLoopProg, hleft, hright]
                      | some right =>
                          cases hchoose : evalLoopCondition operator left right with
                          | none => simp [evalLoopProg, hleft, hright, hchoose]
                          | some choose =>
                              cases choose with
                              | false =>
                                  have hbranch := ih fuel (by omega) state elseBranch hbranches.2
                                  simpa [evalLoopProg, hleft, hright, hchoose] using hbranch
                              | true =>
                                  have hbranch := ih fuel (by omega) state thenBranch hbranches.1
                                  simpa [evalLoopProg, hleft, hright, hchoose] using hbranch
          | loop liveIn body liveOut =>
              have hbody : loopNoMemoryWrites body = true := by
                simpa [loopNoMemoryWrites] using hprogram
              have repeatInvariant : ∀ (bound : Nat),
                  (∀ m, m < bound + 1 → ∀ state : LoopState α,
                    (evalLoopProg m state body).map
                        (fun result => (loopResultState result).memory) =
                      (evalLoopProg m state body).map (fun _ => state.memory)) →
                  ∀ state : LoopState α,
                    (evalLoopRepeat bound state body).map
                        (fun result => (loopResultState result).memory) =
                      (evalLoopRepeat bound state body).map (fun _ => state.memory) := by
                intro bound progIH
                induction bound using Nat.strongRecOn with
                | _ bound ihRepeat =>
                    intro repeatState
                    cases bound with
                    | zero => rfl
                    | succ bound =>
                        cases hbodyEval : evalLoopProg bound repeatState body with
                        | none => simp [evalLoopRepeat, hbodyEval]
                        | some result =>
                            have hresult :
                                (loopResultState result).memory = repeatState.memory := by
                              have h := progIH bound (by omega) repeatState
                              rw [hbodyEval] at h
                              simpa using h
                            have progIH' : ∀ m, m < bound + 1 → ∀ state : LoopState α,
                                (evalLoopProg m state body).map
                                    (fun result => (loopResultState result).memory) =
                                  (evalLoopProg m state body).map (fun _ => state.memory) := by
                              intro m hm
                              exact progIH m (by omega)
                            cases result with
                            | normal nextState =>
                                have hnext := ihRepeat bound (by omega) progIH' nextState
                                have hnormal : nextState.memory = repeatState.memory := by
                                  simpa [loopResultState] using hresult
                                simp [evalLoopRepeat, hbodyEval, hnext, hnormal]
                            | returned nextState values =>
                                simp [evalLoopRepeat, hbodyEval, hresult]
                            | broke nextState label =>
                                cases label with
                                | zero =>
                                    have hnormal : nextState.memory = repeatState.memory := by
                                      simpa [loopResultState] using hresult
                                    simp [evalLoopRepeat, hbodyEval, hnormal, loopResultState]
                                | succ label => simp [evalLoopRepeat, hbodyEval, hresult]
                            | continued nextState label =>
                                cases label with
                                | zero =>
                                    have hnext := ihRepeat bound (by omega) progIH' nextState
                                    have hnormal : nextState.memory = repeatState.memory := by
                                      simpa [loopResultState] using hresult
                                    simp [evalLoopRepeat, hbodyEval, hnext, hnormal]
                                | succ label => simp [evalLoopRepeat, hbodyEval, hresult]
                            | raised nextState exception =>
                                simp [evalLoopRepeat, hbodyEval, hresult]
              simpa [evalLoopProg] using
                repeatInvariant fuel (fun m hm repeatState =>
                  ih m hm repeatState body hbody) state
          | mark body =>
              have hbody : loopNoMemoryWrites body = true := by
                simpa [loopNoMemoryWrites] using hprogram
              exact ih fuel (by omega) state body hbody
          | shMem operator name address =>
              cases operator with
              | load | load8 | load16 | load32 =>
                  cases haddress : evalLoopExp state address with
                  | none => simp [evalLoopProg, haddress]
                  | some address =>
                      cases hvalue : state.memory address with
                      | none => simp [evalLoopProg, haddress, hvalue]
                      | some value =>
                          simp [evalLoopProg, loopResultState, haddress, hvalue]
              | store | store8 | store16 | store32 =>
                  simp [loopNoMemoryWrites] at hprogram
          | _ =>
              simp [evalLoopProg, loopNoMemoryWrites, loopResultState,
                Function.comp_def]

theorem evalLoopProg_result_memory [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (program : LoopProg α)
    (hprogram : loopNoMemoryWrites program = true)
    (result : LoopResult α)
    (heval : evalLoopProg fuel state program = some result) :
    (loopResultState result).memory = state.memory := by
  have hprojection := evalLoopProg_memory_projection fuel state program hprogram
  rw [heval] at hprojection
  simpa using hprojection

theorem evalLoopProg_global_projection [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (program : LoopProg α)
    (hprogram : loopNoGlobalWrites program = true) :
    (evalLoopProg fuel state program).map
        (fun result => (loopResultState result).globals) =
      (evalLoopProg fuel state program).map (fun _ => state.globals) := by
  induction fuel using Nat.strongRecOn generalizing state program with
  | _ fuel ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases program with
          | arith operation =>
              cases operation with
              | longMul left right sourceLeft sourceRight =>
                  by_cases h : left = right <;>
                    simp [evalLoopProg, loopResultState, Function.comp_def, h]
              | longDiv left right sourceLeft sourceRight quotient =>
                  simp [evalLoopProg, loopResultState]
              | div destination dividend divisor =>
                  cases hdividend : state.locals dividend with
                  | none => simp [evalLoopProg, loopResultState, hdividend]
                  | some dividendValue =>
                      cases hdivisor : state.locals divisor with
                      | none => simp [evalLoopProg, loopResultState, hdividend, hdivisor]
                      | some divisorValue =>
                          by_cases hzero : (divisorValue == 0) = true
                          · simp [evalLoopProg, loopResultState, hdividend, hdivisor, hzero]
                          · simp [evalLoopProg, loopResultState, hdividend, hdivisor, hzero]
          | setGlobal address value =>
              simp [loopNoGlobalWrites] at hprogram
          | shMem operator name address =>
              cases operator <;>
                simp [evalLoopProg, loopResultState, Function.comp_def]
          | mark body =>
              have hbody : loopNoGlobalWrites body = true := by
                simpa [loopNoGlobalWrites] using hprogram
              exact ih fuel (by omega) state body hbody
          | loop liveIn body liveOut =>
              have hbody : loopNoGlobalWrites body = true := by
                simpa [loopNoGlobalWrites] using hprogram
              have repeatInvariant : ∀ (bound : Nat),
                  (∀ m, m < bound + 1 → ∀ state : LoopState α,
                    (evalLoopProg m state body).map
                        (fun result => (loopResultState result).globals) =
                      (evalLoopProg m state body).map (fun _ => state.globals)) →
                  ∀ state : LoopState α,
                    (evalLoopRepeat bound state body).map
                        (fun result => (loopResultState result).globals) =
                      (evalLoopRepeat bound state body).map (fun _ => state.globals) := by
                intro bound progIH
                induction bound using Nat.strongRecOn with
                | _ bound ihRepeat =>
                    intro repeatState
                    cases bound with
                    | zero => rfl
                    | succ bound =>
                        cases hbodyEval : evalLoopProg bound repeatState body with
                        | none => simp [evalLoopRepeat, hbodyEval]
                        | some result =>
                            have hresult : (loopResultState result).globals = repeatState.globals := by
                              have h := progIH bound (by omega) repeatState
                              rw [hbodyEval] at h
                              simpa using h
                            have progIH' : ∀ m, m < bound + 1 → ∀ state : LoopState α,
                                (evalLoopProg m state body).map
                                    (fun result => (loopResultState result).globals) =
                                  (evalLoopProg m state body).map (fun _ => state.globals) := by
                              intro m hm
                              exact progIH m (by omega)
                            cases result with
                            | normal nextState =>
                                have hnext := ihRepeat bound (by omega) progIH' nextState
                                have hnormal : nextState.globals = repeatState.globals := by
                                  simpa [loopResultState] using hresult
                                simp [evalLoopRepeat, hbodyEval, hnext, hnormal]
                            | returned nextState values =>
                                simp [evalLoopRepeat, hbodyEval, hresult]
                            | broke nextState label =>
                                cases label with
                                | zero =>
                                    have hnormal : nextState.globals = repeatState.globals := by
                                      simpa [loopResultState] using hresult
                                    simp [evalLoopRepeat, hbodyEval, hnormal, loopResultState]
                                | succ label => simp [evalLoopRepeat, hbodyEval, hresult]
                            | continued nextState label =>
                                cases label with
                                | zero =>
                                    have hnext := ihRepeat bound (by omega) progIH' nextState
                                    have hnormal : nextState.globals = repeatState.globals := by
                                      simpa [loopResultState] using hresult
                                    simp [evalLoopRepeat, hbodyEval, hnext, hnormal]
                                | succ label => simp [evalLoopRepeat, hbodyEval, hresult]
                            | raised nextState exception =>
                                simp [evalLoopRepeat, hbodyEval, hresult]
              simpa [evalLoopProg] using
                repeatInvariant fuel (fun m hm repeatState =>
                  ih m hm repeatState body hbody) state
          | seq first second =>
              have hseq : loopNoGlobalWrites first = true ∧
                  loopNoGlobalWrites second = true := by
                simpa [loopNoGlobalWrites] using hprogram
              cases hfirstEval : evalLoopProg fuel state first with
              | none => simp [evalLoopProg, hfirstEval]
              | some result =>
                  have hresult : (loopResultState result).globals = state.globals := by
                    have h := ih fuel (by omega) state first hseq.1
                    rw [hfirstEval] at h
                    simpa using h
                  cases result with
                  | normal nextState =>
                      have hnext := ih fuel (by omega) nextState second hseq.2
                      have hnormal : nextState.globals = state.globals := by
                        simpa [loopResultState] using hresult
                      simpa [evalLoopProg, hfirstEval, hnormal] using hnext
                  | returned nextState values =>
                      simp [evalLoopProg, hfirstEval, hresult]
                  | broke nextState label =>
                      simp [evalLoopProg, hfirstEval, hresult]
                  | continued nextState label =>
                      simp [evalLoopProg, hfirstEval, hresult]
                  | raised nextState exception =>
                      simp [evalLoopProg, hfirstEval, hresult]
          | ite operator condition right thenBranch elseBranch live =>
              have hbranches : loopNoGlobalWrites thenBranch = true ∧
                  loopNoGlobalWrites elseBranch = true := by
                simpa [loopNoGlobalWrites] using hprogram
              cases right with
              | imm right =>
                  cases hleft : state.locals condition with
                  | none => simp [evalLoopProg, hleft]
                  | some left =>
                      cases hchoose : evalLoopCondition operator left right with
                      | none => simp [evalLoopProg, hleft, hchoose]
                      | some choose =>
                          cases choose with
                          | false =>
                              have hbranch := ih fuel (by omega) state elseBranch hbranches.2
                              simpa [evalLoopProg, hleft, hchoose] using hbranch
                          | true =>
                              have hbranch := ih fuel (by omega) state thenBranch hbranches.1
                              simpa [evalLoopProg, hleft, hchoose] using hbranch
              | reg name =>
                  cases hleft : state.locals condition with
                  | none => simp [evalLoopProg, hleft]
                  | some left =>
                      cases hright : state.locals name with
                      | none => simp [evalLoopProg, hleft, hright]
                      | some right =>
                          cases hchoose : evalLoopCondition operator left right with
                          | none => simp [evalLoopProg, hleft, hright, hchoose]
                          | some choose =>
                              cases choose with
                              | false =>
                                  have hbranch := ih fuel (by omega) state elseBranch hbranches.2
                                  simpa [evalLoopProg, hleft, hright, hchoose] using hbranch
                              | true =>
                                  have hbranch := ih fuel (by omega) state thenBranch hbranches.1
                                  simpa [evalLoopProg, hleft, hright, hchoose] using hbranch
          | _ =>
              simp [evalLoopProg, loopNoGlobalWrites, loopResultState, Function.comp_def]

theorem evalLoopProg_result_globals [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (program : LoopProg α)
    (hprogram : loopNoGlobalWrites program = true)
    (result : LoopResult α)
    (heval : evalLoopProg fuel state program = some result) :
    (loopResultState result).globals = state.globals := by
  have hprojection := evalLoopProg_global_projection fuel state program hprogram
  rw [heval] at hprojection
  simpa using hprojection

def lookupLoopFunction : Nat → List (Nat × List Nat × LoopProg α) →
    Option (List Nat × LoopProg α)
  | _, [] => none
  | label, (candidate, parameters, body) :: functions =>
      if label == candidate then some (parameters, body)
      else lookupLoopFunction label functions

def loopBindParameters (parameters : List Nat) (values : List α)
    (locals : Nat → Option α) : Option (Nat → Option α) :=
  if parameters.length != values.length then none
  else
    some ((parameters.zip values).foldl
      (fun locals (name, value) => updateLoopLocal locals name value) locals)

def loopAssignValues (locals : Nat → Option α) (names : List Nat)
    (values : List α) : Option (Nat → Option α) :=
  if names.length != values.length then none
  else
    some ((names.zip values).foldl
      (fun locals (name, value) => updateLoopLocal locals name value) locals)

abbrev LoopPrimitiveHandler (α : Type u) :=
  PrimOp → List α → Option (List α)

/-!
Loop's primitive boundary is supplied by the target/source environment.  The
ordinary evaluator deliberately remains pure and handler-free; this companion
recurses through the control-flow constructors while delegating only the
primitive instruction itself to the explicit handler.
-/
mutual
  def evalLoopProgWithPrimitive [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
      [ShiftRight α] [LT α]
      [DecidableRel (fun left right : α => left < right)]
      (primitive : LoopPrimitiveHandler α) :
      Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, .primitive destinations operator arguments => do
        let arguments ← loopReadLocals state.locals arguments
        let values ← primitive operator arguments
        let locals ← loopAssignValues state.locals destinations values
        pure (.normal { state with locals := locals })
    | fuel + 1, state, .seq first second => do
        let result ← evalLoopProgWithPrimitive primitive fuel state first
        match result with
        | .normal state => evalLoopProgWithPrimitive primitive fuel state second
        | result => pure result
    | fuel + 1, state, .ite operator condition right thenBranch elseBranch live => do
        let left ← state.locals condition
        let right ← match right with
          | .imm value => some value
          | .reg name => state.locals name
        let choose ← evalLoopCondition operator left right
        if choose then
          evalLoopProgWithPrimitive primitive fuel state thenBranch
        else
          evalLoopProgWithPrimitive primitive fuel state elseBranch
    | fuel + 1, state, .loop liveIn body liveOut =>
        evalLoopRepeatWithPrimitive primitive fuel state body
    | fuel + 1, state, .mark body =>
        evalLoopProgWithPrimitive primitive fuel state body
    | fuel + 1, state, program =>
        evalLoopProg (fuel + 1) state program

  def evalLoopRepeatWithPrimitive [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
      [Mul α] [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
      [ShiftLeft α] [ShiftRight α] [LT α]
      [DecidableRel (fun left right : α => left < right)]
      (primitive : LoopPrimitiveHandler α) :
      Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, body => do
        let result ← evalLoopProgWithPrimitive primitive fuel state body
        match result with
        | .normal state => evalLoopRepeatWithPrimitive primitive fuel state body
        | .continued state 0 => evalLoopRepeatWithPrimitive primitive fuel state body
        | .broke state 0 => pure (.normal state)
        | result => pure result
end

/-!
The call-aware evaluator is mutually recursive with call dispatch. It carries
the function table through callees and handlers, so recursive call graphs are
bounded by the same fuel used for ordinary Loop execution.
-/
mutual
  def evalLoopCall [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (functions : List (Nat × List Nat × LoopProg α)) :
      Nat → LoopState α → Option (List Nat × List Nat) → Option Nat → List Nat →
        Option (Nat × LoopProg α × LoopProg α × List Nat) → Option (LoopResult α)
    | 0, _, _, _, _, _ => none
    | fuel + 1, state, returns, target, arguments, handler => do
        let target ← target
        let (parameters, body) ← lookupLoopFunction target functions
        let values ← loopReadLocals state.locals arguments
        let locals ← loopBindParameters parameters values (fun _ => none)
        let calleeState := { state with locals := locals }
        let result ← evalLoopProgWithFunctions functions fuel calleeState body
        match result with
        | .returned _ values =>
            match returns with
            | none => some (.returned state values)
            | some (names, _) => do
                let locals ← loopAssignValues state.locals names values
                match handler with
                | none => some (.normal { state with locals := locals })
                | some (_, _, normal, _) =>
                    evalLoopProgWithFunctions functions fuel
                      { state with locals := locals } normal
        | .raised _ exception =>
            match handler with
            | none => some (.raised state exception)
            | some (name, exceptionBody, _, _) =>
                evalLoopProgWithFunctions functions fuel
                  { state with locals := updateLoopLocal state.locals name exception }
                  exceptionBody
        | .normal _ => some (.normal state)
        | .broke _ label => some (.broke state label)
        | .continued _ label => some (.continued state label)
    termination_by fuel _ _ _ _ _ => fuel

  def evalLoopProgWithFunctions [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (functions : List (Nat × List Nat × LoopProg α)) :
      Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, .call returns target arguments handler =>
        evalLoopCall functions fuel state returns target arguments handler
    | fuel + 1, state, .seq first second => do
        let result ← evalLoopProgWithFunctions functions fuel state first
        match result with
        | .normal state => evalLoopProgWithFunctions functions fuel state second
        | result => some result
    | fuel + 1, state, .ite operator condition right thenBranch elseBranch _ => do
        let left ← state.locals condition
        let right ← match right with
          | .imm value => some value
          | .reg name => state.locals name
        let choose ← evalLoopCondition operator left right
        if choose then evalLoopProgWithFunctions functions fuel state thenBranch
        else evalLoopProgWithFunctions functions fuel state elseBranch
    | fuel + 1, state, .loop _ body _ =>
        evalLoopRepeatWithFunctions functions fuel state body
    | fuel + 1, state, program => evalLoopProg (fuel + 1) state program
    termination_by fuel _ _ => fuel

  def evalLoopRepeatWithFunctions [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (functions : List (Nat × List Nat × LoopProg α)) :
      Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, body => do
        let result ← evalLoopProgWithFunctions functions fuel state body
        match result with
        | .normal state => evalLoopRepeatWithFunctions functions fuel state body
        | .continued state 0 => evalLoopRepeatWithFunctions functions fuel state body
        | .broke state 0 => some (.normal state)
        | result => some result
    termination_by fuel _ _ => fuel
end

/-!
An explicit host boundary for foreign calls. The handler receives the four
word arguments named by the Loop instruction and may update the Loop state or
reject the call. Control-flow recursion is fuel-bounded; ordinary operations
continue to use the base evaluator above.
-/
mutual
  def evalLoopFfi [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (handler : FunName → α → α → α → α → LoopState α → Option (LoopState α)) :
      Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, .ffi function configuration configurationLength array arrayLength _ => do
        let configuration ← state.locals configuration
        let configurationLength ← state.locals configurationLength
        let array ← state.locals array
        let arrayLength ← state.locals arrayLength
        let state ← handler function configuration configurationLength array arrayLength state
        pure (.normal state)
    | fuel + 1, state, .seq first second => do
        let result ← evalLoopFfi handler fuel state first
        match result with
        | .normal state => evalLoopFfi handler fuel state second
        | result => some result
    | fuel + 1, state, .ite operator condition right thenBranch elseBranch _ => do
        let left ← state.locals condition
        let right ← match right with
          | .imm value => some value
          | .reg name => state.locals name
        let choose ← evalLoopCondition operator left right
        if choose then evalLoopFfi handler fuel state thenBranch
        else evalLoopFfi handler fuel state elseBranch
    | fuel + 1, state, .loop _ body _ => evalLoopFfiRepeat handler fuel state body
    | fuel + 1, state, program => evalLoopProg (fuel + 1) state program
    termination_by fuel _ _ => fuel

  def evalLoopFfiRepeat [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (handler : FunName → α → α → α → α → LoopState α → Option (LoopState α)) :
      Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, body => do
        let result ← evalLoopFfi handler fuel state body
        match result with
        | .normal state => evalLoopFfiRepeat handler fuel state body
        | .continued state 0 => evalLoopFfiRepeat handler fuel state body
        | .broke state 0 => some (.normal state)
        | result => some result
    termination_by fuel _ _ => fuel
end

/-!
Combined call/FFI semantics.  The individual bridges above are useful for
isolated tests, but a compiler correctness proof needs callees to be able to
perform foreign calls and callers to continue after either effect.  This
evaluator keeps both environments explicit while retaining the same fuel
bound and control-result interface.
-/
mutual
  def evalLoopCallWithCallsAndFfi [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (functions : List (Nat × List Nat × LoopProg α))
      (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α)) :
      Nat → LoopState α → Option (List Nat × List Nat) → Option Nat → List Nat →
        Option (Nat × LoopProg α × LoopProg α × List Nat) → Option (LoopResult α)
    | 0, _, _, _, _, _ => none
    | fuel + 1, state, returns, target, arguments, handler => do
        let target ← target
        let (parameters, body) ← lookupLoopFunction target functions
        let values ← loopReadLocals state.locals arguments
        let locals ← loopBindParameters parameters values (fun _ => none)
        let calleeState := { state with locals := locals }
        let result ← evalLoopProgWithCallsAndFfi functions ffiHandler fuel calleeState body
        match result with
        | .returned _ values =>
            match returns with
            | none => some (.returned state values)
            | some (names, _) => do
                let locals ← loopAssignValues state.locals names values
                match handler with
                | none => some (.normal { state with locals := locals })
                | some (_, _, normal, _) =>
                    evalLoopProgWithCallsAndFfi functions ffiHandler fuel
                      { state with locals := locals } normal
        | .raised _ exception =>
            match handler with
            | none => some (.raised state exception)
            | some (name, exceptionBody, _, _) =>
                evalLoopProgWithCallsAndFfi functions ffiHandler fuel
                  { state with locals := updateLoopLocal state.locals name exception }
                  exceptionBody
        | .normal _ => some (.normal state)
        | .broke _ label => some (.broke state label)
        | .continued _ label => some (.continued state label)
    termination_by fuel _ _ _ _ _ => fuel

  def evalLoopProgWithCallsAndFfi [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (functions : List (Nat × List Nat × LoopProg α))
      (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α)) :
      Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, .call returns target arguments handler =>
        evalLoopCallWithCallsAndFfi functions ffiHandler fuel state returns target arguments handler
    | fuel + 1, state, .ffi function configuration configurationLength array arrayLength _ => do
        let configuration ← state.locals configuration
        let configurationLength ← state.locals configurationLength
        let array ← state.locals array
        let arrayLength ← state.locals arrayLength
        let state ← ffiHandler function configuration configurationLength array arrayLength state
        pure (.normal state)
    | fuel + 1, state, .seq first second => do
        let result ← evalLoopProgWithCallsAndFfi functions ffiHandler fuel state first
        match result with
        | .normal state => evalLoopProgWithCallsAndFfi functions ffiHandler fuel state second
        | result => some result
    | fuel + 1, state, .ite operator condition right thenBranch elseBranch _ => do
        let left ← state.locals condition
        let right ← match right with
          | .imm value => some value
          | .reg name => state.locals name
        let choose ← evalLoopCondition operator left right
        if choose then evalLoopProgWithCallsAndFfi functions ffiHandler fuel state thenBranch
        else evalLoopProgWithCallsAndFfi functions ffiHandler fuel state elseBranch
    | fuel + 1, state, .loop _ body _ =>
        evalLoopRepeatWithCallsAndFfi functions ffiHandler fuel state body
    | fuel + 1, state, program => evalLoopProg (fuel + 1) state program
    termination_by fuel _ _ => fuel

  def evalLoopRepeatWithCallsAndFfi [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (functions : List (Nat × List Nat × LoopProg α))
      (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α)) :
      Nat → LoopState α → LoopProg α → Option (LoopResult α)
    | 0, _, _ => none
    | fuel + 1, state, body => do
        let result ← evalLoopProgWithCallsAndFfi functions ffiHandler fuel state body
        match result with
        | .normal state => evalLoopRepeatWithCallsAndFfi functions ffiHandler fuel state body
        | .continued state 0 => evalLoopRepeatWithCallsAndFfi functions ffiHandler fuel state body
        | .broke state 0 => some (.normal state)
        | result => some result
    termination_by fuel _ _ => fuel
end

/-!
Public equations for the combined evaluator.  Keeping these cases as named
lemmas makes the later Loop-to-Word simulation proof independent of the
implementation details of the mutually recursive definitions.
-/
section CombinedSemanticEquations

variable [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
  [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
  [LT α] [DecidableRel (fun left right : α => left < right)]

theorem evalLoopProgWithCallsAndFfi_ffi (functions : List (Nat × List Nat × LoopProg α))
    (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (fuel : Nat) (state : LoopState α) (function : FunName)
    (configuration configurationLength array arrayLength : Nat) (live : List Nat) :
    evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
        (.ffi function configuration configurationLength array arrayLength live) =
      (do
        let configuration ← state.locals configuration
        let configurationLength ← state.locals configurationLength
        let array ← state.locals array
        let arrayLength ← state.locals arrayLength
        let state ← ffiHandler function configuration configurationLength array arrayLength state
        pure (.normal state)) := by
  simp [evalLoopProgWithCallsAndFfi]

theorem evalLoopProgWithCallsAndFfi_call
    (functions : List (Nat × List Nat × LoopProg α))
    (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (fuel : Nat) (state : LoopState α) (returns : Option (List Nat × List Nat))
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × LoopProg α × LoopProg α × List Nat)) :
    evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state
        (.call returns target arguments handler) =
      evalLoopCallWithCallsAndFfi functions ffiHandler fuel state returns target arguments handler := by
  simp [evalLoopProgWithCallsAndFfi]

theorem evalLoopProgWithCallsAndFfi_seq_normal
    (functions : List (Nat × List Nat × LoopProg α))
    (ffiHandler : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (fuel : Nat) (state : LoopState α) (first second : LoopProg α)
    (middle : LoopState α) (result : LoopResult α)
    (hfirst : evalLoopProgWithCallsAndFfi functions ffiHandler fuel state first =
      some (.normal middle))
    (hsecond : evalLoopProgWithCallsAndFfi functions ffiHandler fuel middle second =
      some result) :
    evalLoopProgWithCallsAndFfi functions ffiHandler (fuel + 1) state (.seq first second) =
      some result := by
  simp [evalLoopProgWithCallsAndFfi, hfirst, hsecond]

end CombinedSemanticEquations

theorem evalLoopProg_skip [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) :
    evalLoopProg 1 state (.skip : LoopProg α) = some (.normal state) := by
  simp [evalLoopProg]

theorem evalLoopProg_assign [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (name : Nat) (expression : LoopExp α) (value : α)
    (hvalue : evalLoopExp state expression = some value) :
    evalLoopProg 1 state (.assign name expression) =
      some (.normal { state with locals := updateLoopLocal state.locals name value }) := by
  simp [evalLoopProg, hvalue]

theorem evalLoopExp_var [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (name : Nat) (value : α)
    (hvalue : state.locals name = some value) :
    evalLoopExp state (.var name) = some value := by
  simp [evalLoopExp, hvalue]

theorem evalLoopExp_load [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (address value : α) (expression : LoopExp α)
    (haddress : evalLoopExp state expression = some address)
    (hvalue : state.memory address = some value) :
    evalLoopExp state (.load expression) = some value := by
  simp [evalLoopExp, haddress, hvalue]

theorem evalLoopExp_binOp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (operator : BinOp) (left right : LoopExp α)
    (leftValue rightValue : α)
    (hleft : evalLoopExp state left = some leftValue)
    (hright : evalLoopExp state right = some rightValue) :
    evalLoopExp state (.op operator [left, right]) =
      some (evalLoopBinOp operator leftValue rightValue) := by
  simp [evalLoopExp, hleft, hright, evalLoopBinOp]

theorem evalLoopExp_mul [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (left right : LoopExp α) (leftValue rightValue : α)
    (hleft : evalLoopExp state left = some leftValue)
    (hright : evalLoopExp state right = some rightValue) :
    evalLoopExp state (.crepOp .mul [left, right]) = some (leftValue * rightValue) := by
  simp [evalLoopExp, hleft, hright]

theorem evalLoopExp_shift [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (operator : Shift) (left right : LoopExp α)
    (leftValue rightValue : α) (value : α)
    (hleft : evalLoopExp state left = some leftValue)
    (hright : evalLoopExp state right = some rightValue)
    (hvalue : evalLoopShift operator leftValue rightValue = some value) :
    evalLoopExp state (.shift operator left right) = some value := by
  simp [evalLoopExp, hleft, hright, hvalue]

theorem evalLoopProg_seq_normal [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (first second : LoopProg α)
    (middle : LoopState α) (result : LoopResult α)
    (hfirst : evalLoopProg fuel state first = some (.normal middle))
    (hsecond : evalLoopProg fuel middle second = some result) :
    evalLoopProg (fuel + 1) state (.seq first second) = some result := by
  simp [evalLoopProg, hfirst, hsecond]

theorem evalLoopProg_seq_returned [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (first second : LoopProg α)
    (middle : LoopState α) (values : List α)
    (hfirst : evalLoopProg fuel state first = some (.returned middle values)) :
    evalLoopProg (fuel + 1) state (.seq first second) =
      some (.returned middle values) := by
  simp [evalLoopProg, hfirst]

theorem evalLoopProg_seq_broke [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (first second : LoopProg α)
    (middle : LoopState α) (label : Nat)
    (hfirst : evalLoopProg fuel state first = some (.broke middle label)) :
    evalLoopProg (fuel + 1) state (.seq first second) =
      some (.broke middle label) := by
  simp [evalLoopProg, hfirst]

theorem evalLoopProg_seq_continued [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (first second : LoopProg α)
    (middle : LoopState α) (label : Nat)
    (hfirst : evalLoopProg fuel state first = some (.continued middle label)) :
    evalLoopProg (fuel + 1) state (.seq first second) =
      some (.continued middle label) := by
  simp [evalLoopProg, hfirst]

theorem evalLoopProg_seq_raised [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (first second : LoopProg α)
    (middle : LoopState α) (exception : α)
    (hfirst : evalLoopProg fuel state first = some (.raised middle exception)) :
    evalLoopProg (fuel + 1) state (.seq first second) =
      some (.raised middle exception) := by
  simp [evalLoopProg, hfirst]

theorem evalLoopProg_ite_true [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (operator : Cmp) (condition : Nat)
    (right : RegImm α) (thenBranch elseBranch : LoopProg α) (live : List Nat)
    (leftValue rightValue : α) (result : LoopResult α)
    (hleft : state.locals condition = some leftValue)
    (hright : (match right with
      | .imm value => some value
      | .reg name => state.locals name) = some rightValue)
    (hchoose : evalLoopCondition operator leftValue rightValue = some true)
    (hthen : evalLoopProg fuel state thenBranch = some result) :
    evalLoopProg (fuel + 1) state
        (.ite operator condition right thenBranch elseBranch live) = some result := by
  cases right with
  | imm value =>
      have hvalue : value = rightValue := Option.some.inj hright
      subst hvalue
      simp [evalLoopProg, hleft, hchoose, hthen]
  | reg name =>
      simp [evalLoopProg, hleft, hright, hchoose, hthen]

theorem evalLoopProg_ite_false [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) (operator : Cmp) (condition : Nat)
    (right : RegImm α) (thenBranch elseBranch : LoopProg α) (live : List Nat)
    (leftValue rightValue : α) (result : LoopResult α)
    (hleft : state.locals condition = some leftValue)
    (hright : (match right with
      | .imm value => some value
      | .reg name => state.locals name) = some rightValue)
    (hchoose : evalLoopCondition operator leftValue rightValue = some false)
    ( helse : evalLoopProg fuel state elseBranch = some result) :
    evalLoopProg (fuel + 1) state
        (.ite operator condition right thenBranch elseBranch live) = some result := by
  cases right with
  | imm value =>
      have hvalue : value = rightValue := Option.some.inj hright
      subst hvalue
      simp [evalLoopProg, hleft, hchoose, helse]
  | reg name =>
      simp [evalLoopProg, hleft, hright, hchoose, helse]

theorem evalLoopRepeat_break_zero [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (fuel : Nat) (state : LoopState α) :
    evalLoopRepeat (fuel + 2) state (.break 0) = some (.normal state) := by
  simp [evalLoopRepeat, evalLoopProg]

theorem evalLoopExp_cmp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (operator : Cmp) (left right : LoopExp α)
    (leftValue rightValue : α)
    (hleft : evalLoopExp state left = some leftValue)
    (hright : evalLoopExp state right = some rightValue) :
    evalLoopExp state (.cmp operator left right) =
      some (evalLoopCmp operator leftValue rightValue) := by
  simp [evalLoopExp, hleft, hright]

theorem evalLoopProg_load32 [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (address destination : Nat) (addressValue value : α)
    (haddress : state.locals address = some addressValue)
    (hvalue : state.memory addressValue = some value) :
    evalLoopProg 1 state (.load32 address destination) =
      some (.normal { state with locals := updateLoopLocal state.locals destination value }) := by
  simp [evalLoopProg, haddress, hvalue]

theorem evalLoopProg_loadByte [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (address destination : Nat) (addressValue value : α)
    (haddress : state.locals address = some addressValue)
    (hvalue : state.memory addressValue = some value) :
    evalLoopProg 1 state (.loadByte address destination) =
      some (.normal { state with locals := updateLoopLocal state.locals destination value }) := by
  simp [evalLoopProg, haddress, hvalue]

theorem evalLoopProg_store [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (address : LoopExp α) (value : Nat)
    (addressValue valueValue : α)
    (haddress : evalLoopExp state address = some addressValue)
    (hvalue : state.locals value = some valueValue) :
    evalLoopProg 1 state (.store address value) =
      some (.normal { state with memory := updateLoopMemory state.memory addressValue valueValue }) := by
  simp [evalLoopProg, haddress, hvalue]

theorem evalLoopProg_store32 [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (address value : Nat)
    (addressValue valueValue : α)
    (haddress : state.locals address = some addressValue)
    (hvalue : state.locals value = some valueValue) :
    evalLoopProg 1 state (.store32 address value) =
      some (.normal { state with memory := updateLoopMemory state.memory addressValue valueValue }) := by
  simp [evalLoopProg, haddress, hvalue]

theorem evalLoopProg_storeByte [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (address value : Nat)
    (addressValue valueValue : α)
    (haddress : state.locals address = some addressValue)
    (hvalue : state.locals value = some valueValue) :
    evalLoopProg 1 state (.storeByte address value) =
      some (.normal { state with memory := updateLoopMemory state.memory addressValue valueValue }) := by
  simp [evalLoopProg, haddress, hvalue]

theorem evalLoopProg_div [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (destination dividend divisor : Nat)
    (dividendValue divisorValue : α)
    (hdividend : state.locals dividend = some dividendValue)
    (hdivisor : state.locals divisor = some divisorValue)
    (hnonzero : (divisorValue == 0) = false) :
    evalLoopProg 1 state (.arith (.div destination dividend divisor)) =
      some (.normal { state with
        locals := updateLoopLocal state.locals destination (dividendValue / divisorValue) }) := by
  simp [evalLoopProg, hdividend, hdivisor, hnonzero]

theorem evalLoopProg_setGlobal [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (address : α) (expression : LoopExp α) (value : α)
    (hvalue : evalLoopExp state expression = some value) :
    evalLoopProg 1 state (.setGlobal address expression) =
      some (.normal { state with globals := updateLoopGlobal state.globals address value }) := by
  simp [evalLoopProg, hvalue]

theorem evalLoopProg_locValue [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (destination source : Nat) (value : α)
    (hvalue : state.locals source = some value) :
    evalLoopProg 1 state (.locValue destination source) =
      some (.normal { state with locals := updateLoopLocal state.locals destination value }) := by
  simp [evalLoopProg, hvalue]

theorem evalLoopProg_shMem_load [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (operator : CrepMemOp) (name : Nat) (address : LoopExp α)
    (addressValue value : α)
    (hoperator : operator = .load ∨ operator = .load8 ∨
      operator = .load16 ∨ operator = .load32)
    (haddress : evalLoopExp state address = some addressValue)
    (hvalue : state.memory addressValue = some value) :
    evalLoopProg 1 state (.shMem operator name address) =
      some (.normal { state with locals := updateLoopLocal state.locals name value }) := by
  rcases hoperator with rfl | rfl | rfl | rfl <;>
    simp [evalLoopProg, haddress, hvalue]

theorem evalLoopProg_shMem_store [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (operator : CrepMemOp) (name : Nat) (address : LoopExp α)
    (addressValue value : α)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (haddress : evalLoopExp state address = some addressValue)
    (hvalue : state.locals name = some value) :
    evalLoopProg 1 state (.shMem operator name address) =
      some (.normal { state with memory := updateLoopMemory state.memory addressValue value }) := by
  rcases hoperator with rfl | rfl | rfl | rfl <;>
    simp [evalLoopProg, haddress, hvalue]

theorem evalLoopProg_return [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (names : List Nat) (values : List α)
    (hvalues : loopReadLocals state.locals names = some values) :
    evalLoopProg 1 state (.return names) = some (.returned state values) := by
  simp [evalLoopProg, hvalues]

theorem evalLoopProg_break [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (label : Nat) :
    evalLoopProg 1 state (.break label) = some (.broke state label) := by
  simp [evalLoopProg]

theorem evalLoopProg_continue [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (label : Nat) :
    evalLoopProg 1 state (.continue label) = some (.continued state label) := by
  simp [evalLoopProg]

theorem evalLoopProg_tick [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) :
    evalLoopProg 1 state (.tick) = some (.normal state) := by
  simp [evalLoopProg]

theorem evalLoopProg_assign_const [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (name : Nat) (value : α) :
    evalLoopProg 1 state (.assign name (.const value)) =
      some (.normal { state with locals := updateLoopLocal state.locals name value }) := by
  simp [evalLoopProg, evalLoopExp]

theorem evalLoopCompile_return_const [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (context : LoopContext α) (live : List Nat) (state : LoopState α) (value : α) :
    (evalLoopProg 12 state
      (loopCompileProg context live (.return [(.const value)]))).map loopResultValues =
      some [value] := by
  simp [loopCompileProg, loopCompileExp, loopCompileExp.loopCompileExps,
    loopCompileExps, loopNestedSeq, loopTempNames, loopAssignTemps,
    evalLoopProg, evalLoopExp, loopReadLocals, updateLoopLocal,
    loopResultValues]

end Flapjack
