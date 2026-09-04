import Flapjack.CrepToLoop

/-!
Executable semantics for the first Loop fragment.

The HOL semantics carries a large machine state and a rich result datatype.
This port starts with the same control distinctions (normal completion,
return, break, continue, and raise) while keeping the value state abstract:
locals, globals, and memory are finite-map-shaped functions.  Fuel makes loop
execution total and gives later preservation proofs a structurally recursive
induction principle.

The evaluator intentionally returns `none` for operations whose state model is
not ported yet, such as calls, FFI, division, and shared-memory primitives.
Those cases are kept visible rather than silently assigned an unrelated
meaning.
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
      match operator with
      | .equal => pure (if left == right then 1 else 0)
      | .notEqual => pure (if left == right then 0 else 1)
      | .lower => pure (if left < right then 1 else 0)
      | .notLower => pure (if left < right then 0 else 1)
      | _ => none
  | .shift operator left right => do
      let left ← evalLoopExp state left
      let right ← evalLoopExp state right
      evalLoopShift operator left right
  | _ => none
termination_by structural expression

def evalLoopCondition [BEq α] (operator : Cmp) (left right : α) : Option Bool :=
  match operator with
  | .equal => some (left == right)
  | .notEqual => some (left != right)
  | _ => none

mutual
  def evalLoopProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
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
    | fuel + 1, state, .tick => some (.normal state)
    | fuel + 1, state, .mark body => evalLoopProg fuel state body
    | _, _, .fail => none
    | _, _, .primitive _ _ _
    | _, _, .arith (.longDiv _ _ _ _ _)
    | _, _, .arith (.div _ _ _)
    | _, _, .shMem _ _ _
    | _, _, .call _ _ _ _
    | _, _, .ffi _ _ _ _ _ _ => none

  def evalLoopRepeat [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
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

theorem evalLoopProg_skip [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) :
    evalLoopProg 1 state (.skip : LoopProg α) = some (.normal state) := by
  simp [evalLoopProg]

theorem evalLoopProg_assign_const [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (name : Nat) (value : α) :
    evalLoopProg 1 state (.assign name (.const value)) =
      some (.normal { state with locals := updateLoopLocal state.locals name value }) := by
  simp [evalLoopProg, evalLoopExp]

theorem evalLoopCompile_return_const [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
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
