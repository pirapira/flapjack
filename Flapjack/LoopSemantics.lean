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

/-! Syntactic approximation of Loop programs that do not update one local.
    Unsupported base-evaluator operations are conservatively treated as
    preserving the local because they cannot produce a result there. -/
def loopNoLocalWrites (name : Nat) : LoopProg α → Bool
  | .assign destination _ => name != destination
  | .primitive destinations _ _ =>
      if name ∈ destinations then false else true
  | .arith (.longMul left right _ _) =>
      if left == right then name != left else true
  | .arith (.longDiv _ _ _ _ _) => true
  | .arith (.div destination _ _) => name != destination
  | .load32 _ destination | .loadByte _ destination => name != destination
  | .seq first second =>
      loopNoLocalWrites name first && loopNoLocalWrites name second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopNoLocalWrites name thenBranch && loopNoLocalWrites name elseBranch
  | .loop _ body _ => loopNoLocalWrites name body
  | .mark body => loopNoLocalWrites name body
  | .locValue destination _ => name != destination
  | .shMem operator _name _address =>
      match operator with
      | .load | .load8 | .load16 | .load32 => name != _name
      | .store | .store8 | .store16 | .store32 => true
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

/-! Exact list-valued counterpart of CakeML's `word_op_def`.  In particular,
    Add/And/Or/Xor fold over every operand and Sub succeeds only for a pair. -/
def evalLoopWordOp [OfNat α 0] [Add α] [Sub α] [AndOp α] [OrOp α]
    [HXor α α α] [Complement α]
    (operator : BinOp) (values : List α) : Option α :=
  match operator with
  | .add => some (values.foldr (fun left right => left + right) 0)
  | .and => some (values.foldr (fun left right => AndOp.and left right)
      (Complement.complement (0 : α)))
  | .or => some (values.foldr (fun left right => OrOp.or left right) 0)
  | .xor => some (values.foldr (fun left right => HXor.hXor left right) 0)
  | .sub =>
      match values with
      | [left, right] => some (left - right)
      | _ => none

def evalLoopShift [ShiftLeft α] [ShiftRight α]
    (operator : Shift) (left right : α) : Option α :=
  match operator with
  | .lsl => some (ShiftLeft.shiftLeft left right)
  | .lsr => some (ShiftRight.shiftRight left right)
  | .asr | .ror => none

/-! Complete source-compatible shift semantics.  The original evaluator is
    retained for the small historical Loop fragment; this sibling adds the
    target-supplied arithmetic-right and rotate-right operations and preserves
    Pancake's invalid shift-count rule. -/
def evalLoopShiftFull [PanShiftWidth α] [ShiftLeft α] [ShiftRight α]
    [ArithmeticShiftRight α] [RotateRightOp α]
    (operator : Shift) (left right : α) : Option α :=
  let amount := PanShiftWidth.amount (α := α) right
  if amount ≠ 0 ∧ PanShiftWidth.width (α := α) ≤ amount then none else
    match operator with
    | .lsl => some (ShiftLeft.shiftLeft left right)
    | .lsr => some (ShiftRight.shiftRight left right)
    | .asr => some (ArithmeticShiftRight.arithmeticShiftRight left right)
    | .ror => some (RotateRightOp.rotateRight left right)

def evalLoopCmp [BEq α] [OfNat α 0] [OfNat α 1] [AndOp α] [PanCmp α]
    (operator : Cmp) (left right : α) : α :=
  match operator with
  | .equal => if left == right then 1 else 0
  | .notEqual => if left == right then 0 else 1
  | .lower => if PanCmp.lower left right then 1 else 0
  | .less => if PanCmp.less left right then 1 else 0
  | .notLower => if PanCmp.lower left right then 0 else 1
  | .notLess => if PanCmp.less left right then 0 else 1
  | .test => if AndOp.and left right == 0 then 1 else 0
  | .notTest => if AndOp.and left right == 0 then 0 else 1

def evalLoopExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α]
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

def evalLoopExpFull [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α] [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [Complement α]
    (state : LoopState α) : LoopExp α → Option α
  | .const value => some value
  | .var name => state.locals name
  | .lookup address => state.globals address
  | .load address => do
      let address ← evalLoopExpFull state address
      state.memory address
  | .op operator expressions => do
      let values ← evalLoopExpListFull state expressions
      evalLoopWordOp operator values
  | .crepOp .mul [left, right] => do
      let left ← evalLoopExpFull state left
      let right ← evalLoopExpFull state right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalLoopExpFull state left
      let right ← evalLoopExpFull state right
      pure (evalLoopCmp operator left right)
  | .shift operator left right => do
      let left ← evalLoopExpFull state left
      let right ← evalLoopExpFull state right
      evalLoopShiftFull operator left right
  | .baseAddr | .topAddr => none
  | _ => none
termination_by expression => sizeOf expression

where
  evalLoopExpListFull [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [PanCmp α] [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
      [Complement α] (state : LoopState α) :
      List (LoopExp α) → Option (List α)
    | [] => some []
    | expression :: expressions => do
        let value ← evalLoopExpFull state expression
        let values ← evalLoopExpListFull state expressions
        pure (value :: values)
    termination_by expressions => sizeOf expressions

/-! Direct source-shaped evaluator for `loopSem$eval_def`.
    Unlike the historical evaluator above, this exposes the two address
    bounds explicitly because they are fields of CakeML's source state. -/
def evalLoopExpSource [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanCmp α] [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [Complement α]
    (state : LoopState α) (baseAddr topAddr : α) : LoopExp α → Option α
  | .const value => some value
  | .var name => state.locals name
  | .lookup address => state.globals address
  | .load address => do
      let address ← evalLoopExpSource state baseAddr topAddr address
      state.memory address
  | .op operator expressions => do
      let values ← evalLoopExpSourceList state baseAddr topAddr expressions
      evalLoopWordOp operator values
  | .shift operator left right => do
      let left ← evalLoopExpSource state baseAddr topAddr left
      let right ← evalLoopExpSource state baseAddr topAddr right
      evalLoopShiftFull operator left right
  | .baseAddr => some baseAddr
  | .topAddr => some topAddr
  | _ => none
termination_by expression => sizeOf expression
where
  evalLoopExpSourceList [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [PanCmp α] [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
      [Complement α] (state : LoopState α) (baseAddr topAddr : α) :
      List (LoopExp α) → Option (List α)
    | [] => some []
    | expression :: expressions => do
        let value ← evalLoopExpSource state baseAddr topAddr expression
        let values ← evalLoopExpSourceList state baseAddr topAddr expressions
        pure (value :: values)
    termination_by expressions => sizeOf expressions

def evalLoopCondition [BEq α] [OfNat α 0] [AndOp α] [PanCmp α]
    (operator : Cmp) (left right : α) : Option Bool :=
  match operator with
  | .equal => some (left == right)
  | .notEqual => some (left != right)
  | .lower => some (PanCmp.lower left right)
  | .less => some (PanCmp.less left right)
  | .notLower => some (!PanCmp.lower left right)
  | .notLess => some (!PanCmp.less left right)
  | .test => some (AndOp.and left right == 0)
  | .notTest => some (AndOp.and left right != 0)

end Flapjack
