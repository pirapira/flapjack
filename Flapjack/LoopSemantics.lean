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

theorem evalLoopProg_load32 [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : LoopState α) (address destination : Nat) (addressValue value : α)
    (haddress : state.locals address = some addressValue)
    (hvalue : state.memory addressValue = some value) :
    evalLoopProg 1 state (.load32 address destination) =
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
