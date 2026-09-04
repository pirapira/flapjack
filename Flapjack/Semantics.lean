import Flapjack.Compile

/-!
Deterministic semantics for the currently supported compiler fragment.

The full Flapjack semantics will add memory, calls, exceptions, and loop state.
This first relation is deliberately small but executable: it is enough to
state semantic preservation for constants and the core return/sequence cases
already lowered by `compileProg`.
-/

namespace Flapjack

def evalPanExp [Add α] [Mul α]
    (locals : VarName → Option α) (expression : Exp α) : Option α :=
  match expression with
  | .const value => some value
  | .var .local name => locals name
  | .op .add [left, right] => do
      let left ← evalPanExp locals left
      let right ← evalPanExp locals right
      pure (left + right)
  | .panOp .mul [left, right] => do
      let left ← evalPanExp locals left
      let right ← evalPanExp locals right
      pure (left * right)
  | _ => none
termination_by structural expression

def evalCrepExp [Add α] [Mul α]
    (locals : Nat → Option α) (expression : CrepExp α) : Option α :=
  match expression with
  | .const value => some value
  | .var name => locals name
  | .op .add [left, right] => do
      let left ← evalCrepExp locals left
      let right ← evalCrepExp locals right
      pure (left + right)
  | .crepOp .mul [left, right] => do
      let left ← evalCrepExp locals left
      let right ← evalCrepExp locals right
      pure (left * right)
  | _ => none
termination_by structural expression

def evalCrepExps [Add α] [Mul α] (locals : Nat → Option α) :
    List (CrepExp α) → Option (List α)
  | [] => some []
  | expression :: expressions => do
      let value ← evalCrepExp locals expression
      let values ← evalCrepExps locals expressions
      pure (value :: values)

def evalPanProg [BEq α] [OfNat α 0] [Add α] [Mul α]
    (locals : VarName → Option α) : Prog α → Option (List α)
  | .skip => some []
  | .return expression => (evalPanExp locals expression).map (fun value => [value])
  | .seq first second => do
      let firstResult ← evalPanProg locals first
      if firstResult.isEmpty then evalPanProg locals second else pure firstResult
  | .ite condition thenBranch elseBranch => do
      let condition ← evalPanExp locals condition
      if condition == 0 then evalPanProg locals elseBranch
      else evalPanProg locals thenBranch
  | _ => none

def evalCrepProg [Add α] [Mul α] (locals : Nat → Option α) : CrepProg α → Option (List α)
  | .skip => some []
  | .return expressions => evalCrepExps locals expressions
  | .seq first second => do
      let firstResult ← evalCrepProg locals first
      if firstResult.isEmpty then evalCrepProg locals second else pure firstResult
  | _ => none

def updatePanLocal (locals : VarName → Option α) (name : VarName) (value : α) :
    VarName → Option α :=
  fun current => if current == name then some value else locals current

def updateCrepLocal (locals : Nat → Option α) (name : Nat) (value : α) :
    Nat → Option α :=
  fun current => if current = name then some value else locals current

def evalPanStateProg [Add α] [Mul α] (locals : VarName → Option α) :
    Prog α → Option ((VarName → Option α) × List α)
  | .skip => some (locals, [])
  | .assign .local name value => do
      let value ← evalPanExp locals value
      pure (updatePanLocal locals name value, [])
  | .return value => do
      let value ← evalPanExp locals value
      pure (locals, [value])
  | .seq first second => do
      let (locals', firstResult) ← evalPanStateProg locals first
      if firstResult.isEmpty then evalPanStateProg locals' second
      else pure (locals', firstResult)
  | _ => none

def lookupPanFunction :
    FunName → List (FunName × List VarName × Prog α) →
      Option (List VarName × Prog α)
  | _, [] => none
  | name, (candidate, parameters, body) :: functions =>
      if name == candidate then some (parameters, body)
      else lookupPanFunction name functions

def evalPanExps [Add α] [Mul α] (locals : VarName → Option α) :
    List (Exp α) → Option (List α)
  | [] => some []
  | expression :: expressions => do
      let value ← evalPanExp locals expression
      let values ← evalPanExps locals expressions
      pure (value :: values)

def bindPanParameters (parameters : List VarName) (values : List α) :
    Option (VarName → Option α) :=
  if parameters.length != values.length then none
  else
    some ((parameters.zip values).foldl
      (fun locals (name, value) => updatePanLocal locals name value) (fun _ => none))

/-!
Call-aware executable semantics for the handler-free source fragment.  The
full Pancake semantics has memory, exceptions, clock accounting, and FFI
effects; those are intentionally separate interfaces below.  Keeping this
fragment explicit prevents the source-to-artifact call regression from
silently using the older evaluator, which deliberately rejects calls.
-/
mutual
  def evalPanCallWithCalls [Add α] [Mul α]
      (functions : List (FunName × List VarName × Prog α)) :
      Nat → (VarName → Option α) → Prog α →
        Option ((VarName → Option α) × List α)
    | 0, _, _ => none
    | fuel + 1, locals, .call info function arguments => do
        let values ← evalPanExps locals arguments
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanParameters parameters values
        let result ← evalPanProgWithCalls functions fuel calleeLocals body
        match info with
        | none => pure (locals, result.2)
        | some (none, none) => pure (locals, [])
        | some (some (.local, name), none) =>
            match result.2 with
            | [value] => pure (updatePanLocal locals name value, [])
            | _ => none
        | _ => none
    | _, _, _ => none
    termination_by fuel _ _ => fuel

  def evalPanProgWithCalls [Add α] [Mul α]
      (functions : List (FunName × List VarName × Prog α)) :
      Nat → (VarName → Option α) → Prog α →
        Option ((VarName → Option α) × List α)
    | 0, _, _ => none
    | fuel + 1, locals, .skip => some (locals, [])
    | fuel + 1, locals, .assign .local name value => do
        let value ← evalPanExp locals value
        pure (updatePanLocal locals name value, [])
    | fuel + 1, locals, .return value => do
        let value ← evalPanExp locals value
        pure (locals, [value])
    | fuel + 1, locals, .seq first second => do
        let (locals', firstResult) ←
          evalPanProgWithCalls functions fuel locals first
        if firstResult.isEmpty then
          evalPanProgWithCalls functions fuel locals' second
        else
          pure (locals', firstResult)
    | fuel + 1, locals, .call info function arguments =>
        evalPanCallWithCalls functions fuel locals
          (.call info function arguments)
    | fuel + 1, locals,
        .decCall name _ function arguments body => do
        let (locals', values) ←
          evalPanCallWithCalls functions fuel locals
            (.call (some (some (.local, name), none)) function arguments)
        evalPanProgWithCalls functions fuel locals' body
    | _, _, _ => none
    termination_by fuel _ _ => fuel
end

/-!
Control-result semantics for the same source fragment.  This is the source
counterpart of the Loop and Word handler evaluators: a callee's locals do not
escape, successful return values are assigned to an explicitly local call
destination, and a matching exception handler resumes with the exception
value bound in its handler variable.
-/
inductive PanControlResult (α : Type u) where
  | normal (locals : VarName → Option α)
  | returned (locals : VarName → Option α) (values : List α)
  | raised (locals : VarName → Option α) (exception : ExceptionId) (value : α)

def assignPanCallResult (locals : VarName → Option α)
    (destination : Option (VarKind × VarName)) (values : List α) :
    Option (VarName → Option α) :=
  match destination, values with
  | none, [] => some locals
  | some (.local, name), [value] => some (updatePanLocal locals name value)
  | _, _ => none

mutual
  def evalPanCallWithHandlers [Add α] [Mul α]
      (functions : List (FunName × List VarName × Prog α)) :
      Nat → (VarName → Option α) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        Option (PanControlResult α)
    | 0, _, _, _, _ => none
    | fuel + 1, locals, info, function, arguments => do
        let values ← evalPanExps locals arguments
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanParameters parameters values
        let result ← evalPanProgWithHandlers functions fuel calleeLocals body
        match result with
        | .normal _ => pure (.normal locals)
        | .returned _ values =>
            match info with
            | none => pure (.returned locals values)
            | some (destination, _) => do
                let locals ← assignPanCallResult locals destination values
                pure (.normal locals)
        | .raised _ exception value =>
            match info with
            | some (_, some (caught, handlerVariable, handlerProgram)) =>
                if caught == exception then
                  evalPanProgWithHandlers functions fuel
                    (updatePanLocal locals handlerVariable value) handlerProgram
                else pure (.raised locals exception value)
            | _ => pure (.raised locals exception value)
    termination_by fuel _ _ _ _ => fuel

  def evalPanProgWithHandlers [Add α] [Mul α]
      (functions : List (FunName × List VarName × Prog α)) :
      Nat → (VarName → Option α) → Prog α → Option (PanControlResult α)
    | 0, _, _ => none
    | fuel + 1, locals, .skip => some (.normal locals)
    | fuel + 1, locals, .assign .local name value => do
        let value ← evalPanExp locals value
        pure (.normal (updatePanLocal locals name value))
    | fuel + 1, locals, .seq first second => do
        let result ← evalPanProgWithHandlers functions fuel locals first
        match result with
        | .normal locals => evalPanProgWithHandlers functions fuel locals second
        | result => pure result
    | fuel + 1, locals, .call info function arguments =>
        evalPanCallWithHandlers functions fuel locals info function arguments
    | fuel + 1, locals, .decCall name _ function arguments body => do
        let result ← evalPanCallWithHandlers functions fuel locals
          (some (some (.local, name), none)) function arguments
        match result with
        | .normal locals => evalPanProgWithHandlers functions fuel locals body
        | result => pure result
    | fuel + 1, locals, .raise exception value => do
        let value ← evalPanExp locals value
        pure (.raised locals exception value)
    | fuel + 1, locals, .return value => do
        let value ← evalPanExp locals value
        pure (.returned locals [value])
    | _, _, _ => none
    termination_by fuel _ _ => fuel
end

/-!
The source-level foreign-call boundary.  The host handler is deliberately an
argument of the evaluator: Pancake's FFI effects are not determined by the
pure compiler, so the semantic theorem must quantify over this environment.
-/
abbrev PanFfiHandler (α : Type u) :=
  FunName → α → α → α → α →
    (VarName → Option α) → Option (VarName → Option α)

def evalPanExtCall [Add α] [Mul α]
    (handler : PanFfiHandler α)
    (locals : VarName → Option α) (function : FunName)
    (configuration configurationLength array arrayLength : Exp α) :
    Option (VarName → Option α) := do
  let configuration ← evalPanExp locals configuration
  let configurationLength ← evalPanExp locals configurationLength
  let array ← evalPanExp locals array
  let arrayLength ← evalPanExp locals arrayLength
  handler function configuration configurationLength array arrayLength locals

def evalPanFfiProg [Add α] [Mul α]
    (handler : PanFfiHandler α)
    (locals : VarName → Option α) : Prog α → Option (VarName → Option α)
  | .extCall function configuration configurationLength array arrayLength =>
      evalPanExtCall handler locals function configuration configurationLength array arrayLength
  | .seq first second => do
      let locals ← evalPanFfiProg handler locals first
      evalPanFfiProg handler locals second
  | _ => none

theorem evalPanExtCall_single [Add α] [Mul α]
    (handler : PanFfiHandler α)
    (locals : VarName → Option α) (function : FunName)
    (configuration configurationLength array arrayLength : Exp α) :
    evalPanFfiProg handler locals
      (.extCall function configuration configurationLength array arrayLength) =
      evalPanExtCall handler locals function configuration configurationLength array arrayLength := by
  simp [evalPanFfiProg]

mutual
  def evalPanCallWithCallsAndFfi [Add α] [Mul α]
      (functions : List (FunName × List VarName × Prog α))
      (handler : PanFfiHandler α) :
      Nat → (VarName → Option α) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        Option (PanControlResult α)
    | 0, _, _, _, _ => none
    | fuel + 1, locals, info, function, arguments => do
        let values ← evalPanExps locals arguments
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanParameters parameters values
        let result ← evalPanProgWithCallsAndFfi functions handler fuel calleeLocals body
        match result with
        | .normal _ => pure (.normal locals)
        | .returned _ values =>
            match info with
            | none => pure (.returned locals values)
            | some (destination, _) => do
                let locals ← assignPanCallResult locals destination values
                pure (.normal locals)
        | .raised _ exception value =>
            match info with
            | some (_, some (caught, handlerVariable, handlerProgram)) =>
                if caught == exception then
                  evalPanProgWithCallsAndFfi functions handler fuel
                    (updatePanLocal locals handlerVariable value) handlerProgram
                else pure (.raised locals exception value)
            | _ => pure (.raised locals exception value)
    termination_by fuel _ _ _ _ => fuel

  def evalPanProgWithCallsAndFfi [Add α] [Mul α]
      (functions : List (FunName × List VarName × Prog α))
      (handler : PanFfiHandler α) :
      Nat → (VarName → Option α) → Prog α → Option (PanControlResult α)
    | 0, _, _ => none
    | fuel + 1, locals, .skip => some (.normal locals)
    | fuel + 1, locals, .assign .local name value => do
        let value ← evalPanExp locals value
        pure (.normal (updatePanLocal locals name value))
    | fuel + 1, locals, .seq first second => do
        let result ← evalPanProgWithCallsAndFfi functions handler fuel locals first
        match result with
        | .normal locals => evalPanProgWithCallsAndFfi functions handler fuel locals second
        | result => pure result
    | fuel + 1, locals, .call info function arguments =>
        evalPanCallWithCallsAndFfi functions handler fuel locals info function arguments
    | fuel + 1, locals, .decCall name _ function arguments body => do
        let result ← evalPanCallWithCallsAndFfi functions handler fuel locals
          (some (some (.local, name), none)) function arguments
        match result with
        | .normal locals => evalPanProgWithCallsAndFfi functions handler fuel locals body
        | result => pure result
    | fuel + 1, locals,
        .extCall function configuration configurationLength array arrayLength => do
        let locals ← evalPanExtCall handler locals function configuration
          configurationLength array arrayLength
        pure (.normal locals)
    | fuel + 1, locals, .raise exception value => do
        let value ← evalPanExp locals value
        pure (.raised locals exception value)
    | fuel + 1, locals, .return value => do
        let value ← evalPanExp locals value
        pure (.returned locals [value])
    | _, _, _ => none
    termination_by fuel _ _ => fuel
end

def evalCrepStateProg [Add α] [Mul α] (locals : Nat → Option α) :
    CrepProg α → Option ((Nat → Option α) × List α)
  | .skip => some (locals, [])
  | .assign name value => do
      let value ← evalCrepExp locals value
      pure (updateCrepLocal locals name value, [])
  | .return values => do
      let values ← evalCrepExps locals values
      pure (locals, values)
  | .seq first second => do
      let (locals', firstResult) ← evalCrepStateProg locals first
      if firstResult.isEmpty then evalCrepStateProg locals' second
      else pure (locals', firstResult)
  | _ => none

def updateMemory [BEq α] (memory : α → Option α) (address value : α) : α → Option α :=
  fun current => if current == address then some value else memory current

def evalPanMemExp [BEq α] [Add α] [Mul α]
    (locals : VarName → Option α) (memory : α → Option α) : Exp α → Option α
  | .const value => some value
  | .var .local name => locals name
  | .load _ address | .load32 address | .loadByte address => do
      let address ← evalPanMemExp locals memory address
      memory address
  | .op .add [left, right] => do
      let left ← evalPanMemExp locals memory left
      let right ← evalPanMemExp locals memory right
      pure (left + right)
  | .panOp .mul [left, right] => do
      let left ← evalPanMemExp locals memory left
      let right ← evalPanMemExp locals memory right
      pure (left * right)
  | _ => none
termination_by expression => sizeOf expression

def evalCrepMemExp [BEq α] [Add α] [Mul α]
    (locals : Nat → Option α) (memory : α → Option α) : CrepExp α → Option α
  | .const value => some value
  | .var name => locals name
  | .load address | .load32 address | .loadByte address => do
      let address ← evalCrepMemExp locals memory address
      memory address
  | .op .add [left, right] => do
      let left ← evalCrepMemExp locals memory left
      let right ← evalCrepMemExp locals memory right
      pure (left + right)
  | .crepOp .mul [left, right] => do
      let left ← evalCrepMemExp locals memory left
      let right ← evalCrepMemExp locals memory right
      pure (left * right)
  | _ => none
termination_by expression => sizeOf expression

def evalPanMemProg [BEq α] [Add α] [Mul α] [OfNat α 0]
    (locals : VarName → Option α)
    (memory : α → Option α) : Prog α →
    Option ((VarName → Option α) × (α → Option α) × List α)
  | .skip => some (locals, memory, [])
  | .dec name _ value body => do
      let value ← evalPanMemExp locals memory value
      evalPanMemProg (updatePanLocal locals name value) memory body
  | .assign .local name value => do
      let value ← evalPanMemExp locals memory value
      pure (updatePanLocal locals name value, memory, [])
  | .store address value => do
      let address ← evalPanMemExp locals memory address
      let value ← evalPanMemExp locals memory value
      pure (locals, updateMemory memory address value, [])
  | .store32 address value | .storeByte address value => do
      let address ← evalPanMemExp locals memory address
      let value ← evalPanMemExp locals memory value
      pure (locals, updateMemory memory address value, [])
  | .return value => do
      let value ← evalPanMemExp locals memory value
      pure (locals, memory, [value])
  | .seq first second => do
      let (locals', memory', firstResult) ← evalPanMemProg locals memory first
      if firstResult.isEmpty then evalPanMemProg locals' memory' second
      else pure (locals', memory', firstResult)
  | .ite condition thenBranch elseBranch => do
      let condition ← evalPanMemExp locals memory condition
      if condition == 0 then
        evalPanMemProg locals memory elseBranch
      else
        evalPanMemProg locals memory thenBranch
  | _ => none

def evalCrepMemProg [BEq α] [Add α] [Mul α] (locals : Nat → Option α)
    (memory : α → Option α) : CrepProg α →
    Option ((Nat → Option α) × (α → Option α) × List α)
  | .skip => some (locals, memory, [])
  | .dec name value body => do
      let value ← evalCrepMemExp locals memory value
      evalCrepMemProg (updateCrepLocal locals name value) memory body
  | .assign name value => do
      let value ← evalCrepMemExp locals memory value
      pure (updateCrepLocal locals name value, memory, [])
  | .store address value => do
      let address ← evalCrepMemExp locals memory address
      let value ← evalCrepMemExp locals memory value
      pure (locals, updateMemory memory address value, [])
  | .store32 address value | .storeByte address value => do
      let address ← evalCrepMemExp locals memory address
      let value ← evalCrepMemExp locals memory value
      pure (locals, updateMemory memory address value, [])
  | .storeGlob address value => do
      let value ← evalCrepMemExp locals memory value
      pure (locals, updateMemory memory address value, [])
  | .return values => do
      let values ← evalCrepMemExps locals memory values
      pure (locals, memory, values)
  | .seq first second => do
      let (locals', memory', firstResult) ← evalCrepMemProg locals memory first
      if firstResult.isEmpty then evalCrepMemProg locals' memory' second
      else pure (locals', memory', firstResult)
  | _ => none
  where
  evalCrepMemExps [BEq α] [Add α] [Mul α] (locals : Nat → Option α)
      (memory : α → Option α) : List (CrepExp α) → Option (List α)
    | [] => some []
    | expression :: expressions => do
        let value ← evalCrepMemExp locals memory expression
        let values ← evalCrepMemExps locals memory expressions
        pure (value :: values)

def evalPanMemProgFuelBase [BEq α] [Add α] [Mul α] [OfNat α 0]
    (fuel : Nat) (locals : VarName → Option α) (memory : α → Option α) :
    Prog α → Option ((VarName → Option α) × (α → Option α) × List α) :=
  fun program =>
    match fuel, program with
    | _, .skip => some (locals, memory, [])
    | 0, _ => none
    | fuel + 1, .dec name _ value body => do
        let value ← evalPanMemExp locals memory value
        evalPanMemProgFuelBase fuel (updatePanLocal locals name value) memory body
    | fuel + 1, .assign .local name value => do
        let value ← evalPanMemExp locals memory value
        pure (updatePanLocal locals name value, memory, [])
    | fuel + 1, .store address value => do
        let address ← evalPanMemExp locals memory address
        let value ← evalPanMemExp locals memory value
        pure (locals, updateMemory memory address value, [])
    | fuel + 1, .store32 address value | fuel + 1, .storeByte address value => do
        let address ← evalPanMemExp locals memory address
        let value ← evalPanMemExp locals memory value
        pure (locals, updateMemory memory address value, [])
    | fuel + 1, .return value => do
        let value ← evalPanMemExp locals memory value
        pure (locals, memory, [value])
    | fuel + 1, .seq first second => do
        let (locals', memory', firstResult) ←
          evalPanMemProgFuelBase fuel locals memory first
        if firstResult.isEmpty then
          evalPanMemProgFuelBase fuel locals' memory' second
        else
          pure (locals', memory', firstResult)
    | fuel + 1, .ite condition thenBranch elseBranch => do
        let condition ← evalPanMemExp locals memory condition
        if condition == 0 then
          evalPanMemProgFuelBase fuel locals memory elseBranch
        else
          evalPanMemProgFuelBase fuel locals memory thenBranch
    | fuel + 1, .while _ _ => none
    | _, _ => none
termination_by fuel => fuel

mutual
  def evalPanMemProgFuel [BEq α] [Add α] [Mul α] [OfNat α 0]
      : Nat → (VarName → Option α) → (α → Option α) → Prog α →
        Option ((VarName → Option α) × (α → Option α) × List α)
    | _, locals, memory, .skip => some (locals, memory, [])
    | 0, _, _, _ => none
    | fuel + 1, locals, memory, .dec name _ value body => do
        let value ← evalPanMemExp locals memory value
        evalPanMemProgFuel fuel (updatePanLocal locals name value) memory body
    | fuel + 1, locals, memory, .seq first second => do
        let (locals', memory', firstResult) ←
          evalPanMemProgFuel fuel locals memory first
        if firstResult.isEmpty then
          evalPanMemProgFuel fuel locals' memory' second
        else
          pure (locals', memory', firstResult)
    | fuel + 1, locals, memory, .ite condition thenBranch elseBranch => do
        let condition ← evalPanMemExp locals memory condition
        if condition == 0 then
          evalPanMemProgFuel fuel locals memory elseBranch
        else
          evalPanMemProgFuel fuel locals memory thenBranch
    | fuel + 1, locals, memory, .while condition body =>
        evalPanMemWhileFuel fuel locals memory condition body
    | fuel, locals, memory, program => evalPanMemProgFuelBase fuel locals memory program
    termination_by fuel => fuel

  def evalPanMemWhileFuel [BEq α] [Add α] [Mul α] [OfNat α 0]
      : Nat → (VarName → Option α) → (α → Option α) → Exp α → Prog α →
        Option ((VarName → Option α) × (α → Option α) × List α)
    | 0, locals, memory, condition, _ => do
        let conditionValue ← evalPanMemExp locals memory condition
        if conditionValue == 0 then some (locals, memory, []) else none
    | fuel + 1, locals, memory, condition, body => do
        let conditionValue ← evalPanMemExp locals memory condition
        if conditionValue == 0 then some (locals, memory, [])
        else
          let result ← evalPanMemProgFuel fuel locals memory body
          if result.2.2.isEmpty then
            evalPanMemWhileFuel fuel result.1 result.2.1 condition body
          else
            some result
    termination_by fuel _ _ _ _ => fuel
end

theorem evalPanMemProgFuel_while_const_zero [BEq α] [LawfulBEq α] [Add α]
    [Mul α] [OfNat α 0]
    (fuel : Nat) (locals : VarName → Option α) (memory : α → Option α)
    (body : Prog α) :
    evalPanMemProgFuel (fuel + 1) locals memory (.while (.const (0 : α)) body) =
      some (locals, memory, []) := by
  cases fuel <;>
    simp [evalPanMemProgFuel, evalPanMemWhileFuel, evalPanMemExp]

def evalCrepMemProgFuel [BEq α] [Add α] [Mul α] [OfNat α 0]
    (fuel : Nat) (locals : Nat → Option α) (memory : α → Option α) :
    CrepProg α → Option ((Nat → Option α) × (α → Option α) × List α) :=
  fun program =>
    match fuel, program with
    | _, .skip => some (locals, memory, [])
    | 0, _ => none
    | fuel + 1, .dec name value body => do
        let value ← evalCrepMemExp locals memory value
        evalCrepMemProgFuel fuel (updateCrepLocal locals name value) memory body
    | fuel + 1, .assign name value => do
        let value ← evalCrepMemExp locals memory value
        pure (updateCrepLocal locals name value, memory, [])
    | fuel + 1, .store address value => do
        let address ← evalCrepMemExp locals memory address
        let value ← evalCrepMemExp locals memory value
        pure (locals, updateMemory memory address value, [])
    | fuel + 1, .store32 address value | fuel + 1, .storeByte address value => do
        let address ← evalCrepMemExp locals memory address
        let value ← evalCrepMemExp locals memory value
        pure (locals, updateMemory memory address value, [])
    | fuel + 1, .storeGlob address value => do
        let value ← evalCrepMemExp locals memory value
        pure (locals, updateMemory memory address value, [])
    | fuel + 1, .return values => do
        let values ← evalCrepMemProg.evalCrepMemExps locals memory values
        pure (locals, memory, values)
    | fuel + 1, .seq first second => do
        let (locals', memory', firstResult) ←
          evalCrepMemProgFuel fuel locals memory first
        if firstResult.isEmpty then
          evalCrepMemProgFuel fuel locals' memory' second
        else
          pure (locals', memory', firstResult)
    | fuel + 1, .ite condition thenBranch elseBranch => do
        let condition ← evalCrepMemExp locals memory condition
        if condition == 0 then
          evalCrepMemProgFuel fuel locals memory elseBranch
        else
          evalCrepMemProgFuel fuel locals memory thenBranch
    | fuel + 1, .while _ _ => none
    | _, _ => none
termination_by fuel => fuel

def evalPanMemResult [BEq α] [Add α] [Mul α] [OfNat α 0]
    (locals : VarName → Option α)
    (memory : α → Option α) (program : Prog α) : Option (List α) :=
  (evalPanMemProg locals memory program).map (fun result => result.2.2)

def evalCrepMemResult [BEq α] [Add α] [Mul α] (locals : Nat → Option α)
    (memory : α → Option α) (program : CrepProg α) : Option (List α) :=
  (evalCrepMemProg locals memory program).map (fun result => result.2.2)

theorem compile_return_const_preserves_semantics [BEq α] [OfNat α 0] [Add α] [Mul α]
    (context : CompileContext α) (locals : VarName → Option α)
    (compiledLocals : Nat → Option α) (value : α) :
    evalCrepProg compiledLocals (compileProg context (.return (.const value))) =
      evalPanProg locals (.return (.const value)) := by
  simp [compileProg, evalCrepProg, evalCrepExps, evalCrepExp, evalPanProg, evalPanExp,
    compileExp]

theorem compile_skip_preserves_semantics [BEq α] [OfNat α 0] [Add α] [Mul α]
    (context : CompileContext α) (locals : VarName → Option α)
    (compiledLocals : Nat → Option α) :
    evalCrepProg compiledLocals (compileProg context (.skip : Prog α)) =
      evalPanProg locals (.skip : Prog α) := by
  simp [compileProg, evalCrepProg, evalPanProg]

theorem compile_local_var_preserves_semantics [BEq α] [OfNat α 0] [Add α] [Mul α]
    (context : CompileContext α) (name : VarName) (slot : Nat)
    (lookup : lookupInfo name context.vars = some (.one, [slot]))
    (locals : VarName → Option α) (compiledLocals : Nat → Option α)
    (environment_agrees : compiledLocals slot = locals name) :
    evalCrepExps compiledLocals (compileExp context (.var .local name)).1 =
      (evalPanExp locals (.var .local name)).map (fun value => [value]) := by
  rw [compileExp_local_var context name .one [slot] lookup]
  cases h : locals name <;>
    simp [evalCrepExps, evalCrepExp, evalPanExp, environment_agrees, h]

theorem compile_local_assign_return_const_preserves_semantics
    [BEq α] [OfNat α 0] [Add α] [Mul α]
    (context : CompileContext α) (name : VarName) (slot : Nat) (value : α)
    (lookup : lookupInfo name context.vars = some (.one, [slot]))
    (locals : VarName → Option α) (compiledLocals : Nat → Option α) :
    (evalCrepStateProg compiledLocals
        (compileProg context
          (.seq (.assign .local name (.const value))
            (.return (.var .local name))))).map Prod.snd =
      (evalPanStateProg locals
        (.seq (.assign .local name (.const value))
          (.return (.var .local name)))).map Prod.snd := by
  simp [compileProg, compileExp, crepNestedSeq, lookup,
    compileExp_local_var context name .one [slot] lookup,
    evalCrepStateProg, evalPanStateProg, evalCrepExp, evalCrepExps, evalPanExp,
    updatePanLocal, updateCrepLocal, distinctLists]

theorem compile_store_load_const_preserves_semantics
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α] [Mul α]
    (context : CompileContext α) (address value : α)
    (locals : VarName → Option α) (compiledLocals : Nat → Option α)
    (memory : α → Option α) :
    evalCrepMemResult compiledLocals memory
        (compileProg context
          (.seq (.store (.const address) (.const value))
            (.return (.load .one (.const address))))) =
      evalPanMemResult locals memory
        (.seq (.store (.const address) (.const value))
          (.return (.load .one (.const address)))) := by
  simp [compileProg, compileExp, freshNames, nestedDecs, stores, crepNestedSeq,
    evalCrepMemResult, evalPanMemResult, evalCrepMemProg, evalPanMemProg,
    evalCrepMemProg.evalCrepMemExps,
    evalCrepMemExp, evalPanMemExp, updateMemory, updateCrepLocal, loadShape]

theorem compile_store32_load32_const_preserves_semantics
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α] [Mul α]
    (context : CompileContext α) (address value : α)
    (locals : VarName → Option α) (compiledLocals : Nat → Option α)
    (memory : α → Option α) :
    evalCrepMemResult compiledLocals memory
        (compileProg context
          (.seq (.store32 (.const address) (.const value))
            (.return (.load32 (.const address))))) =
      evalPanMemResult locals memory
        (.seq (.store32 (.const address) (.const value))
          (.return (.load32 (.const address)))) := by
  simp [compileProg, compileExp, evalCrepMemResult, evalPanMemResult,
    evalCrepMemProg, evalPanMemProg, evalCrepMemProg.evalCrepMemExps,
    evalCrepMemExp, evalPanMemExp, updateMemory, updateCrepLocal]

theorem compile_storeByte_loadByte_const_preserves_semantics
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α] [Mul α]
    (context : CompileContext α) (address value : α)
    (locals : VarName → Option α) (compiledLocals : Nat → Option α)
    (memory : α → Option α) :
    evalCrepMemResult compiledLocals memory
        (compileProg context
          (.seq (.storeByte (.const address) (.const value))
            (.return (.loadByte (.const address))))) =
      evalPanMemResult locals memory
        (.seq (.storeByte (.const address) (.const value))
          (.return (.loadByte (.const address)))) := by
  simp [compileProg, compileExp, evalCrepMemResult, evalPanMemResult,
    evalCrepMemProg, evalPanMemProg, evalCrepMemProg.evalCrepMemExps,
    evalCrepMemExp, evalPanMemExp, updateMemory, updateCrepLocal]

theorem compile_ite_const_preserves_semantics
    [BEq α] [OfNat α 0] [Add α] [Mul α]
    (fuel : Nat) (context : CompileContext α)
    (condition thenValue elseValue : α)
    (locals : VarName → Option α) (compiledLocals : Nat → Option α)
    (memory : α → Option α) :
    (evalCrepMemProgFuel fuel compiledLocals memory
        (compileProg context
          (.ite (.const condition)
            (.return (.const thenValue))
            (.return (.const elseValue))))).map (fun result => result.2.2) =
      (evalPanMemProgFuel fuel locals memory
        (.ite (.const condition)
          (.return (.const thenValue))
          (.return (.const elseValue)))).map (fun result => result.2.2) := by
  cases fuel with
  | zero =>
      simp [compileProg, compileExp, evalCrepMemProgFuel, evalPanMemProgFuel]
  | succ fuel =>
      simp [compileProg, compileExp, evalCrepMemProgFuel, evalPanMemProgFuel,
        evalCrepMemExp, evalPanMemExp]
      split <;>
        cases fuel <;>
          simp [evalCrepMemProgFuel, evalPanMemProgFuel,
            evalPanMemProgFuelBase,
            evalCrepMemProg.evalCrepMemExps, evalCrepMemExp, evalCrepExp,
            evalPanMemExp]

theorem compile_pan_mul_const_preserves_semantics
    [BEq α] [OfNat α 0] [Add α] [Mul α]
    (context : CompileContext α) (left right : α)
    (locals : VarName → Option α) (compiledLocals : Nat → Option α) :
    evalCrepProg compiledLocals
        (compileProg context
          (.return (.panOp .mul [.const left, .const right]))) =
      evalPanProg locals
        (.return (.panOp .mul [.const left, .const right])) := by
  simp [compileProg, compileExp, compileExp.compileExpList, cexpHeads,
    compilePanOp, evalCrepProg, evalCrepExps, evalCrepExp, evalPanProg,
    evalPanExp]

end Flapjack
