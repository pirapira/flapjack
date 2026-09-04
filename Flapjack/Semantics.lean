import Flapjack.Compile

/-!
Deterministic semantics for the currently supported compiler fragment.

The full Flapjack semantics will add memory, calls, exceptions, and loop state.
This first relation is deliberately small but executable: it is enough to
state semantic preservation for constants and the core return/sequence cases
already lowered by `compileProg`.
-/

namespace Flapjack

def evalPanExp [Add α] (locals : VarName → Option α) (expression : Exp α) : Option α :=
  match expression with
  | .const value => some value
  | .var .local name => locals name
  | .op .add [left, right] => do
      let left ← evalPanExp locals left
      let right ← evalPanExp locals right
      pure (left + right)
  | _ => none
termination_by structural expression

def evalCrepExp [Add α] (locals : Nat → Option α) (expression : CrepExp α) : Option α :=
  match expression with
  | .const value => some value
  | .var name => locals name
  | .op .add [left, right] => do
      let left ← evalCrepExp locals left
      let right ← evalCrepExp locals right
      pure (left + right)
  | _ => none
termination_by structural expression

def evalCrepExps [Add α] (locals : Nat → Option α) : List (CrepExp α) → Option (List α)
  | [] => some []
  | expression :: expressions => do
      let value ← evalCrepExp locals expression
      let values ← evalCrepExps locals expressions
      pure (value :: values)

def evalPanProg [Add α] (locals : VarName → Option α) : Prog α → Option (List α)
  | .skip => some []
  | .return expression => (evalPanExp locals expression).map (fun value => [value])
  | .seq first second => do
      let firstResult ← evalPanProg locals first
      if firstResult.isEmpty then evalPanProg locals second else pure firstResult
  | _ => none

def evalCrepProg [Add α] (locals : Nat → Option α) : CrepProg α → Option (List α)
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

def evalPanStateProg [Add α] (locals : VarName → Option α) :
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

def evalCrepStateProg [Add α] (locals : Nat → Option α) :
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

def evalPanMemExp [BEq α] [Add α]
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
  | _ => none
termination_by expression => sizeOf expression

def evalCrepMemExp [BEq α] [Add α]
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
  | _ => none
termination_by expression => sizeOf expression

def evalPanMemProg [BEq α] [Add α] (locals : VarName → Option α)
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
  | .return value => do
      let value ← evalPanMemExp locals memory value
      pure (locals, memory, [value])
  | .seq first second => do
      let (locals', memory', firstResult) ← evalPanMemProg locals memory first
      if firstResult.isEmpty then evalPanMemProg locals' memory' second
      else pure (locals', memory', firstResult)
  | _ => none

def evalCrepMemProg [BEq α] [Add α] (locals : Nat → Option α)
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
  evalCrepMemExps [BEq α] [Add α] (locals : Nat → Option α)
      (memory : α → Option α) : List (CrepExp α) → Option (List α)
    | [] => some []
    | expression :: expressions => do
        let value ← evalCrepMemExp locals memory expression
        let values ← evalCrepMemExps locals memory expressions
        pure (value :: values)

def evalPanMemResult [BEq α] [Add α] (locals : VarName → Option α)
    (memory : α → Option α) (program : Prog α) : Option (List α) :=
  (evalPanMemProg locals memory program).map (fun result => result.2.2)

def evalCrepMemResult [BEq α] [Add α] (locals : Nat → Option α)
    (memory : α → Option α) (program : CrepProg α) : Option (List α) :=
  (evalCrepMemProg locals memory program).map (fun result => result.2.2)

theorem compile_return_const_preserves_semantics [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (locals : VarName → Option α)
    (compiledLocals : Nat → Option α) (value : α) :
    evalCrepProg compiledLocals (compileProg context (.return (.const value))) =
      evalPanProg locals (.return (.const value)) := by
  simp [compileProg, evalCrepProg, evalCrepExps, evalCrepExp, evalPanProg, evalPanExp,
    compileExp]

theorem compile_skip_preserves_semantics [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (locals : VarName → Option α)
    (compiledLocals : Nat → Option α) :
    evalCrepProg compiledLocals (compileProg context (.skip : Prog α)) =
      evalPanProg locals (.skip : Prog α) := by
  simp [compileProg, evalCrepProg, evalPanProg]

theorem compile_local_var_preserves_semantics [BEq α] [OfNat α 0] [Add α]
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
    [BEq α] [OfNat α 0] [Add α]
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
    updatePanLocal, updateCrepLocal]

theorem compile_store_load_const_preserves_semantics
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
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

end Flapjack
