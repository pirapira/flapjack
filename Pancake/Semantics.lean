import Pancake.Compile

/-!
Deterministic semantics for the currently supported compiler fragment.

The full Pancake semantics will add memory, calls, exceptions, and loop state.
This first relation is deliberately small but executable: it is enough to
state semantic preservation for constants and the core return/sequence cases
already lowered by `compileProg`.
-/

namespace Pancake

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

end Pancake
