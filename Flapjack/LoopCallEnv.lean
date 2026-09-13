import Flapjack.LoopSemantics

/-!
# Pancake `loopSem.call_env`

Faithful executable port of `cakeml/pancake/semantics/loopSemScript.sml:177-180`.
Calling a Loop function replaces the local environment with the positional
argument list; the global and memory environments are preserved.
-/

namespace Flapjack

def localsFromList : List α → Nat → Option α
  | values, name => values[name]?

def callEnv (args : List α) (state : LoopState α) : LoopState α :=
  { state with locals := localsFromList args }

@[simp] theorem localsFromList_get (args : List α) (name : Nat) :
    localsFromList args name = args[name]? := by
  rfl

@[simp] theorem callEnv_locals (args : List α) (state : LoopState α) (name : Nat) :
    (callEnv args state).locals name = args[name]? := by
  rfl

theorem callEnv_globals (args : List α) (state : LoopState α) :
    (callEnv args state).globals = state.globals := by
  rfl

theorem callEnv_memory (args : List α) (state : LoopState α) :
    (callEnv args state).memory = state.memory := by
  rfl

end Flapjack
