import Flapjack.LoopStateResult

/-!
# Pancake `loopSem.call_env`

Faithful executable port of `cakeml/pancake/semantics/loopSemScript.sml:177-180`.
Calling a Loop function replaces the local environment with the positional
argument list; the global and memory environments are preserved.
-/

namespace Flapjack

def machineLocalsFromList : List (LoopValue W) → Nat → Option (LoopValue W)
  | values, name => values[name]?

def callEnv (args : List (LoopValue W)) (state : LoopMachineState W F) :
    LoopMachineState W F :=
  { state with locals := machineLocalsFromList args }

@[simp] theorem machineLocalsFromList_get (args : List (LoopValue W)) (name : Nat) :
    machineLocalsFromList args name = args[name]? := by
  rfl

@[simp] theorem callEnv_locals (args : List (LoopValue W)) (state : LoopMachineState W F)
    (name : Nat) :
    (callEnv args state).locals name = args[name]? := by
  rfl

theorem callEnv_globals (args : List (LoopValue W)) (state : LoopMachineState W F) :
    (callEnv args state).globals = state.globals := by
  rfl

theorem callEnv_memory (args : List (LoopValue W)) (state : LoopMachineState W F) :
    (callEnv args state).memory = state.memory := by
  rfl

end Flapjack