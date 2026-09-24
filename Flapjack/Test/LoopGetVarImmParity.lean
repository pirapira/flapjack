import Flapjack.LoopGetVarImm
import Flapjack.Pancake.Semantics.LoopSem

/-!
# Original-domain parity for `loopSem.get_var_imm`

The expected observations are direct HOL-EVAL results from
`scripts/hol-probes/loop_sem_get_var_imm_probe.out`, generated from
`cakeml/pancake/semantics/loopSemScript.sml:165-167`.
-/

namespace Flapjack.Test.LoopGetVarImmParity

open Flapjack

def probeState : LoopMachineState Nat :=
  { locals := fun name =>
      if name == 1 then some (.word 5)
      else if name == 3 then some (.loc 9 0)
      else none
    globals := fun _ => none
    memory := fun _ => none
    mdomain := fun _ => true
    shMdomain := fun _ => true
    clock := 10
    code := []
    be := false
    ffi := trivialFfiState Nat 0
    baseAddr := 100
    topAddr := 200 }

def originalRegHit : Option LoopWordLoc := some (.word 5)
def originalRegMiss : Option LoopWordLoc := none
def originalImmWord : Option LoopWordLoc := some (.word 7)
def originalRegLoc : Option LoopWordLoc := some (.loc 9 0)

#guard getVarImm probeState (.reg 1) == originalRegHit
#guard getVarImm probeState (.reg 2) == originalRegMiss
#guard getVarImm probeState (.imm 7) == originalImmWord
#guard getVarImm probeState (.reg 3) == originalRegLoc

/-- The width-indexed exact HOL counterpart of `get_var_imm_def` agrees with
    the generic executable helper (HOL argument order: operand first). -/
example (state : LoopMachineState (BitVec 64)) (operand : RegImm (BitVec 64)) :
    getVarImmHOL operand state = getVarImm state operand :=
  getVarImmHOL_eq_getVarImm operand state

example (state : LoopMachineState (BitVec 64)) :
    getVarImmHOL (.imm (7 : BitVec 64)) state = some (.word 7) := rfl

example (state : LoopMachineState (BitVec 64)) (name : Nat) :
    getVarImmHOL (.reg name) state = state.locals name := rfl

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop get_var_imm register hit", getVarImm probeState (.reg 1) == originalRegHit),
      ("Loop get_var_imm register miss", getVarImm probeState (.reg 2) == originalRegMiss),
      ("Loop get_var_imm immediate", getVarImm probeState (.imm 7) == originalImmWord),
      ("Loop get_var_imm location value", getVarImm probeState (.reg 3) == originalRegLoc) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopGetVarImmParity
