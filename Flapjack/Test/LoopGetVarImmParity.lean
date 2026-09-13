import Flapjack.LoopGetVarImm

/-!
# Original-domain parity for `loopSem.get_var_imm`

The expected observations are direct HOL-EVAL results from
`scripts/hol-probes/loop_sem_get_var_imm_probe.out`, generated from
`cakeml/pancake/semantics/loopSemScript.sml:165-167`.
-/

namespace Flapjack.Test.LoopGetVarImmParity

open Flapjack

inductive ProbeWordLoc where
  | word (value : Nat)
  | loc (identifier offset : Nat)
deriving DecidableEq, Repr

def probeState : LoopState ProbeWordLoc :=
  { locals := fun name =>
      if name == 1 then some (.word 5)
      else if name == 3 then some (.loc 9 0)
      else none
    globals := fun _ => none
    memory := fun _ => none }

def originalRegHit : Option ProbeWordLoc := some (.word 5)
def originalRegMiss : Option ProbeWordLoc := none
def originalImmWord : Option ProbeWordLoc := some (.word 7)
def originalRegLoc : Option ProbeWordLoc := some (.loc 9 0)

#guard getVarImm probeState (.reg 1) == originalRegHit
#guard getVarImm probeState (.reg 2) == originalRegMiss
#guard getVarImm probeState (.imm (.word 7)) == originalImmWord
#guard getVarImm probeState (.reg 3) == originalRegLoc

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop get_var_imm register hit", getVarImm probeState (.reg 1) == originalRegHit),
      ("Loop get_var_imm register miss", getVarImm probeState (.reg 2) == originalRegMiss),
      ("Loop get_var_imm immediate", getVarImm probeState (.imm (.word 7)) == originalImmWord),
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
