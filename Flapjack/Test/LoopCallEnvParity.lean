import Flapjack.LoopCallEnv
import Flapjack.LoopGetVarImm

/-!
# Original-domain parity for `loopSem.call_env`

The expected observations are direct HOL-EVAL results from
`scripts/hol-probes/loop_sem_call_env_probe.out`, generated from
`cakeml/pancake/semantics/loopSemScript.sml:177-180`.
-/

namespace Flapjack.Test.LoopCallEnvParity

open Flapjack

inductive ProbeWord where
  | word (value : Nat)
deriving DecidableEq, Repr

def callerState : LoopState ProbeWord :=
  { locals := fun _ => some (.word 99)
    globals := fun _ => some (.word 41)
    memory := fun _ => some (.word 42) }

def calleeArgs : List ProbeWord := [.word 5, .word 7]

def originalArgZero : Option ProbeWord := some (.word 5)
def originalArgOne : Option ProbeWord := some (.word 7)
def originalArgMissing : Option ProbeWord := none

#guard getVarImm (callEnv calleeArgs callerState) (.reg 0) == originalArgZero
#guard getVarImm (callEnv calleeArgs callerState) (.reg 1) == originalArgOne
#guard getVarImm (callEnv calleeArgs callerState) (.reg 2) == originalArgMissing
#guard (callEnv calleeArgs callerState).globals (.word 0) == some (.word 41)
#guard (callEnv calleeArgs callerState).memory (.word 0) == some (.word 42)

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop call_env argument zero", getVarImm (callEnv calleeArgs callerState) (.reg 0) == originalArgZero),
      ("Loop call_env argument one", getVarImm (callEnv calleeArgs callerState) (.reg 1) == originalArgOne),
      ("Loop call_env missing argument", getVarImm (callEnv calleeArgs callerState) (.reg 2) == originalArgMissing),
      ("Loop call_env preserves globals", (callEnv calleeArgs callerState).globals (.word 0) == some (.word 41)),
      ("Loop call_env preserves memory", (callEnv calleeArgs callerState).memory (.word 0) == some (.word 42)) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopCallEnvParity
