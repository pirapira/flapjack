import Flapjack.LoopCallEnv

/-!
# Original-domain parity for `loopSem.call_env`

The expected observations are direct HOL-EVAL results from
`scripts/hol-probes/loop_sem_call_env_probe.out`, generated from
`cakeml/pancake/semantics/loopSemScript.sml:177-180`.
-/

namespace Flapjack.Test.LoopCallEnvParity

open Flapjack

def callerState : LoopMachineState Nat :=
  { locals := fun _ => some (.loc 99 0)
    globals := fun _ => some (.word 41)
    memory := fun _ => some (.word 42)
    mdomain := fun _ => true
    shMdomain := fun _ => true
    clock := 17
    code := []
    be := false
    ffi := 23
    baseAddr := 100
    topAddr := 200 }

def calleeArgs : List LoopWordLoc := [.word 5, .word 7]

def originalArgZero : Option LoopWordLoc := some (.word 5)
def originalArgOne : Option LoopWordLoc := some (.word 7)
def originalArgMissing : Option LoopWordLoc := none

#guard (callEnv calleeArgs callerState).locals 0 == originalArgZero
#guard (callEnv calleeArgs callerState).locals 1 == originalArgOne
#guard (callEnv calleeArgs callerState).locals 2 == originalArgMissing
#guard (callEnv calleeArgs callerState).globals 0 == some (.word 41)
#guard (callEnv calleeArgs callerState).memory 0 == some (.word 42)
#guard (callEnv calleeArgs callerState).clock == 17

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop call_env argument zero", (callEnv calleeArgs callerState).locals 0 == originalArgZero),
      ("Loop call_env argument one", (callEnv calleeArgs callerState).locals 1 == originalArgOne),
      ("Loop call_env missing argument", (callEnv calleeArgs callerState).locals 2 == originalArgMissing),
      ("Loop call_env preserves globals", (callEnv calleeArgs callerState).globals 0 == some (.word 41)),
      ("Loop call_env preserves memory", (callEnv calleeArgs callerState).memory 0 == some (.word 42)),
      ("Loop call_env preserves clock", (callEnv calleeArgs callerState).clock == 17) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopCallEnvParity
