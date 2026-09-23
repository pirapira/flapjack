import Flapjack.Pancake.Proofs.PanToCrep

/-!
Direct runtime oracle checks against `scripts/hol-probes/crep_replicate_const_probe.out`,
generated from `crepSem$eval` for
`pan_to_crepProofScript.sml:evaluate_replicate_const`.  The production runtime
evaluator currently returns the bare word carried by a `word_lab` cell, so this
is *not* the HOL statement shape yet: the oracle evidence below reconstructs
HOL's `Word 0w` shape with `List.map PanWordLab.word`, and the exact tagged port
is pending bead `flapjack-pxn.18.4.3.48`, which depends on the production
evaluator itself yielding `word_lab` values (bead `flapjack-pxn.18.4.3.43`).
-/

namespace Flapjack.Test.CrepReplicateConstParity

open Flapjack

def noNatMemory : Nat → Option Nat := fun _ => none
def noNatDomain : Nat → Bool := fun _ => false

def baseState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := noNatMemory
    memaddrs := noNatDomain
    shMemaddrs := noNatDomain
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 0
    ffiContext := natCrepRuntimeFfiContext
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 12
    topAddress := 13 }

/-- HOL `Word 0w` reconstruction for a list of evaluated constants. -/
def evalReplicate (count : Nat) : Option (List (PanWordLab Nat)) :=
  (evalCrepRuntimeExps baseState (List.replicate count (.const 0))).map
    (fun values => values.map PanWordLab.word)

/-- `replicate_const_one=SOME [Word 0w]`. -/
def oneGuard : Bool :=
  evalReplicate 1 == some [.word 0]

/-- `replicate_const_three=SOME [Word 0w; Word 0w; Word 0w]`. -/
def threeGuard : Bool :=
  evalReplicate 3 == some [.word 0, .word 0, .word 0]

/-- `replicate_const_empty=SOME []`. -/
def emptyGuard : Bool :=
  evalReplicate 0 == some []

/-- `replicate_const_nonzero=SOME [Word 9w; Word 9w]`. -/
def nonzeroGuard : Bool :=
  (evalCrepRuntimeExps baseState (List.replicate 2 (.const 9))).map
      (fun values => values.map PanWordLab.word) ==
    some [.word 9, .word 9]

def replicateConstGuard : Bool :=
  oneGuard && threeGuard && emptyGuard && nonzeroGuard

#eval replicateConstGuard
#guard replicateConstGuard

/-- The untagged runtime helper instantiates at the probe state. -/
example : evalCrepRuntimeExps baseState (List.replicate 3 (.const 0)) =
    some [0, 0, 0] :=
  evalCrepRuntimeExps_replicate_const 3 baseState

def runChecks : IO Bool := do
  if replicateConstGuard then
    IO.println "PASS crep replicate_const oracle cells (untagged)"
  else
    IO.println "FAIL crep replicate_const oracle cells (untagged)"
  pure replicateConstGuard

end Flapjack.Test.CrepReplicateConstParity