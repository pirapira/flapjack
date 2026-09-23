import Flapjack.Pancake.Proofs.PanToCrep

/-!
Direct runtime checks against `scripts/hol-probes/crep_replicate_const_probe.out`,
generated from `crepSem$eval` for
`pan_to_crepProofScript.sml:evaluate_replicate_const`.  The production runtime
evaluator returns the bare word carried by a `word_lab` cell, so HOL's
`Word 0w` shape is recovered with `List.map PanWordLab.word` (injective because
`word_lab` has the single constructor `Word`).  The tagged theorem is
`evaluateReplicateConst` in `Flapjack/Pancake/Proofs/PanToCrep.lean`.
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

/-- The tagged theorem instantiates at the probe state. -/
example : evalReplicate 3 = some [.word 0, .word 0, .word 0] :=
  evaluateReplicateConst 3 baseState

def runChecks : IO Bool := do
  if replicateConstGuard then
    IO.println "PASS crep evaluate_replicate_const Word 0w shape"
  else
    IO.println "FAIL crep evaluate_replicate_const Word 0w shape"
  pure replicateConstGuard

end Flapjack.Test.CrepReplicateConstParity