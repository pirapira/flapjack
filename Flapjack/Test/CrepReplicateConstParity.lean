import Flapjack.Pancake.Proofs.PanToCrep

/-!
Direct runtime checks against `scripts/hol-probes/crep_replicate_const_probe.out`.
HOL's `pan_to_crepProofScript.sml:evaluate_replicate_const` evaluates a
`REPLICATE n (Const 0w)` argument list to `SOME (REPLICATE n (Word 0w))`.  The
checks below run the production `word_lab`-returning evaluator
`evalCrepRuntimeExpsWordLab` (no post-map) and compare its `PanWordLab` cells
against the recorded HOL rows.
-/

namespace Flapjack.Test.CrepReplicateConstParity

open Flapjack

def noNatMemory : Nat → PanWordLab Nat := fun _ => .word 0
def noNatDomain : Nat → Bool := fun _ => false

/-- Base state with empty locals/globals, matching the probe's `s with locals
:= FEMPTY`. -/
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

def evalConsts (values : List Nat) : Option (List (PanWordLab Nat)) :=
  evalCrepRuntimeExpsWordLab baseState (values.map (fun value => .const value))

/-- `replicate_const_one=SOME [Word 0w]`. -/
def oneGuard : Bool :=
  evalConsts [0] == some [.word 0]

/-- `replicate_const_three=SOME [Word 0w; Word 0w; Word 0w]`. -/
def threeGuard : Bool :=
  evalConsts [0, 0, 0] == some [.word 0, .word 0, .word 0]

/-- `replicate_const_empty=SOME []`. -/
def emptyGuard : Bool :=
  evalConsts [] == some []

/-- `replicate_const_nonzero=SOME [Word 9w; Word 9w]`. -/
def nonzeroGuard : Bool :=
  evalConsts [9, 9] == some [.word 9, .word 9]

def replicateConstGuard : Bool :=
  oneGuard && threeGuard && emptyGuard && nonzeroGuard

#guard replicateConstGuard

/-- The word_lab core instantiated concretely.  This core is untagged (the HOL
tag is withheld pending the arbitrary-runtime-hook mismatch tracked by bead
flapjack-pxn.18.4.3.48.1). -/
example : evalCrepRuntimeExpsWordLab baseState
    (List.replicate 3 (.const (0 : Nat))) = some [.word 0, .word 0, .word 0] :=
  evaluateReplicateConst 3 baseState

/-- Projection: the production evaluator read back through `PanWordLab.word`
equals the word_lab core, for a representative expression. -/
example :
    (evalCrepRuntimeExp baseState (.const (7 : Nat))).map PanWordLab.word =
      evalCrepRuntimeExpWordLab baseState (.const (7 : Nat)) :=
  evalCrepRuntimeExp_wordLab_projection baseState (.const (7 : Nat))

/-- Projection: the production list evaluator read back through `PanWordLab.word`
equals the word_lab list core. -/
example :
    (evalCrepRuntimeExps baseState [.const (1 : Nat), .const (2 : Nat)]).map
        (List.map PanWordLab.word) =
      evalCrepRuntimeExpsWordLab baseState [.const (1 : Nat), .const (2 : Nat)] :=
  evalCrepRuntimeExps_wordLab_projection baseState [.const (1 : Nat), .const (2 : Nat)]

def runChecks : IO Bool := do
  IO.println s!"PASS crep evaluate_replicate_const word_lab shape"
  pure replicateConstGuard

end Flapjack.Test.CrepReplicateConstParity