import Flapjack.PanItreeEvaluate

/-!
# Parity checks for Pancake `itree_evaluate_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_evaluate_probe.out` is generated from
`pan_itreeSemScript.sml:582-594`.  Lean checks cover normal and FFI-terminal
mapping and preservation of silent/visible tree structure.
-/

namespace Flapjack.Test.PanItreeEvaluateParity

open Flapjack

def normalTree : PanFfiTree (PanItreeEvaluateTerminal Nat Nat) :=
  .ret (.inr (some 7, 3))

def errorTree : PanFfiTree (PanItreeEvaluateTerminal Nat Nat) :=
  .ret (.inl (.inl .failed))

def tauTree : PanFfiTree (PanItreeEvaluateTerminal Nat Nat) :=
  .tau normalTree

def observeNormal : Bool :=
  match panItreeEvaluate 3 normalTree with
  | .ret (.result (some 7) 3) => true
  | _ => false

def observeError : Bool :=
  match panItreeEvaluate 3 errorTree with
  | .ret (.error 3 : PanItreeEvaluateResult Nat Nat) => true
  | _ => false

def observeTau : Bool :=
  match panItreeEvaluate 3 tauTree with
  | .tau (.ret (.result (some 7) 3)) => true
  | _ => false

#guard observeNormal
#guard observeError
#guard observeTau

def runChecks : IO Bool := do
  if observeNormal then IO.println "PASS itree_evaluate normal result" else IO.println "FAIL itree_evaluate normal result"
  if observeError then IO.println "PASS itree_evaluate FFI error" else IO.println "FAIL itree_evaluate FFI error"
  if observeTau then IO.println "PASS itree_evaluate preserves Tau" else IO.println "FAIL itree_evaluate preserves Tau"
  pure (observeNormal && observeError && observeTau)

end Flapjack.Test.PanItreeEvaluateParity
