import Flapjack.PanItreeLtree

/-!
# Parity checks for Pancake `ltree_def`

The source reference is `pan_itreeSemScript.sml:1537-1559`; the direct HOL
fixture is `scripts/hol-probes/pan_itree_ltree_probe.out`. The stateful
two-Vis case checks the intermediate `itree_iter` transition: the first
oracle changes state from `0` to `1`, so the second oracle returns `[8]` and
that value is observable in the final continuation.
-/

namespace Flapjack.Test.PanItreeLtreeParity

open Flapjack

def sourceProbeCommand : String := "scripts/hol-probes/regenerate.sh"

#guard sourceProbeCommand == "scripts/hol-probes/regenerate.sh"

def statefulOracle : FfiOracle Nat := fun _ state _ _bytes =>
  if state = 0 then .returned 1 [7] else .returned 2 [8]

def statefulWorld : PanFfiWorld Nat :=
  { oracle := statefulOracle, state := 0 }

def twoVisTree : PanFfiTree (List UInt8) :=
  .vis (.extCall "foo") [] [1]
    (fun _response =>
      .vis (.extCall "foo") [] [2]
        (fun response =>
          match response with
          | .returned bytes => .ret bytes
          | _ => .ret []))

def lengthFailureWorld : PanFfiWorld Nat :=
  { oracle := fun _ state _ _bytes => .returned state [], state := 9 }

def lengthFailureTree : PanFfiTree Unit :=
  .vis (.extCall "foo") [] [1] (fun _ => .ret ())

def finalWorld : PanFfiWorld Nat :=
  { oracle := fun _ _ _ _ => .final .failed, state := 9 }

def finalTree : PanFfiTree Unit :=
  .vis (.extCall "foo") [] [1] (fun _ => .ret ())

def observeRet : Bool :=
  match panLtreeFuel 1 (.ret [1]) statefulWorld with
  | .ret bytes => bytes == [1]
  | _ => false

def observeTau : Bool :=
  match panLtreeFuel 1 (.tau (.ret ())) statefulWorld with
  | .tau (.ret ()) => true
  | _ => false

def observeIntermediate : Bool :=
  match panLtreeFuel 2 twoVisTree statefulWorld with
  | .tau (.tau (.ret bytes)) => bytes == [8]
  | _ => false

def observeLengthFailure : Bool :=
  match panLtreeFuel 1 lengthFailureTree lengthFailureWorld with
  | .tau (.ret ()) => true
  | _ => false

def observeFinal : Bool :=
  match panLtreeFuel 1 finalTree finalWorld with
  | .tau (.ret ()) => true
  | _ => false

#guard observeRet
#guard observeTau
#guard observeIntermediate
#guard observeLengthFailure
#guard observeFinal

def runChecks : IO Bool := do
  if observeRet then IO.println "PASS ltree Ret" else IO.println "FAIL ltree Ret"
  if observeTau then IO.println "PASS ltree Tau" else IO.println "FAIL ltree Tau"
  if observeIntermediate then IO.println "PASS ltree intermediate Vis/state" else IO.println "FAIL ltree intermediate Vis/state"
  if observeLengthFailure then IO.println "PASS ltree length failure" else IO.println "FAIL ltree length failure"
  if observeFinal then IO.println "PASS ltree Oracle_final" else IO.println "FAIL ltree Oracle_final"
  pure (observeRet && observeTau && observeIntermediate && observeLengthFailure && observeFinal)

end Flapjack.Test.PanItreeLtreeParity
