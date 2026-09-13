import Flapjack.PanItreeTracePrefix

/-!
# Parity checks for Pancake `trace_prefix_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_trace_prefix_probe.out` is generated from
`pan_itreeSemScript.sml:1639-1653`. The Lean checks cover the same Ret, Tau,
successful Vis, length-mismatch, and terminal-oracle branches. The two-Vis
case is intentionally stateful: its second event depends on the host state
written by the first successful oracle call, so it checks the intermediate
state transition as well as the emitted trace.
-/

namespace Flapjack.Test.PanItreeTracePrefixParity

open Flapjack

def sourceProbeCommand : String := "scripts/hol-probes/regenerate.sh"

#guard sourceProbeCommand == "scripts/hol-probes/regenerate.sh"

def statefulOracle : FfiOracle Nat := fun _ state _ _bytes =>
  if state = 0 then .returned 1 [7] else .returned 2 [8]

def statefulWorld : PanFfiWorld Nat :=
  { oracle := statefulOracle, state := 0 }

def twoVisTree : PanFfiTree Unit :=
  .tau (.vis (.extCall "foo") [] [1]
    (fun _response =>
      .vis (.extCall "foo") [] [2]
        (fun _ => .ret ())))

def lengthFailureOracle : FfiOracle Nat := fun _ state _ _ =>
  .returned state []

def lengthFailureWorld : PanFfiWorld Nat :=
  { oracle := lengthFailureOracle, state := 9 }

def lengthFailureTree : PanFfiTree Unit :=
  .vis (.extCall "foo") [] [1] (fun _ => .ret ())

def finalOracle : FfiOracle Nat := fun _ _ _ _ => .final .failed

def finalWorld : PanFfiWorld Nat :=
  { oracle := finalOracle, state := 9 }

def finalTree : PanFfiTree Unit :=
  .vis (.extCall "foo") [] [1] (fun _response =>
    match _response with
    | .final .failed => .ret ()
    | _ => .ret ())

def observeRet : Bool :=
  tracePrefixFuel 0 (.ret ()) statefulWorld == some []

def observeTau : Bool :=
  tracePrefixFuel 1 (.tau (.ret ())) statefulWorld == some []

def observeIntermediate : Bool :=
  match tracePrefixFuel 3 twoVisTree statefulWorld with
  | some [first, second] =>
      first.name == .extCall "foo" &&
        first.bytes == [(1, 7)] &&
        second.name == .extCall "foo" &&
        second.bytes == [(2, 8)]
  | _ => false

def observeLengthFailure : Bool :=
  tracePrefixFuel 1 lengthFailureTree lengthFailureWorld == some []

def observeFinal : Bool :=
  tracePrefixFuel 1 finalTree finalWorld == some []

#guard observeRet
#guard observeTau
#guard observeIntermediate
#guard observeLengthFailure
#guard observeFinal

def runChecks : IO Bool := do
  if observeRet then IO.println "PASS trace_prefix Ret" else IO.println "FAIL trace_prefix Ret"
  if observeTau then IO.println "PASS trace_prefix Tau" else IO.println "FAIL trace_prefix Tau"
  if observeIntermediate then IO.println "PASS trace_prefix intermediate Vis/state" else IO.println "FAIL trace_prefix intermediate Vis/state"
  if observeLengthFailure then IO.println "PASS trace_prefix length failure" else IO.println "FAIL trace_prefix length failure"
  if observeFinal then IO.println "PASS trace_prefix Oracle_final" else IO.println "FAIL trace_prefix Oracle_final"
  pure (observeRet && observeTau && observeIntermediate && observeLengthFailure && observeFinal)

end Flapjack.Test.PanItreeTracePrefixParity
