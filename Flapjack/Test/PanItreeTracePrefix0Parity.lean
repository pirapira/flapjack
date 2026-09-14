import Flapjack.PanItreeTracePrefix

/-!
# Parity checks for Pancake `trace_prefix0_def`

The source reference is `pan_itreeSemScript.sml:1674-1688`; the direct HOL
fixture is `scripts/hol-probes/pan_itree_trace_prefix0_probe.out`. Its result
injections are normalized by `PanFfiResponse`, and the test checks the same
Ret/Tau, intermediate stateful Vis, length-failure, and Oracle_final cases.
-/

namespace Flapjack.Test.PanItreeTracePrefix0Parity

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
      .vis (.extCall "foo") [] [2] (fun _ => .ret ())))

def lengthFailureWorld : PanFfiWorld Nat :=
  { oracle := fun _ state _ _bytes => .returned state [], state := 9 }

def lengthFailureTree : PanFfiTree Unit :=
  .vis (.extCall "foo") [] [1] (fun _ => .ret ())

def finalWorld : PanFfiWorld Nat :=
  { oracle := fun _ _ _ _ => .final .failed, state := 9 }

def finalTree : PanFfiTree Unit :=
  .vis (.extCall "foo") [] [1] (fun _ => .ret ())

def observeRet : Bool :=
  tracePrefix0Fuel 0 (.ret ()) statefulWorld == some []

def observeTau : Bool :=
  tracePrefix0Fuel 1 (.tau (.ret ())) statefulWorld == some []

def observeIntermediate : Bool :=
  match tracePrefix0Fuel 3 twoVisTree statefulWorld with
  | some [first, second] =>
      first.bytes == [(1, 7)] && second.bytes == [(2, 8)]
  | _ => false

def observeLengthFailure : Bool :=
  tracePrefix0Fuel 1 lengthFailureTree lengthFailureWorld == some []

def observeFinal : Bool :=
  tracePrefix0Fuel 1 finalTree finalWorld == some []

#guard observeRet
#guard observeTau
#guard observeIntermediate
#guard observeLengthFailure
#guard observeFinal

def runChecks : IO Bool := do
  if observeRet then IO.println "PASS trace_prefix0 Ret" else IO.println "FAIL trace_prefix0 Ret"
  if observeTau then IO.println "PASS trace_prefix0 Tau" else IO.println "FAIL trace_prefix0 Tau"
  if observeIntermediate then IO.println "PASS trace_prefix0 intermediate Vis/state" else IO.println "FAIL trace_prefix0 intermediate Vis/state"
  if observeLengthFailure then IO.println "PASS trace_prefix0 length failure" else IO.println "FAIL trace_prefix0 length failure"
  if observeFinal then IO.println "PASS trace_prefix0 Oracle_final" else IO.println "FAIL trace_prefix0 Oracle_final"
  pure (observeRet && observeTau && observeIntermediate && observeLengthFailure && observeFinal)

end Flapjack.Test.PanItreeTracePrefix0Parity
