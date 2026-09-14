import Flapjack.RiscV.RegAlloc

/-! The source `mk_bij`/`list_remap` pass assigns each first-seen clash-tree
    variable the next allocator node, preserving existing assignments across
    Delta, Set, and source-order Seq traversal.  The expected maps and next
    counters are direct observations from
    `scripts/hol-probes/reg_alloc_mk_bij_probe.out`. -/

namespace Flapjack.Test.CakeMkBijParity

open Flapjack

def hasMapping (bijection : WordBijection) (source node : Nat) : Bool :=
  lookupNatInfo source bijection.toNode == some node &&
    lookupNatInfo node bijection.fromNode == some source

def emptyExact : Bool :=
  let bijection := wordMkBijection
    (.seq (.delta [] []) (.set []))
  bijection.next == 0 &&
    bijection.toNode == [] && bijection.fromNode == []

#guard emptyExact

def deltaExact : Bool :=
  let bijection := wordMkBijection (.delta [1, 2] [2, 3])
  bijection.next == 3 &&
    hasMapping bijection 1 2 &&
    hasMapping bijection 2 0 &&
    hasMapping bijection 3 1

#guard deltaExact

def setExact : Bool :=
  let bijection := wordMkBijection (.set [0, 1, 2])
  bijection.next == 3 &&
    hasMapping bijection 0 0 &&
    hasMapping bijection 1 1 &&
    hasMapping bijection 2 2

#guard setExact

def seqExact : Bool :=
  let bijection := wordMkBijection
    (.seq (.delta [1] [2]) (.set [0, 1, 2]))
  bijection.next == 3 &&
    hasMapping bijection 0 0 &&
    hasMapping bijection 1 1 &&
    hasMapping bijection 2 2

#guard seqExact

def parityGuard : Bool := emptyExact && deltaExact && setExact && seqExact

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS Cake mk_bij HOL parity"
  else
    IO.println "FAIL Cake mk_bij HOL parity"
  pure parityGuard

end Flapjack.Test.CakeMkBijParity
