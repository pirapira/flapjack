import Flapjack.RiscV.CakeAllocatorCore

/-!
# CakeML allocator spill/coalesce priority parity

The expected values are direct EVAL observations from
`scripts/hol-probes/word_alloc_cost_probe.out`, produced from
`cakeml/compiler/backend/word_allocScript.sml`:

* `get_spillcost`    lines 1666-1670
* `get_coalescecost` lines 1676-1681

These weights drive which values the IRC allocator spills, and therefore
which values occupy frame slots.  The guards below check the port's
`getSpillCost` / `getCoalesceCost` against the original, replacing
hand-entered expectations with oracle-backed ones (bead
`flapjack-pxn.8.5.14.1.3`).
-/

namespace Flapjack.Test.CakeSpillCostParity

open Flapjack.RiscV.CakeAlloc

/-- `get_spillcost (c,lr,lm,rr,rm) istail` weights each use class and
    multiplies tail-call costs by five. -/
def spillCostOracleExact : Bool :=
  getSpillCost 0 0 0 0 0 false == 0 &&
    getSpillCost 1 0 0 0 0 false == 1 &&
    getSpillCost 0 1 0 0 0 false == 2 &&
    getSpillCost 0 0 1 0 0 false == 4 &&
    getSpillCost 0 0 0 1 0 false == 2 &&
    getSpillCost 0 0 0 0 1 false == 4 &&
    getSpillCost 1 1 1 1 1 false == 13 &&
    getSpillCost 1 1 1 1 1 true == 65

#guard spillCostOracleExact

/-- `get_coalescecost` charges one extra per endpoint present in the
    spill-cost table: `(30,1,2)` empty, `(33,1,2)` with one endpoint
    present, `(36,1,2)` with both, and `(96,1,2)` at priority 2. -/
def coalesceCostOracleExact : Bool :=
  getCoalesceCost (fun _ => none) 3 0 1 2 == (30, (1, 2)) &&
    getCoalesceCost (fun n => if n == 1 then some 7 else none) 3 0 1 2 ==
      (33, (1, 2)) &&
    getCoalesceCost (fun n => if n == 2 then some 9 else none) 3 0 1 2 ==
      (33, (1, 2)) &&
    getCoalesceCost (fun _ => some 1) 3 0 1 2 == (36, (1, 2)) &&
    getCoalesceCost (fun _ => some 1) 3 2 1 2 == (96, (1, 2))

#guard coalesceCostOracleExact

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("allocator spill costs match get_spillcost", spillCostOracleExact),
      ("allocator coalesce costs match get_coalescecost",
        coalesceCostOracleExact) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSpillCostParity