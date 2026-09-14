import Flapjack.RiscV.CakeAllocatorCore

/-!
# Executable checks for the CakeML IRC allocator core

These checks pin the frame-relevant decisions of `Flapjack.RiscV.CakeAlloc`
(`Flapjack/RiscV/CakeAllocatorCore.lean`), the ported core of CakeML's
`compiler/backend/reg_alloc/reg_allocScript.sml` and
`compiler/backend/word_allocScript.sml`.  They are the executable half of bead
`flapjack-pxn.8.5.14.1.3.1`; the pinned constants are taken directly from the
original HOL definitions.
-/

namespace Flapjack.Test.CakeAllocatorCore

open Flapjack.RiscV.CakeAlloc

/-- Exactly one of the three WordLang variable conventions holds. -/
def conventionExact : Bool :=
  (List.range 64).all (fun n =>
    (if isPhyVar n then 1 else 0) + (if isAllocVar n then 1 else 0) +
      (if isStackVar n then 1 else 0) == 1)

#guard conventionExact

/-- CakeML's fixed spill-cost magic numbers, including the tail factor 5. -/
def spillCostExact : Bool :=
  getSpillCost 0 0 0 0 0 false == 0 &&
    getSpillCost 1 0 0 0 0 false == 1 &&
    getSpillCost 0 1 0 0 0 false == 2 &&
    getSpillCost 0 0 1 0 0 false == 4 &&
    getSpillCost 0 0 0 1 0 false == 2 &&
    getSpillCost 0 0 0 0 1 false == 4 &&
    getSpillCost 1 1 1 1 1 false == 13 &&
    getSpillCost 1 1 1 1 1 true == 65

#guard spillCostExact

/-- Coalescing cost weights frequency, priority and endpoint spill costs. -/
def coalesceCostExact : Bool :=
  getCoalesceCost (fun _ => none) 3 0 1 2 == (30, (1, 2)) &&
    getCoalesceCost (fun _ => some 1) 3 0 1 2 == (36, (1, 2))

#guard coalesceCostExact

/-- The RISC-V hardware-forced edges of `get_forced`. -/
def forcedEdgesExact : Bool :=
  getForcedAddCarry 1 3 4 == [(1, 3), (1, 4)] &&
    getForcedAddCarry 1 1 4 == [(1, 4)] &&
    getForcedAddCarry 1 1 1 == [] &&
    getForcedOverflow 2 2 == [] &&
    getForcedOverflow 2 5 == [(2, 5)] &&
    getForcedLongMul 1 2 3 == [(1, 2), (1, 3)]

#guard forcedEdgesExact

/-- `limit_var` is the smallest multiple of four above the variable, plus one. -/
def limitVarExact : Bool :=
  limitVar 0 == 5 &&
    limitVar 3 == 5 &&
    limitVar 4 == 9 &&
    limitVar 7 == 9 &&
    limitVar 8 == 13

#guard limitVarExact

/-- Stack-only propagation along moves (`merge_stack_only`). -/
def mergeStackOnlyExact : Bool :=
  mergeStackOnly 1 2 [1] [7] == ([1], [7]) &&
    mergeStackOnly 1 5 [1] [7] == ([5, 1], [1, 7]) &&
    mergeStackOnly 3 6 [] [7] == ([], [7]) &&
    mergeStackOnly 2 6 [] [7] == ([], [7])

#guard mergeStackOnlyExact

/-- Branch merge (`merge_stack_sets`) keeps the intersection and the
per-branch differences, and unions the forced sets. -/
def mergeStackSetsExact : Bool :=
  mergeStackSets [1, 2] [] [1, 3] [9] [1, 4] [8] == ([1, 3, 4], [9, 8])

#guard mergeStackSetsExact

/-- Temporary names are removed before slot assignment (`remove_temp_stack`). -/
def removeTempStackExact : Bool :=
  removeTempStack [1, 2] [1, 2, 3] [7] == ([3], [7])

#guard removeTempStackExact

/-- Colour defaults: physical variables keep their hardware register,
allocated variables keep their colour and everything else defaults to zero. -/
def colourDefaultExact : Bool :=
  spDefault [(3, 1)] 3 == 1 &&
    spDefault [] 4 == 2 &&
    spDefault [] 5 == 0 &&
    totalColour [(3, 1)] 3 == 2

#guard colourDefaultExact

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("the three WordLang variable conventions partition the variable space",
        conventionExact),
      ("CakeML spill costs use the original magic numbers and tail factor",
        spillCostExact),
      ("CakeML coalescing costs use the original weights", coalesceCostExact),
      ("RISC-V forced interference edges match get_forced", forcedEdgesExact),
      ("the SSA temporary numbering base matches limit_var", limitVarExact),
      ("stack-only propagation matches merge_stack_only", mergeStackOnlyExact),
      ("branch merging matches merge_stack_sets", mergeStackSetsExact),
      ("temporary names are removed before slot assignment", removeTempStackExact),
      ("colouring defaults match sp_default and total_colour", colourDefaultExact) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeAllocatorCore
