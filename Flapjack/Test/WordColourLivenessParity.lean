import Flapjack.RiscV.CorrectnessColour

/-! The matching HOL observations on `check_colouring_ok_alt`'s assignment
    write/live-after set are in
    `scripts/hol-probes/word_alloc_live_colour_noalias_probe.out`.  This is a
    local clash-checker prerequisite for HOL `colouring_ok`; it is not a port
    of the full Word evaluator theorem. -/

namespace Flapjack.Test.WordColourLivenessParity

open Flapjack Flapjack.RiscV

def destination : Nat := 1
def liveAfter : List Nat := [2, 3]
def goodColouring : NatInfoMap Nat := [(1, 8), (2, 9), (3, 10)]
def badColouring : NatInfoMap Nat := [(1, 8), (2, 8), (3, 10)]

def goodColour (name : Nat) : Nat :=
  if name = 1 then 8 else if name = 2 then 9 else if name = 3 then 10 else 0

def allocatorEdges : List (Nat × Nat) := wordClashPairs [destination] liveAfter
def allocatorColouring : NatInfoMap Nat := [(3, 5), (2, 4), (1, 3)]

def allocatorColour (name : Nat) : Nat :=
  match lookupNatInfo name allocatorColouring with
  | some colour => colour
  | none => 0

def clashCheckGood : Bool :=
  wordColouringRespectsClashes (wordClashPairs [destination] liveAfter) goodColouring

def clashCheckBad : Bool :=
  wordColouringRespectsClashes (wordClashPairs [destination] liveAfter) badColouring

theorem liveAfterNoAlias (current : Nat) (hcurrent : current ∈ liveAfter)
    (hdifferent : current ≠ destination) :
    goodColour current ≠ goodColour destination := by
  apply wordColouringRespectsClashes_singleWrite_liveAfter_noAlias
    goodColouring destination liveAfter (wordClashPairs [destination] liveAfter)
    goodColour
  · decide
  · intro current hcurrent hdifferent
    simp [liveAfter] at hcurrent
    rcases hcurrent with rfl | rfl <;>
      simp [wordClashPairs, liveAfter, destination]
  · intro name hname
    rcases hname with rfl | hname
    · simp [destination, goodColouring, goodColour, lookupNatInfo]
    · simp [liveAfter] at hname
      rcases hname with rfl | rfl <;>
        simp [goodColouring, goodColour, lookupNatInfo]
  · exact hcurrent
  · exact hdifferent

theorem allocatorColouringIsProduced :
    wordAllocateVarsWithClashes [1, 2, 3] allocatorEdges = some allocatorColouring := by
  decide

theorem allocatorLiveAfterNoAlias (current : Nat) (hcurrent : current ∈ liveAfter)
    (hdifferent : current ≠ destination) :
    allocatorColour current ≠ allocatorColour destination := by
  apply wordAllocateVarsWithClashes_noAliasOnLiveAfter
    [1, 2, 3] allocatorEdges allocatorColouring allocatorColouringIsProduced
    destination liveAfter allocatorColour
  · intro current hcurrent hdifferent
    simp [liveAfter] at hcurrent
    rcases hcurrent with rfl | rfl <;>
      simp [allocatorEdges, wordClashPairs, liveAfter, destination]
  · intro name hname
    rcases hname with rfl | hname
    · simp [allocatorColouring, allocatorColour, destination, lookupNatInfo]
    · simp [liveAfter] at hname
      rcases hname with rfl | rfl <;>
        simp [allocatorColouring, allocatorColour, lookupNatInfo]
  · exact hcurrent
  · exact hdifferent

#guard clashCheckGood
#guard !clashCheckBad
#guard goodColour 2 != goodColour destination
#guard goodColour 3 != goodColour destination
#guard allocatorColour 2 != allocatorColour destination
#guard allocatorColour 3 != allocatorColour destination

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("write and live-after use distinct colours", clashCheckGood),
      ("clash checker rejects destination alias with live-after", !clashCheckBad),
      ("no-alias theorem covers the first live-after variable",
        decide (goodColour 2 ≠ goodColour destination)),
      ("no-alias theorem covers the second live-after variable",
        decide (goodColour 3 ≠ goodColour destination)),
      ("allocator output derives live-after no-alias",
        decide (allocatorColour 2 ≠ allocatorColour destination) &&
          decide (allocatorColour 3 ≠ allocatorColour destination)) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.WordColourLivenessParity
