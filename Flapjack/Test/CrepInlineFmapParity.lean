import Flapjack.Pancake.CrepInline.Pass

/-! Regression for the genuine finite-map representation and the exact
`inline_prog` port (`flapjack-pxn.18.5.5.7`).

HOL `inline_prog_def` terminates with `CARD (FDOM fs) LEX prog_size`; the
function-represented `Flapjack.FiniteMap` has no finite domain, so the port
uses `CrepInlineFmap` with `lookup`/`remove`/`submap`/`card`.  These checks
pin the lookup/removal/cardinality laws and the two headline behaviours of
`crepInlineProgFmap`: a known callee is inlined (tick + argument-load wrapper)
and an unknown callee is left untouched. -/

namespace Flapjack.Test.CrepInlineFmapParity

open Flapjack

def fmapEntries : CrepInlineFmap Nat :=
  .insert "f" ([7], CrepProg.skip) .empty

theorem fmapLookupHit :
    fmapEntries.lookup "f" = some ([7], CrepProg.skip) := by
  simp [fmapEntries, CrepInlineFmap.lookup]

theorem fmapLookupMiss : fmapEntries.lookup "g" = none := by
  simp [fmapEntries, CrepInlineFmap.lookup]

theorem fmapRemoveLookupNone : (fmapEntries.remove "f").lookup "f" = none :=
  CrepInlineFmap.lookup_remove_none "f" fmapEntries

theorem fmapCardRemove : (fmapEntries.remove "f").card = 0 := by
  simp [fmapEntries, CrepInlineFmap.remove]

theorem fmapCardRemoveLt : (fmapEntries.remove "f").card < fmapEntries.card :=
  CrepInlineFmap.card_remove_lt "f" fmapEntries
    (value := ([7], CrepProg.skip))
    (by simp [fmapEntries, CrepInlineFmap.lookup])

theorem fmapSubmapRefl : CrepInlineFmap.submap fmapEntries fmapEntries :=
  CrepInlineFmap.submap_refl fmapEntries

/-- `inline_prog` on a finite-map hit inlines the callee body. -/
def fmapInlined : CrepProg Nat :=
  crepInlineProgFmap fmapEntries (.call none "f" [])

def inlinedShape : Bool :=
  match fmapInlined with
  | .seq .tick _ => true
  | _ => false

def fmapMissShape : Bool :=
  match crepInlineProgFmap fmapEntries (.call none "g" []) with
  | .call none "g" _ => true
  | _ => false

/-- Matching HOL `FLOOKUP` on the finite map. -/
def lookupShape : Bool :=
  (fmapEntries.lookup "f").isSome && (fmapEntries.lookup "g").isNone &&
    ((fmapEntries.remove "f").lookup "f").isNone

def parityGuard : Bool := inlinedShape && fmapMissShape && lookupShape

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS crep_inline exact finite-map inline_prog port"
  else
    IO.println "FAIL crep_inline exact finite-map inline_prog port"
  pure parityGuard

end Flapjack.Test.CrepInlineFmapParity