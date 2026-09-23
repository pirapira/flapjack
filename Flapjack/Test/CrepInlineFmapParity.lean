import Flapjack.Pancake.CrepInline.Pass

/-! Regression for the duplicate-free finite-map representation and the
`inline_prog` port (`flapjack-pxn.18.5.5.7`).

HOL `inline_prog_def` terminates with `CARD (FDOM fs) LEX prog_size`; the
function-represented `Flapjack.FiniteMap` has no finite domain, so the port
uses `CrepInlineFmap`, a unique-key finite map with
`lookup`/`remove`/`submap`/`card`.  These checks pin the lookup/removal/
cardinality laws, that `card` equals the domain cardinality, and that the
smart `insert` replaces a duplicate key rather than shadowing it. -/

namespace Flapjack.Test.CrepInlineFmapParity

open Flapjack

def fmapEntries : CrepInlineFmap Nat :=
  CrepInlineFmap.insert "f" ([7], CrepProg.skip) CrepInlineFmap.empty

theorem fmapLookupHit :
    fmapEntries.lookup "f" = some ([7], CrepProg.skip) :=
  CrepInlineFmap.lookup_insert_self "f" ([7], CrepProg.skip) CrepInlineFmap.empty

theorem fmapLookupMiss : fmapEntries.lookup "g" = none := by
  simp [fmapEntries, CrepInlineFmap.insert, CrepInlineFmap.empty,
    CrepInlineFmap.lookup, List.lookup]

theorem fmapRemoveLookupNone : (fmapEntries.remove "f").lookup "f" = none :=
  CrepInlineFmap.lookup_remove_none "f" fmapEntries

theorem fmapCardRemove : (fmapEntries.remove "f").card = 0 := by
  simp [fmapEntries, CrepInlineFmap.insert, CrepInlineFmap.empty,
    CrepInlineFmap.remove, CrepInlineFmap.card]

theorem fmapCardRemoveLt : (fmapEntries.remove "f").card < fmapEntries.card :=
  CrepInlineFmap.card_remove_lt "f" fmapEntries
    (value := ([7], CrepProg.skip))
    (CrepInlineFmap.lookup_insert_self "f" ([7], CrepProg.skip) CrepInlineFmap.empty)

theorem fmapSubmapRefl : CrepInlineFmap.submap fmapEntries fmapEntries :=
  CrepInlineFmap.submap_refl fmapEntries

/-- Re-inserting an existing key replaces the binding instead of shadowing it,
    so the map has domain cardinality one (the coordinator's
    duplicate-key counterexample). -/
def fmapDupInsert : CrepInlineFmap Nat :=
  CrepInlineFmap.insert "f" ([1], CrepProg.skip) fmapEntries

theorem fmapDupInsertLookup : fmapDupInsert.lookup "f" = some ([1], CrepProg.skip) :=
  CrepInlineFmap.lookup_insert_self "f" ([1], CrepProg.skip) fmapEntries

theorem fmapDupInsertCard : fmapDupInsert.card = 1 := by
  simp [fmapDupInsert, fmapEntries, CrepInlineFmap.insert, CrepInlineFmap.empty,
    CrepInlineFmap.card, bne_self_eq_false]

theorem fmapDupInsertCardDomain :
    fmapDupInsert.card = (fmapDupInsert.entries.map Prod.fst).eraseDups.length :=
  CrepInlineFmap.card_eq_domain_cardinality fmapDupInsert

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
