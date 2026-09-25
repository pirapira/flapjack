import Flapjack.Pancake.CrepInline.Pass

/-! Regression for the duplicate-free finite-map representation and the
`inline_prog` port (`flapjack-pxn.18.5.5.7`).

HOL `inline_prog_def` terminates with `CARD (FDOM fs) LEX prog_size`; the
function-represented `Flapjack.FiniteMap` has no finite domain, so the port
uses `CrepInlineFmap`, a unique-key finite map with
`lookup`/`remove`/`submap`/`card`.  These checks pin the lookup/removal/
cardinality laws, that `card` equals the domain cardinality, and that the
smart `insert` replaces a duplicate key rather than shadowing it.  The
`fmapDupOverwrite`/`fmapNestedShape`/`fmapArgShape` fixtures mirror the direct
HOL oracle rows in `scripts/hol-probes/crep_inline_code_inl_probe.out`
(`lookup_dup_f`, `inline_nested_call`, `inline_arg_call`). -/

namespace Flapjack.Test.CrepInlineFmapParity

open Flapjack
open Flapjack.Basis.Pure.MlString

private abbrev ExactName := Flapjack.Basis.Pure.MlString.MlString
private def exactKey (s : String) : ExactName := ofString s

private def exactRows :
    List (ExactName × (List Nat × CrepProgHOL 8)) :=
  [(exactKey "other", ([], .skip)),
   (exactKey "f", ([7], .skip)),
   (exactKey "f", ([9], .tick))]

private def exactSelectedRows :=
  crepInlineSelectedHOLRows [exactKey "f"] exactRows

/-- Filtering keeps the original selected triple order, as the
    `compile_inl_prog` input list does in HOL. -/
theorem exactFilterPreservesOrder :
    exactSelectedRows =
      [(exactKey "f", ([7], CrepProgHOL.skip)),
       (exactKey "f", ([9], CrepProgHOL.tick))] := by
  rfl

/-- HOL `alist_to_fmap` is a right fold of `|+`, so the first duplicate row is
    the `FLOOKUP` result. The exact carrier uses the same selected source rows. -/
theorem exactMapDuplicateFirst :
    (crepInlineMapHOL [exactKey "f"] exactRows).lookup (exactKey "f") =
      some ([7], CrepProgHOL.skip) := by
  rw [crepInlineMapHOL_lookup]
  change List.lookup (exactKey "f") exactSelectedRows = _
  rw [exactFilterPreservesOrder]
  simp [exactKey]

/-- HOL `DOMSUB` removes the selected function's binding. -/
theorem exactMapDomsub :
    ((crepInlineMapHOL [exactKey "f"] exactRows).remove (exactKey "f")).lookup
      (exactKey "f") = none := by
  rw [CrepInlineFmapHOL.lookup_remove]
  simp

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

/-- HOL `lookup_dup_f` / `inline_dup_call`: a duplicate key is overwritten
    (`|+` on HOL, smart `insert` here), so lookup returns the last binding. -/
def fmapDupOverwrite : CrepInlineFmap Nat :=
  CrepInlineFmap.insert "f" ([9], .dec 9 (.const 3) .skip) fmapEntries

theorem fmapDupOverwriteLookup :
    fmapDupOverwrite.lookup "f" = some ([9], .dec 9 (.const 3) .skip) :=
  CrepInlineFmap.lookup_insert_self "f" ([9], .dec 9 (.const 3) .skip) fmapEntries

/-- HOL `inline_nested_call`: the callee body calls `f` again; `inline_prog`
    removes `f` from the map (`\\`, DOMSUB) before recursing, so the nested
    call is left untouched. -/
def fmapNestedEntries : CrepInlineFmap Nat :=
  CrepInlineFmap.insert "f" ([], CrepProg.call none "f" []) CrepInlineFmap.empty

def fmapNestedShape : Bool :=
  match crepInlineProgFmap fmapNestedEntries (.call none "f" []) with
  | .seq .tick (.call none "f" []) => true
  | _ => false

/-- HOL `inline_arg_call`: argument loading through `arg_load`/`GENLIST`. -/
def fmapArgEntries : CrepInlineFmap Nat :=
  CrepInlineFmap.insert "f" ([7], .dec 1 (.const 1) .skip) CrepInlineFmap.empty

def fmapArgShape : Bool :=
  match crepInlineProgFmap fmapArgEntries (.call none "f" [.const 5]) with
  | .seq .tick
      (.dec 8 (.const 5) (.dec 7 (.var 8) (.dec 1 (.const 1) .skip))) => true
  | _ => false

/-- Carrier bridge: HOL `FLOOKUP` of the `FiniteMap` view is the map lookup. -/
theorem bridgeFlookup :
    FLOOKUP (CrepInlineFmap.toFiniteMap fmapEntries) "f" =
      some ([7], CrepProg.skip) :=
  CrepInlineFmap.FLOOKUP_toFiniteMap fmapEntries "f"

/-- Carrier bridge for `SUBMAP` (holds definitionally through the view). -/
theorem bridgeSubmapIff :
    (CrepInlineFmap.submap fmapEntries fmapEntries) ↔
      (∀ name value,
        FLOOKUP (CrepInlineFmap.toFiniteMap fmapEntries) name = some value →
        FLOOKUP (CrepInlineFmap.toFiniteMap fmapEntries) name = some value) :=
  CrepInlineFmap.submap_iff_flookup fmapEntries fmapEntries

/-- The carrier bridge commutes with `remove` (HOL `\\`). -/
theorem bridgeRemove (name : FunName) :
    CrepInlineFmap.toFiniteMap (fmapEntries.remove name) =
      fun key => if key == name then none else
        CrepInlineFmap.toFiniteMap fmapEntries key :=
  CrepInlineFmap.toFiniteMap_remove fmapEntries name

/-- The carrier bridge commutes with `insert` (HOL `|+`). -/
theorem bridgeInsert :
    (CrepInlineFmap.insert "g" ([3], CrepProg.skip) fmapEntries).lookup "g" =
      some ([3], CrepProg.skip) := by
  rw [CrepInlineFmap.lookup_insert]; simp

/-- A map that re-binds `"f"`: canonical `insert` drops the shadowed binding,
    so it is the same carrier as `fmapEntries`. -/
def fmapReinsert : CrepInlineFmap Nat :=
  CrepInlineFmap.insert "f" ([7], CrepProg.skip)
    (CrepInlineFmap.insert "f" ([9], .dec 9 (.const 3) .skip) CrepInlineFmap.empty)

theorem fmapReinsertViewEq :
    CrepInlineFmap.toFiniteMap fmapReinsert =
      CrepInlineFmap.toFiniteMap fmapEntries := by
  rw [show fmapReinsert = fmapEntries from rfl]

/-- The universal correspondence: any two carriers with the same HOL `FLOOKUP`
    view give the same inlined program (here the same map). -/
theorem bridgeCongr :
    crepInlineProgFmap fmapEntries CrepProg.skip =
      crepInlineProgFmap fmapEntries CrepProg.skip :=
  crepInlineProgFmap_congr (fs := fmapEntries) (gs := fmapEntries) rfl CrepProg.skip

/-- The universal correspondence applied to the shadowing `fmapReinsert`. -/
theorem bridgeCongrShadow :
    crepInlineProgFmap fmapReinsert CrepProg.skip =
      crepInlineProgFmap fmapEntries CrepProg.skip :=
  crepInlineProgFmap_congr (fs := fmapReinsert) (gs := fmapEntries)
    fmapReinsertViewEq CrepProg.skip

/-- Lean `.call none` defining equation of `crepInlineProgFmap`, in the shape
    of HOL `inline_prog_def`'s `Call` clause (ctyp `NONE`).  This is an unfold
    of the Lean definition, not a cross-system equality with HOL. -/
theorem clauseCallNone :
    crepInlineProgFmap fmapEntries (.call none "f" [.const 5]) =
      (match fmapEntries.lookup "f" with
       | none => .call none "f" [.const 5]
       | some (argsVname, body) =>
           let inlined :=
             (crepUnreachElim (crepInlineProgFmap (fmapEntries.remove "f") body)).1
           let tmp := crepInlineTmpNames ([.const 5].flatMap crepExpVars) argsVname
           crepInlineTail (crepArgLoad tmp [.const 5] argsVname inlined)) :=
  crepInlineProgFmap_call_hol fmapEntries "f" [.const 5]

/-- Lean `.call (some (rts, some _))` defining equation (the
    `SOME(rts, SOME _)` branch of HOL `inline_prog_def`'s `Call` clause): only
    the ctyp is updated and the handler recursively inlined.  Lean unfold, not
    a cross-system equality. -/
theorem clauseCallHandler :
    crepInlineProgFmap fmapEntries (.call (some ([1], some (0, .skip))) "f" []) =
      .call (some ([1], some (0, crepInlineProgFmap fmapEntries .skip))) "f" [] :=
  crepInlineProgFmap_call_some_handler_hol fmapEntries [1] 0 .skip "f" []

/-- Lean `.dec v e p` defining equation (structural recursion, matching HOL
    `inline_prog_def`'s `Dec` clause).  Lean unfold, not a cross-system
    equality. -/
theorem clauseDec :
    crepInlineProgFmap fmapEntries (.dec 1 (.const 1) .skip) =
      .dec 1 (.const 1) (crepInlineProgFmap fmapEntries .skip) :=
  crepInlineProgFmap_dec_hol fmapEntries 1 (.const 1) .skip

def clauseGuard : Bool :=
  match crepInlineProgFmap fmapEntries (.call (some ([1], some (0, .skip))) "f" []) with
  | .call (some ([1], some (_, _))) "f" [] => true
  | _ => false

/-- Cross-system helper observations against
    `scripts/hol-probes/crep_inline_helper_probe.out` (rows `eoc_p`,
    `branch_p`, `tail_p`, `argload_p`, `nontail_p`, `unreach_p`), evaluated on
    the same inputs by the original HOL definitions in
    `cakeml/pancake/crep_inlineScript.sml`. -/
def helperBody : CrepProg Nat := .dec 1 (.const 1) .skip

def helperP : CrepProg Nat :=
  .seq (.dec 1 (.const 1) (.return [.var 2])) .skip

theorem helperEocP :
    crepTransformEoc [10] helperP =
      .seq (.dec 1 (.const 1) (.seq (.assign 10 (.var 2)) .skip)) .skip := by
  simp [helperP, crepTransformEoc, crepNestedSeq]

theorem helperBranchP :
    crepTransformBranch 0 [10] helperP =
      .seq (.dec 1 (.const 1)
        (.seq (.seq (.assign 10 (.var 2)) .skip) (.break 0))) .skip := by
  simp [helperP, crepTransformBranch, crepNestedSeq]

theorem helperTailP :
    crepInlineTail helperP =
      .seq .tick (.seq (.dec 1 (.const 1) (.return [.var 2])) .skip) := by
  simp [helperP, crepInlineTail]

theorem helperArgLoadP :
    crepArgLoad [20] [.const 5] [7] helperBody =
      .dec 20 (.const 5) (.dec 7 (.var 20) (.dec 1 (.const 1) .skip)) := by
  simp [helperBody, crepArgLoad, nestedDecs]

theorem helperNontailP :
    crepInlineNontail helperBody [10] [11] [20] [.const 5] [7] =
      .dec 11 (.const 0)
        (.seq (.dec 20 (.const 5) (.dec 7 (.var 20) (.dec 1 (.const 1) .skip)))
          (.seq (.assign 10 (.var 11)) .skip)) := by
  simp [helperBody, crepInlineNontail, crepArgLoad, nestedDecs, crepNestedSeq]

theorem helperUnreachP :
    (crepUnreachElim helperP).1 = .dec 1 (.const 1) (.return [.var 2]) := by
  simp [helperP, crepUnreachElim]

/-- Matching HOL `FLOOKUP` on the finite map. -/
def lookupShape : Bool :=
  (fmapEntries.lookup "f").isSome && (fmapEntries.lookup "g").isNone &&
    ((fmapEntries.remove "f").lookup "f").isNone

def exactCarrierGuard : Bool :=
  let ordered := match exactSelectedRows with
    | [(first, ([7], .skip)), (second, ([9], .tick))] =>
        first == exactKey "f" && second == exactKey "f"
    | _ => false
  let firstWins := match
      (crepInlineMapHOL [exactKey "f"] exactRows).lookup (exactKey "f") with
    | some ([7], .skip) => true
    | _ => false
  let domsubRemoves :=
    ((crepInlineMapHOL [exactKey "f"] exactRows).remove (exactKey "f")).lookup
      (exactKey "f") |>.isNone
  ordered && firstWins && domsubRemoves

def parityGuard : Bool :=
  inlinedShape && fmapMissShape && lookupShape && fmapNestedShape && fmapArgShape &&
    clauseGuard && exactCarrierGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS crep_inline finite-map inline_prog and exact HOL input carrier"
  else
    IO.println "FAIL crep_inline exact finite-map inline_prog port"
  pure parityGuard

end Flapjack.Test.CrepInlineFmapParity
