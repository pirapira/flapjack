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

/-- Matching HOL `FLOOKUP` on the finite map. -/
def lookupShape : Bool :=
  (fmapEntries.lookup "f").isSome && (fmapEntries.lookup "g").isNone &&
    ((fmapEntries.remove "f").lookup "f").isNone

def parityGuard : Bool :=
  inlinedShape && fmapMissShape && lookupShape && fmapNestedShape && fmapArgShape &&
    clauseGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS crep_inline exact finite-map inline_prog port"
  else
    IO.println "FAIL crep_inline exact finite-map inline_prog port"
  pure parityGuard

end Flapjack.Test.CrepInlineFmapParity
