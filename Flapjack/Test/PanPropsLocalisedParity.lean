import Flapjack.Pancake.Semantics.PanProps

/-! Exact-carrier parity for HOL `panProps$localised_exp`,
`panProps$nameless_exp`, `panProps$localised_prog`, and the `[local]` helper
`panProps$opt_mmap_eq_some_helper`
(`cakeml/pancake/semantics/panPropsScript.sml:1362/1371/1380/1575`, beads
flapjack-4ac.4.70/.4.72/.4.74/.4.89).

The rows exercise the `Var Local`-only rejection of `localisedExpHOL`, the
`NStruct`/`NField` rejection of `namelessExpHOL`, the program-level clauses of
`localisedProgHOL` (global assignment and global call destination), and a
positive application of the `List.mapM` helper. -/

namespace Flapjack.Test

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev ExactName := Flapjack.Basis.Pure.MlString.MlString

private def nameA : ExactName := .implode [97]
private def nameB : ExactName := .implode [98]

private def exprVar : ExpHOL 64 := .var .local nameA
private def exprGlobal : ExpHOL 64 := .var .global nameA
private def exprConst : ExpHOL 64 := .const 0

/-- `localised_exp` accepts a local variable. -/
example : localisedExpHOL exprVar = true := rfl

/-- `localised_exp` rejects a global variable. -/
example : localisedExpHOL exprGlobal = false := rfl

/-- `localised_exp` accepts a non-variable leaf. -/
example : localisedExpHOL (.load32 exprVar) = true := rfl

/-- `nameless_exp` accepts a non-structural leaf. -/
example : namelessExpHOL exprConst = true := rfl

/-- `nameless_exp` rejects a field projection. -/
example : namelessExpHOL (.nfield nameA exprVar) = false := rfl

/-- `nameless_exp` rejects a structural name. -/
example : namelessExpHOL (.nstruct nameB [(nameA, exprVar)]) = false := rfl

/-- `localised_prog` accepts a local assignment. -/
example : localisedProgHOL (.assign .local nameA exprVar) = true := rfl

/-- `localised_prog` rejects a global assignment. -/
example : localisedProgHOL (.assign .global nameA exprConst) = false := rfl

/-- `localised_prog` accepts a call with a local argument list. -/
example : localisedProgHOL ((.call none nameA [exprVar]) : ProgHOL 64) = true := rfl

/-- `localised_prog` rejects a call whose destination is global. -/
example : localisedProgHOL
    ((.call (some (some (.global, nameA), none)) nameB []) : ProgHOL 64) = false := rfl

/-- `localised_prog` accepts a call with a localised handler body. -/
example : localisedProgHOL
    ((.call (some (none, some (nameB, nameA, .skip))) nameB [exprVar]) : ProgHOL 64) =
    true := rfl

/-- `opt_mmap_eq_some_helper` transfers success along pointwise-equal maps. -/
example : [1, 2].mapM (fun n => some (n + 1)) = some [2, 3] :=
  optMmapEqSomeHelper (fun n => some (n + 1)) (fun n => some (n + 1)) [1, 2] [2, 3]
    rfl (by intro x _ y hy; exact hy)

end Flapjack.Test
