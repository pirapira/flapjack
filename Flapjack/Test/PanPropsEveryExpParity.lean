import Flapjack.Pancake.Semantics.PanProps

/-! Exact-carrier parity for HOL `panProps$every_exp`
(`cakeml/pancake/semantics/panPropsScript.sml:1311-1333`, bead flapjack-4ac.4.68).

The rows exercise the leaf conjunction and the two `EVERY` folds
(`everyExpListHOL` for `RStruct`/`Op`/`Panop` and `everyExpFieldListHOL` for the
`MAP SND` field list of `NStruct`) over the exact `ExpHOL 64` carrier. -/

namespace Flapjack.Test

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev ExactName := Flapjack.Basis.Pure.MlString.MlString

private def nameA : ExactName := .implode [97]
private def nameB : ExactName := .implode [98]

private def exprVar : ExpHOL 64 := .var .local nameA
private def exprConst : ExpHOL 64 := .const 0

private def allTrue : ExpHOL 64 → Bool := fun _ => true

/-- Predicate holding on `Var` leaves and on `RStruct` containers, but not on
    `Const` leaves: it distinguishes the root conjunct from the list fold. -/
private def rstructVarSel : ExpHOL 64 → Bool
  | .rstruct _ => true
  | .var _ _ => true
  | _ => false

/-- Leaf insertion: `every_exp P (Var ..) = P (Var ..)`. -/
example : everyExpHOL allTrue exprVar = true := rfl

/-- Leaf rejection: `every_exp P (Const ..) = P (Const ..)`, here `false`. -/
example : everyExpHOL rstructVarSel exprConst = false := rfl

/-- A non-list container is false when the root predicate rejects it, even
    though its sub-expression is selected. -/
example : everyExpHOL rstructVarSel (.load32 exprVar) = false := rfl

/-- `EVERY` fold over `RStruct` arguments accepts an all-selected list. -/
example : everyExpHOL rstructVarSel (.rstruct [exprVar, exprVar]) = true := rfl

/-- `EVERY` fold rejects an `RStruct` argument list with an unselected member. -/
example : everyExpHOL rstructVarSel (.rstruct [exprVar, exprConst]) = false := rfl

/-- `NStruct` checks the `MAP SND` field list, leaving field names untouched. -/
example : everyExpHOL rstructVarSel (.nstruct nameB [(nameA, exprVar)]) = false :=
  rfl

/-- `every_exp` accepts a fully selected nested expression. -/
example : everyExpHOL allTrue (.cmp .equal (.load32 exprVar) (.nstruct nameB [(nameA, exprVar)])) =
    true :=
  rfl

end Flapjack.Test
