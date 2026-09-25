import Flapjack.Pancake.Semantics.PanProps

/-! Exact-carrier parity for HOL `panProps$exps_of`
(`cakeml/pancake/semantics/panPropsScript.sml:1336-1358`, bead flapjack-4ac.4.69).

Each row matches one HOL clause over the exact `ProgHOL 64`/`ExpHOL 64`
carriers. -/

namespace Flapjack.Test

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev ExactName := Flapjack.Basis.Pure.MlString.MlString

private def nameA : ExactName := .implode [97]
private def nameB : ExactName := .implode [98]

private def exprVar : ExpHOL 64 := .var .local nameA
private def exprConst : ExpHOL 64 := .const 0

/-- `exps_of (Raise _ e) = [e]`. -/
example : expsOfHOL (.raise nameB exprVar : ProgHOL 64) = [exprVar] := rfl

/-- `exps_of (Seq p q) = exps_of p ++ exps_of q`. -/
example :
    expsOfHOL (.seq (.assign .local nameA exprVar) (.return exprConst) : ProgHOL 64) =
      [exprVar, exprConst] :=
  rfl

/-- `exps_of (If e p q) = e :: exps_of p ++ exps_of q`. -/
example : expsOfHOL (.ite exprVar .skip .break : ProgHOL 64) = [exprVar] := rfl

/-- `exps_of (While e p) = e :: exps_of p`. -/
example : expsOfHOL (.while exprVar (.return exprConst) : ProgHOL 64) = [exprVar, exprConst] :=
  rfl

/-- `exps_of (Call NONE _ es) = es`. -/
example : expsOfHOL (.call none nameA [exprConst] : ProgHOL 64) = [exprConst] := rfl

/-- `exps_of (Call (SOME (_ , SOME (_ , _ , ep)))) _ es = es ++ exps_of ep`. -/
example :
    expsOfHOL (.call (some (none, some (nameB, nameA, .return exprVar))) nameA [exprConst] :
        ProgHOL 64) =
      [exprConst, exprVar] :=
  rfl

/-- `exps_of (Call (SOME (_ , NONE)) _ es) = es`. -/
example : expsOfHOL (.call (some (none, none)) nameA [exprConst] : ProgHOL 64) = [exprConst] :=
  rfl

/-- `exps_of (DecCall _ _ _ es p) = es ++ exps_of p`. -/
example :
    expsOfHOL (.decCall nameA .one nameB [exprConst] (.return exprVar) : ProgHOL 64) =
      [exprConst, exprVar] :=
  rfl

/-- `exps_of (Store e1 e2) = [e1;e2]`. -/
example : expsOfHOL (.store exprVar exprConst : ProgHOL 64) = [exprVar, exprConst] := rfl

/-- `exps_of (ExtCall _ e1 e2 e3 e4) = [e1;e2;e3;e4]`. -/
example :
    expsOfHOL (.extCall nameA exprVar exprConst exprVar exprConst : ProgHOL 64) =
      [exprVar, exprConst, exprVar, exprConst] :=
  rfl

/-- Default clause: `exps_of _ = []`. -/
example : expsOfHOL (.skip : ProgHOL 64) = [] := rfl

/-- `exps_of (Primitive _ _ es) = es` keeps the argument list unchanged. -/
example : expsOfHOL (.primitive nameA .addCarry [exprVar, exprConst] : ProgHOL 64) =
    [exprVar, exprConst] :=
  rfl

end Flapjack.Test
