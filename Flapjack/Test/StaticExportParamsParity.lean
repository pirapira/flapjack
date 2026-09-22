import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `check_export_params_def`
    (`cakeml/pancake/panStaticScript.sml:649-658`). -/

def exportedParamScope : Scope := .funScope "f" ""

#guard staticResultOk (checkExportParams "" exportedParamScope [])

#guard
  staticResultOk
      (checkExportParams "" exportedParamScope [("x", .one), ("y", .one)])

#guard
  staticResultErrorMessage
      (checkExportParams "" exportedParamScope
        [("pair", .comb [.one, .one]), ("later", .one)]) ==
    some "exported function parameter pair has shape {1,1} instead of a word in function f\n"

#guard
  staticResultErrorMessage
      (staticCheckFunctionHeader (α := Nat) ([] : StructContext)
        { name := "f", inline := false, exported := true,
          params := [("pair", .comb [.one, .one])],
          body := .skip, returnShape := .one }) ==
    some "exported function parameter pair has shape {1,1} instead of a word in function f\n"

end Flapjack
