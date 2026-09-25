import Flapjack.Pancake.PanLang.Decl

/-! Direct HOL-oracle parity for the exact `is_wf_shape`/`is_wf_flds`/`is_wf_ctxt`
ports (`scripts/hol-probes/pan_lang_is_wf_shape_probe.out`, nine rows).  The
contexts are the exact MlString-keyed `StructContextExact`. -/

namespace Flapjack.Test.PanLangIsWfShapeParity

open Flapjack
open Flapjack.Pancake.PanLang

private def nameA : MlS := Flapjack.Basis.Pure.MlString.ofString "A"
private def nameB : MlS := Flapjack.Basis.Pure.MlString.ofString "B"
private def nameZ : MlS := Flapjack.Basis.Pure.MlString.ofString "Z"
private def nameF : MlS := Flapjack.Basis.Pure.MlString.ofString "f"

private def info (fields : List (MlS × ShapeHOL)) (size : Nat) : StructInfoHOLExact :=
  { fields := fields, size := size }

private def ctxt : StructContextExact := [(nameA, info [(nameF, .one)] 2)]
private def ctxtOk : StructContextExact :=
  [(nameA, info [(nameF, .named nameB)] 2), (nameB, info [] 1)]
private def ctxtDup : StructContextExact := [(nameA, info [] 1), (nameA, info [] 1)]
private def ctxtFieldMiss : StructContextExact := [(nameA, info [(nameF, .named nameB)] 2)]

example : isWfShapeExactHOL ctxt .one = true := by decide
example : isWfShapeExactHOL ctxt (.comb [.one, .comb [.one]]) = true := by decide
example : isWfShapeExactHOL ctxt (.named nameA) = true := by decide
example : isWfShapeExactHOL ctxt (.named nameZ) = false := by decide
example : isWfFldsExactHOL ctxt [(nameF, .one)] = true := by decide
example : isWfFldsExactHOL ctxt [(nameF, .named nameZ)] = false := by decide
example : isWfCtxtExactHOL ctxtOk = true := by decide
example : isWfCtxtExactHOL ctxtDup = false := by decide
example : isWfCtxtExactHOL ctxtFieldMiss = false := by decide

private def isWfShapeGuard : Bool :=
  (isWfShapeExactHOL ctxt .one == true) &&
  (isWfShapeExactHOL ctxt (.comb [.one, .comb [.one]]) == true) &&
  (isWfShapeExactHOL ctxt (.named nameA) == true) &&
  (isWfShapeExactHOL ctxt (.named nameZ) == false) &&
  (isWfFldsExactHOL ctxt [(nameF, .one)] == true) &&
  (isWfFldsExactHOL ctxt [(nameF, .named nameZ)] == false) &&
  (isWfCtxtExactHOL ctxtOk == true) &&
  (isWfCtxtExactHOL ctxtDup == false) &&
  (isWfCtxtExactHOL ctxtFieldMiss == false)

#eval isWfShapeGuard
#guard isWfShapeGuard

def runChecks : IO Bool := do
  IO.println (if isWfShapeGuard then "PASS panLang is_wf_shape/is_wf_flds/is_wf_ctxt exact carriers match all 9 oracle rows" else "FAIL panLang is_wf_shape parity")
  pure isWfShapeGuard

end Flapjack.Test.PanLangIsWfShapeParity
