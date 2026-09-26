import Flapjack.Pancake.PanLang
import Flapjack.Pancake.PanLang.Prog

/-!
# Original-domain parity for `panLang$exp_ids`

The source definition is `cakeml/pancake/panLangScript.sml:222-231`.
The expected observations come from the checked-in HOL probe
`scripts/hol-probes/pan_lang_exp_ids_probeScript.sml`.
-/

namespace Flapjack.Test.PanExpIdsParity

open Flapjack

def empty : Prog Nat := .skip
def raiseOne : Prog Nat := .raise "E" (.const 7)
def sequence : Prog Nat :=
  .seq (.raise "E1" (.const 1)) (.raise "E2" (.const 2))
def declaration : Prog Nat :=
  .dec "x" .one (.const 0) (.raise "ED" (.const 3))
def conditionalLoop : Prog Nat :=
  .ite (.const 0)
    (.raise "EI" (.const 4))
    (.while (.const 0) (.raise "EW" (.const 5)))
def callHandler : Prog Nat :=
  .call (some (none, some ("EC", "h",
    .seq (.raise "EH" (.const 6)) .skip))) "f" []
def fallback : Prog Nat := .assign .local "x" (.const 9)

private def byteRangedRaise : Prog (BitVec 64) := .raise "E" (.const 7)

example :
    (Flapjack.Pancake.PanLang.expIdsHOL
      (Flapjack.Pancake.PanLang.progToHOL byteRangedRaise)).map
        Flapjack.Basis.Pure.MlString.toStringOfBytes =
      expIds byteRangedRaise := by
  exact Flapjack.Pancake.PanLang.expIdsHOL_progToHOL_byteRanged byteRangedRaise
    (by
      change Flapjack.Pancake.PanLang.NameRanged "E" ∧
        Flapjack.Pancake.PanLang.ExpByteRanged (.const 7)
      constructor
      · simp [Flapjack.Pancake.PanLang.NameRanged]
      · change True
        trivial)

def same (actual expected : List ExceptionId) : Bool := actual == expected

#guard same (expIds empty) []
#guard same (expIds raiseOne) ["E"]
#guard same (expIds sequence) ["E1", "E2"]
#guard same (expIds declaration) ["ED"]
#guard same (expIds conditionalLoop) ["EI", "EW"]
#guard same (expIds callHandler) ["EC", "EH"]
#guard same (expIds fallback) []

def check (name : String) (actual expected : List ExceptionId) : IO Bool := do
  if same actual expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {repr expected}, got {repr actual}"
    pure false

def runChecks : IO Bool := do
  let results ← [
    check "pan exp_ids empty" (expIds empty) [],
    check "pan exp_ids raise" (expIds raiseOne) ["E"],
    check "pan exp_ids sequence" (expIds sequence) ["E1", "E2"],
    check "pan exp_ids declaration" (expIds declaration) ["ED"],
    check "pan exp_ids conditional/loop" (expIds conditionalLoop) ["EI", "EW"],
    check "pan exp_ids call handler" (expIds callHandler) ["EC", "EH"],
    check "pan exp_ids fallback" (expIds fallback) [] ].mapM id
  pure (results.all id)

/-! ## Exact-carrier parity for `exp_ids` (bead flapjack-4ac.1.33)

`expIdsHOL` is the tagged port of `cakeml/pancake/panLangScript.sml:222-231`
over the exact `ProgHOL` carrier.  The guards below replay the seven
`pan_lang_exp_ids_probe.out` rows through the name bridge `toStringOfBytes`. -/

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def eEmpty : ProgHOL 8 := .skip
def eRaise : ProgHOL 8 := .raise (ofString "E") (.const 7)
def eSequence : ProgHOL 8 :=
  .seq (.raise (ofString "E1") (.const 1)) (.raise (ofString "E2") (.const 2))
def eDeclaration : ProgHOL 8 :=
  .dec (ofString "x") .one (.const 0) (.raise (ofString "ED") (.const 3))
def eConditionalLoop : ProgHOL 8 :=
  .ite (.const 0)
    (.raise (ofString "EI") (.const 4))
    (.while (.const 0) (.raise (ofString "EW") (.const 5)))
def eCallHandler : ProgHOL 8 :=
  .call (some (none, some (ofString "EC", ofString "h",
    .seq (.raise (ofString "EH") (.const 6)) .skip))) (ofString "f") []
def eFallback : ProgHOL 8 := .assign .local (ofString "x") (.const 9)

def namesOf (program : ProgHOL 8) : List String :=
  (expIdsHOL program).map toStringOfBytes

#guard namesOf eEmpty == []
#guard namesOf eRaise == ["E"]
#guard namesOf eSequence == ["E1", "E2"]
#guard namesOf eDeclaration == ["ED"]
#guard namesOf eConditionalLoop == ["EI", "EW"]
#guard namesOf eCallHandler == ["EC", "EH"]
#guard namesOf eFallback == []

example : namesOf eRaise = ["E"] := by
  simp only [namesOf, eRaise, expIdsHOL, List.map_cons, List.map_nil]
  rw [toStringOfBytes_ofString_of_bytes "E" (by decide)]

example : namesOf eCallHandler = ["EC", "EH"] := by
  simp only [namesOf, eCallHandler, expIdsHOL, List.map_cons, List.map_nil,
    List.append_nil]
  rw [toStringOfBytes_ofString_of_bytes "EC" (by decide),
    toStringOfBytes_ofString_of_bytes "EH" (by decide)]

end Flapjack.Test.PanExpIdsParity
