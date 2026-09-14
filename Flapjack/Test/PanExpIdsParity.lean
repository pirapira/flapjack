import Flapjack.Language

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

end Flapjack.Test.PanExpIdsParity
