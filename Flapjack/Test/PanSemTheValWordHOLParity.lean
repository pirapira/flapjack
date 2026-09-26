import Flapjack.Pancake.Semantics.PanSem.EvalExact

/-!
# Parity of the exact `panSem$theValWord` over `ValueHOL`

HOL `theValWord_def` (`cakeml/pancake/semantics/panSemScript.sml:42`) specifies
only `theValWord (ValWord w) = w`; the other `v` constructors are unspecified.
The direct HOL row `the_val_word=3w` is in
`scripts/hol-probes/pan_word_helpers_probe.out`.  This module replays the
specified equation over the exact `ValueHOL` carrier, records the documented
totalization on the unspecified branches, and checks the kernel bridge to the
executed evaluator's `valueWord` helper.
-/

namespace Flapjack.Test.PanSemTheValWordHOLParity

open Flapjack

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n

private def nameA : Flapjack.Basis.Pure.MlString.MlString :=
  Flapjack.Basis.Pure.MlString.ofString "A"

private def valWord : ValueHOL 8 := .val (.word (w8 3))

private def rstruct : ValueHOL 8 := .rStruct []

private def nstruct : ValueHOL 8 := .nStruct nameA []

/-- Replays the HOL row `the_val_word=3w` of
    `scripts/hol-probes/pan_word_helpers_probe.out`. -/
example : theValWordHOL valWord = w8 3 := rfl

/-- The exact tagged specified equation of `theValWord_def`. -/
example : theValWordHOL (.val (.word (w8 3)) : ValueHOL 8) = w8 3 :=
  theValWordHOL_val_word (w8 3)

/-- Documented totalization on HOL's unspecified `RStruct` branch (not a HOL
    statement; the rendering chooses `0`). -/
example : theValWordHOL rstruct = 0 := rfl

/-- Documented totalization on HOL's unspecified `NStruct` branch. -/
example : theValWordHOL nstruct = 0 := rfl

/-- Kernel bridge to the exact evaluator's totalized `valueWord` helper. -/
example : theValWordHOL valWord = valueWord valWord :=
  theValWordHOL_eq_valueWord valWord

private def eqGuard : Bool :=
  (theValWordHOL valWord == w8 3) && (theValWordHOL rstruct == 0) &&
    (theValWordHOL nstruct == 0)

#guard eqGuard

def runChecks : IO Bool := do
  IO.println "PASS panSem theValWord specified equation over exact ValueHOL"
  pure eqGuard

end Flapjack.Test.PanSemTheValWordHOLParity