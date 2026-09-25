import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-!
# Parity of the exact `panSem$isValWord` over `ValueHOL`

Direct original-HOL oracle rows are in
`scripts/hol-probes/pan_sem_is_val_word_probe.out` (`is_valword_val=T`,
`is_valword_rstruct=F`, `is_valword_nstruct=F`, `is_valword_wordlab=T`);
this module reproduces them over the faithful `ValueHOL` carrier.
-/

namespace Flapjack.Test.PanSemIsValWordHOLParity

open Flapjack

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n

private def nameA : Flapjack.Basis.Pure.MlString.MlString :=
  Flapjack.Basis.Pure.MlString.ofString "A"

private def valWord : ValueHOL 8 := .val (.word (w8 7))

private def rstruct : ValueHOL 8 := .rStruct []

private def nstruct : ValueHOL 8 := .nStruct nameA []

private def wordlabVal : ValueHOL 8 := .val (.word (w8 7))

example : isValWordHOL valWord = true := rfl

example : isValWordHOL rstruct = false := rfl

example : isValWordHOL nstruct = false := rfl

example : isValWordHOL wordlabVal = true := rfl

private def isValWordGuard : Bool :=
  (isValWordHOL valWord == true) && (isValWordHOL rstruct == false) &&
    (isValWordHOL nstruct == false) && (isValWordHOL wordlabVal == true)

#eval isValWordGuard
#guard isValWordGuard

def runChecks : IO Bool := do
  IO.println "PASS panSem isValWord exact carrier matches all 4 oracle rows"
  pure isValWordGuard

end Flapjack.Test.PanSemIsValWordHOLParity