import Flapjack.LoopToWord

/-!
# Loop-to-word context lookup parity tests

These regressions exercise the ports of `find_var_def`, `find_reg_imm_def` and
`make_ctxt_def` from `cakeml/pancake/loop_to_wordScript.sml`. The expected
values below are checked-in output from the original HOL definitions, produced
by `scripts/hol-probes/loop_to_word_probeScript.sml` and regenerated with
`scripts/hol-probes/regenerate.sh`. This test therefore compares Flapjack with
the original Pancake implementation rather than with a second Lean
transcription.
-/

namespace Flapjack.Test.LoopToWord

open Flapjack Flapjack.LoopToWord

/-! The values are the literal records from
    `scripts/hol-probes/loop_to_word_probe.out`. Keep these names tied to the
    probe output: they are not executable reference definitions. -/
def originalFindVarEmpty : Nat := 0
def originalFindVarHit : Nat := 7
def originalFindVarMiss : Nat := 0
def originalFindVarCtxt10 : Nat := 2
def originalFindVarCtxt11 : Nat := 4
def originalFindVarCtxt12 : Nat := 6
def originalFindRegImmImm : RegImm Nat := .imm 5
def originalFindRegImmReg : RegImm Nat := .reg 0
def originalFindRegImmCtxt : RegImm Nat := .reg 4

def sameRegImm : RegImm Nat → RegImm Nat → Bool
  | .imm left, .imm right => left == right
  | .reg left, .reg right => left == right
  | _, _ => false

#guard findVar [] 0 == originalFindVarEmpty
#guard findVar [(3, 7)] 3 == originalFindVarHit
#guard findVar [(3, 7)] 4 == originalFindVarMiss
#guard findVar (makeCtxt 2 [10, 11, 12] []) 10 == originalFindVarCtxt10
#guard findVar (makeCtxt 2 [10, 11, 12] []) 11 == originalFindVarCtxt11
#guard findVar (makeCtxt 2 [10, 11, 12] []) 12 == originalFindVarCtxt12

example : findRegImm [] (.imm 5 : RegImm Nat) = originalFindRegImmImm := rfl
example : findRegImm [] (.reg 11 : RegImm Nat) = originalFindRegImmReg := rfl
example : findRegImm (makeCtxt 2 [10, 11, 12] []) (.reg 11 : RegImm Nat) =
    originalFindRegImmCtxt := rfl

def runChecks : IO Bool := do
  let mut ok := true
  if findVar [] 0 != originalFindVarEmpty then
    IO.println "FAIL LoopToWord.findVar empty"; ok := false
  if findVar [(3, 7)] 3 != originalFindVarHit then
    IO.println "FAIL LoopToWord.findVar hit"; ok := false
  if findVar [(3, 7)] 4 != originalFindVarMiss then
    IO.println "FAIL LoopToWord.findVar miss"; ok := false
  if findVar (makeCtxt 2 [10, 11, 12] []) 10 != originalFindVarCtxt10 then
    IO.println "FAIL LoopToWord.makeCtxt/findVar 10"; ok := false
  if findVar (makeCtxt 2 [10, 11, 12] []) 11 != originalFindVarCtxt11 then
    IO.println "FAIL LoopToWord.makeCtxt/findVar 11"; ok := false
  if findVar (makeCtxt 2 [10, 11, 12] []) 12 != originalFindVarCtxt12 then
    IO.println "FAIL LoopToWord.makeCtxt/findVar 12"; ok := false
  if !sameRegImm (findRegImm [] (.imm 5 : RegImm Nat)) originalFindRegImmImm then
    IO.println "FAIL LoopToWord.findRegImm immediate"; ok := false
  if !sameRegImm (findRegImm [] (.reg 11 : RegImm Nat)) originalFindRegImmReg then
    IO.println "FAIL LoopToWord.findRegImm register"; ok := false
  if !sameRegImm (findRegImm (makeCtxt 2 [10, 11, 12] []) (.reg 11 : RegImm Nat))
      originalFindRegImmCtxt then
    IO.println "FAIL LoopToWord.findRegImm context"; ok := false
  if ok then
    IO.println "PASS LoopToWord find_var/find_reg_imm/make_ctxt parity"
  pure ok

end Flapjack.Test.LoopToWord
