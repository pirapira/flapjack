/-
  Direct parity checks for the ported `wordConvs$flat_exp_conventions`
  (`flatExpConventions`) against the original HOL `EVAL` oracle
  `scripts/hol-probes/word_convs_flat_exp_probe.out`.

  The programs are built at the HOL word width `8 word` (`BitVec 8`).
-/
import Flapjack.Pancake.WordConvs

namespace Flapjack.Test.WordLangFlatExpParity

open Flapjack

private abbrev W := BitVec 8

private def emptySet : WordLangNumSet := fun _ => none

private def cutsets : WordLangCutsets := (emptySet, emptySet)

private def good : WordLangProg W := .set .nextFree (.var 1)

private def bad : WordLangProg W := .assign 1 (.const 0)

private def assignProg : WordLangProg W := .assign 1 (.const 0)

private def storeProg : WordLangProg W := .store (.const 0) 1

private def setVarProg : WordLangProg W := .set .nextFree (.var 1)

private def setOpProg : WordLangProg W := .set .nextFree (.op .add [])

private def shareVarProg : WordLangProg W := .shareInst .load 1 (.var 1)

private def shareAddProg : WordLangProg W :=
  .shareInst .load 1 (.op .add [.var 1, .const 0])

private def shareConstProg : WordLangProg W := .shareInst .load 1 (.const 0)

private def seqBadProg : WordLangProg W := .seq bad .skip

private def seqOkProg : WordLangProg W := .seq good good

private def callNoneProg : WordLangProg W := .call none none [] none

private def callHandlerBadProg : WordLangProg W :=
  .call none none [] (some (2, bad, 20, 21))

private def callRetBadProg : WordLangProg W :=
  .call (some ([1], cutsets, bad, 10, 11)) none [] none

private def callBothOkProg : WordLangProg W :=
  .call (some ([1], cutsets, good, 10, 11)) none [] (some (2, good, 20, 21))

private def loopProg : WordLangProg W := .loop emptySet good emptySet

private def ifBadProg : WordLangProg W :=
  .ite .equal 0 (.reg 1) bad .skip

private def mustTerminateProg : WordLangProg W := .mustTerminate good

private def instProg : WordLangProg W := .inst (.skip : WordLangInst W)

-- The 17 kernel-checked cases, matching `word_convs_flat_exp_probe.out`.

example : flatExpConventions assignProg = false := by decide
example : flatExpConventions storeProg = false := by decide
example : flatExpConventions setVarProg = true := by decide
example : flatExpConventions setOpProg = false := by decide
example : flatExpConventions shareVarProg = true := by decide
example : flatExpConventions shareAddProg = true := by decide
example : flatExpConventions shareConstProg = false := by decide
example : flatExpConventions seqBadProg = false := by decide
example : flatExpConventions seqOkProg = true := by decide
example : flatExpConventions callNoneProg = true := by decide
example : flatExpConventions callHandlerBadProg = false := by decide
example : flatExpConventions callRetBadProg = false := by decide
example : flatExpConventions callBothOkProg = true := by decide
example : flatExpConventions loopProg = true := by decide
example : flatExpConventions ifBadProg = false := by decide
example : flatExpConventions mustTerminateProg = true := by decide
example : flatExpConventions instProg = true := by decide

#guard flatExpConventions assignProg == false
#guard flatExpConventions storeProg == false
#guard flatExpConventions setVarProg == true
#guard flatExpConventions setOpProg == false
#guard flatExpConventions shareVarProg == true
#guard flatExpConventions shareAddProg == true
#guard flatExpConventions shareConstProg == false
#guard flatExpConventions seqBadProg == false
#guard flatExpConventions seqOkProg == true
#guard flatExpConventions callNoneProg == true
#guard flatExpConventions callHandlerBadProg == false
#guard flatExpConventions callRetBadProg == false
#guard flatExpConventions callBothOkProg == true
#guard flatExpConventions loopProg == true
#guard flatExpConventions ifBadProg == false
#guard flatExpConventions mustTerminateProg == true
#guard flatExpConventions instProg == true

def runChecks : IO Bool := do
  let assign := flatExpConventions assignProg == false
  let store := flatExpConventions storeProg == false
  let setVar := flatExpConventions setVarProg == true
  let setOp := flatExpConventions setOpProg == false
  let shareVar := flatExpConventions shareVarProg == true
  let shareAdd := flatExpConventions shareAddProg == true
  let shareConst := flatExpConventions shareConstProg == false
  let seqBad := flatExpConventions seqBadProg == false
  let seqOk := flatExpConventions seqOkProg == true
  let callNone := flatExpConventions callNoneProg == true
  let callHandlerBad := flatExpConventions callHandlerBadProg == false
  let callRetBad := flatExpConventions callRetBadProg == false
  let callBothOk := flatExpConventions callBothOkProg == true
  let loop := flatExpConventions loopProg == true
  let ifBad := flatExpConventions ifBadProg == false
  let mustTerminate := flatExpConventions mustTerminateProg == true
  let inst := flatExpConventions instProg == true
  let all := [assign, store, setVar, setOp, shareVar, shareAdd, shareConst,
    seqBad, seqOk, callNone, callHandlerBad, callRetBad, callBothOk, loop,
    ifBad, mustTerminate, inst]
  if all.all id then
    IO.println "PASS wordConvs flat_exp_conventions matches all 17 oracle rows"
  else
    IO.println "FAIL wordConvs flat_exp_conventions matches all 17 oracle rows"
  pure (all.all id)

end Flapjack.Test.WordLangFlatExpParity