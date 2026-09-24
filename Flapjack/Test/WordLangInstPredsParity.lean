import Flapjack.Pancake.WordConvs

/-!
Kernel-checked parity for the backend `wordConvs` instruction predicates
`distinct_tar_reg`, `two_reg_inst`, and `every_inst` against the direct HOL
oracle `scripts/hol-probes/word_convs_inst_preds_probe.out`.

The programs are built at the HOL word width `8 word` (`BitVec 8`), matching
the oracle fixture.
-/

namespace Flapjack.Test.WordLangInstPredsParity

open Flapjack

private abbrev W := BitVec 8

private def emptySet : WordLangNumSet := fun _ => none

private def cutsets : WordLangCutsets := (emptySet, emptySet)

/-- `P i = (i = Skip)`, the HOL probe's test predicate. -/
private def isSkip : WordLangInst W → Bool
  | .skip => true
  | _ => false

-- Instruction fixtures (oracle rows 1-7).
private def binopSame : WordLangInst W := .arith (.binop .add 1 2 (.reg 1))
private def binopDiff : WordLangInst W := .arith (.binop .add 1 2 (.reg 3))
private def addCarrySame : WordLangInst W := .arith (.addCarry 1 2 1 3)
private def binopTwoSame : WordLangInst W := .arith (.binop .add 1 1 (.reg 0))
private def binopTwoDiff : WordLangInst W := .arith (.binop .add 1 2 (.reg 0))
private def instSkipInst : WordLangInst W := .skip

-- Program fixtures (oracle rows 8-15).
private def instSkip : WordLangProg W := .inst instSkipInst
private def instConst : WordLangProg W := .inst (.const 1 (0 : W))
private def opCurrHeap : WordLangProg W := .opCurrHeap .add 1 2
private def callHandlerBad : WordLangProg W :=
  .call none none [] (some (2, .inst (.const 1 (0 : W)), 20, 21))
private def callRetBad : WordLangProg W :=
  .call (some ([1], cutsets, .inst instSkipInst, 10, 11))
    none [] (some (2, .inst (.const 1 (0 : W)), 20, 21))
private def callRetOk : WordLangProg W :=
  .call (some ([1], cutsets, .inst instSkipInst, 10, 11)) none [] none
private def loopOk : WordLangProg W := .loop emptySet (.inst instSkipInst) emptySet
private def allocProg : WordLangProg W := .alloc 0 cutsets

-- 15 kernel-checked rows matching the HOL oracle.
example : distinctTarReg binopSame = false := by decide
example : distinctTarReg binopDiff = true := by decide
example : distinctTarReg addCarrySame = false := by decide
example : distinctTarReg instSkipInst = true := by decide

example : twoRegInst binopTwoSame = true := by decide
example : twoRegInst binopTwoDiff = false := by decide
example : twoRegInst instSkipInst = true := by decide

example : everyInst isSkip instSkip = true := by decide
example : everyInst isSkip instConst = false := by decide
example : everyInst isSkip opCurrHeap = false := by decide
example : everyInst isSkip callHandlerBad = true := by decide
example : everyInst isSkip callRetBad = false := by decide
example : everyInst isSkip callRetOk = true := by decide
example : everyInst isSkip loopOk = true := by decide
example : everyInst isSkip allocProg = true := by decide

#guard distinctTarReg binopSame == false
#guard distinctTarReg binopDiff == true
#guard distinctTarReg addCarrySame == false
#guard distinctTarReg instSkipInst == true
#guard twoRegInst binopTwoSame == true
#guard twoRegInst binopTwoDiff == false
#guard twoRegInst instSkipInst == true
#guard everyInst isSkip instSkip == true
#guard everyInst isSkip instConst == false
#guard everyInst isSkip opCurrHeap == false
#guard everyInst isSkip callHandlerBad == true
#guard everyInst isSkip callRetBad == false
#guard everyInst isSkip callRetOk == true
#guard everyInst isSkip loopOk == true
#guard everyInst isSkip allocProg == true

def runChecks : IO Bool := do
  let checks :=
    [ (distinctTarReg binopSame == false,
        "PASS wordConvs distinct_tar_reg rejects targeting the source register")
    , (distinctTarReg addCarrySame == false,
        "PASS wordConvs distinct_tar_reg excludes the source registers for AddCarry")
    , (twoRegInst binopTwoSame == true,
        "PASS wordConvs two_reg_inst accepts equal source/destination")
    , (twoRegInst binopTwoDiff == false,
        "PASS wordConvs two_reg_inst rejects distinct source/destination")
    , (everyInst isSkip callHandlerBad == true,
        "PASS wordConvs every_inst ignores a handler without return metadata")
    , (everyInst isSkip callRetBad == false,
        "PASS wordConvs every_inst descends into return and handler bodies")
    , (everyInst isSkip loopOk == true,
        "PASS wordConvs every_inst descends into Loop and Inst bodies")
    ]
  for (ok, message) in checks do
    if ok then IO.println message else IO.println s!"FAIL {message}"
  pure (checks.all (fun check => check.1))

end Flapjack.Test.WordLangInstPredsParity