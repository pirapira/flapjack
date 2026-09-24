import Flapjack.Pancake.WordConvs

/-!
# wordConvs `inst_arg_convention` / `call_arg_convention` oracle parity

Kernel-checked fixtures against the direct HOL oracle
`scripts/hol-probes/word_convs_call_arg_probe.out` (23 rows), which evaluates
`wordConvs$inst_arg_convention` and `wordConvs$call_arg_convention` on the
backend `asm$inst` / `wordLang$prog` syntax.
-/

namespace Flapjack.Test.WordLangCallArgParity

open Flapjack

private abbrev W := BitVec 8
private def w8 (n : Nat) : W := BitVec.ofNat 8 n
private def emptySet : WordLangNumSet := fun _ => none
private def cutsets : WordLangCutsets := (emptySet, emptySet)

private def instAddCarryOk : WordLangInst W := .arith (.addCarry 1 2 3 0)
private def instAddCarryBad : WordLangInst W := .arith (.addCarry 1 2 3 1)
private def instShiftOk : WordLangInst W := .arith (.shift .lsl 1 2 (.reg 8))
private def instShiftBad : WordLangInst W := .arith (.shift .lsl 1 2 (.reg 7))
private def instLongMulOk : WordLangInst W := .arith (.longMul 6 0 0 4)
private def instLongDivOk : WordLangInst W := .arith (.longDiv 0 6 6 0 9)
private def instAddOverflowOk : WordLangInst W := .arith (.addOverflow 1 2 3 0)
private def instSubOverflowBad : WordLangInst W := .arith (.subOverflow 1 2 3 1)
private def instConst : WordLangInst W := .const 1 (w8 0)

private def returnOk : WordLangProg W := .return 1 [2, 4]
private def returnBad : WordLangProg W := .return 1 [4, 2]
private def raiseOk : WordLangProg W := .raise 2
private def raiseBad : WordLangProg W := .raise 3
private def installOk : WordLangProg W := .install 2 4 0 0 cutsets
private def installBad : WordLangProg W := .install 2 5 0 0 cutsets
private def allocOk : WordLangProg W := .alloc 2 cutsets
private def allocBad : WordLangProg W := .alloc 3 cutsets
private def storeConstsOk : WordLangProg W := .storeConsts 0 2 4 6 []
private def callNoneOk : WordLangProg W := .call none none [0, 2, 4] none
private def callNoneBad : WordLangProg W := .call none none [0, 4] none
private def callSomeOk : WordLangProg W :=
  .call (some ([2, 4], cutsets, .skip, 10, 11)) none [2, 4] none
private def callInstOk : WordLangProg W := .inst instAddCarryOk
private def seqBad : WordLangProg W := .seq (.raise 2) (.raise 3)

example : instArgConvention instAddCarryOk = true := by decide
example : instArgConvention instAddCarryBad = false := by decide
example : instArgConvention instShiftOk = true := by decide
example : instArgConvention instShiftBad = false := by decide
example : instArgConvention instLongMulOk = true := by decide
example : instArgConvention instLongDivOk = true := by decide
example : instArgConvention instAddOverflowOk = true := by decide
example : instArgConvention instSubOverflowBad = false := by decide
example : instArgConvention instConst = true := by decide

example : callArgConvention returnOk = true := by decide
example : callArgConvention returnBad = false := by decide
example : callArgConvention raiseOk = true := by decide
example : callArgConvention raiseBad = false := by decide
example : callArgConvention installOk = true := by decide
example : callArgConvention installBad = false := by decide
example : callArgConvention allocOk = true := by decide
example : callArgConvention allocBad = false := by decide
example : callArgConvention storeConstsOk = true := by decide
example : callArgConvention callNoneOk = true := by decide
example : callArgConvention callNoneBad = false := by decide
example : callArgConvention callSomeOk = true := by decide
example : callArgConvention callInstOk = true := by decide
example : callArgConvention seqBad = false := by decide

private def guards : List Bool :=
  [ instArgConvention instAddCarryOk, instArgConvention instAddCarryBad
  , instArgConvention instShiftOk, instArgConvention instShiftBad
  , instArgConvention instLongMulOk, instArgConvention instLongDivOk
  , instArgConvention instAddOverflowOk, instArgConvention instSubOverflowBad
  , instArgConvention instConst
  , callArgConvention returnOk, callArgConvention returnBad
  , callArgConvention raiseOk, callArgConvention raiseBad
  , callArgConvention installOk, callArgConvention installBad
  , callArgConvention allocOk, callArgConvention allocBad
  , callArgConvention storeConstsOk
  , callArgConvention callNoneOk, callArgConvention callNoneBad
  , callArgConvention callSomeOk, callArgConvention callInstOk
  , callArgConvention seqBad ]

private def expected : List Bool :=
  [ true, false, true, false, true, true, true, false, true
  , true, false, true, false, true, false, true, false, true
  , true, false, true, true, false ]

def runChecks : IO Bool := do
  if guards == expected then
    IO.println "PASS wordConvs call_arg_convention matches all 23 oracle rows"
  else
    IO.println "FAIL wordConvs call_arg_convention oracle mismatch"
  pure (guards == expected)

end Flapjack.Test.WordLangCallArgParity
