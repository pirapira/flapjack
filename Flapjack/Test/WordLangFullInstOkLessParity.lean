import Flapjack.Pancake.WordConvs

/-!
Kernel-checked parity for the `wordConvs$full_inst_ok_less_def` port and its
`wordLang$exp_to_addr` helper, against the direct HOL oracle
`scripts/hol-probes/word_convs_full_inst_ok_less_probe.out`.
-/

namespace Flapjack.Test.WordLangFullInstOkLessParity

open Flapjack
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n

private def emptySet : WordLangNumSetHOL := .ln

private def cutsets : WordLangCutsetsHOL := (emptySet, emptySet)

private def cfg : AsmConfig 8 :=
  { isa := .riscv
    encode := fun _ => []
    bigEndian := false
    codeAlignment := 2
    linkReg := none
    avoidRegs := [3]
    regCount := 8
    fpRegCount := 4
    twoRegArith := true
    validImm := fun _ value => value == w8 1
    addrOffset := (w8 0, w8 100)
    hwOffset := (w8 0, w8 100)
    byteOffset := (w8 0, w8 100)
    jumpOffset := (w8 0, w8 100)
    cjumpOffset := (w8 0, w8 100)
    locOffset := (w8 0, w8 100) }

private def goodInstProg : WordLangProgHOL W := .inst (.const 1 0)

private def immOkProg : WordLangProgHOL W :=
  .inst (.arith (.binop .add 1 2 (.imm 1)))

private def badProg : WordLangProgHOL W :=
  .inst (.arith (.binop .add 1 2 (.imm 2)))

private def seqBadProg : WordLangProgHOL W := .seq goodInstProg badProg

private def loopProg : WordLangProgHOL W := .loop emptySet goodInstProg emptySet

private def ifProg : WordLangProgHOL W :=
  .ite .equal 1 (.reg 2) goodInstProg goodInstProg

private def mustTerminateProg : WordLangProgHOL W := .mustTerminate goodInstProg

private def callRetBadProg : WordLangProgHOL W :=
  .call (some ([1], cutsets, badProg, 10, 11)) none [] none

private def callHandlerBadProg : WordLangProgHOL W :=
  .call (some ([1], cutsets, goodInstProg, 10, 11)) none []
    (some (2, badProg, 20, 21))

private def callNoneHandlerBadProg : WordLangProgHOL W :=
  .call none none [] (some (2, badProg, 20, 21))

private def callOkProg : WordLangProgHOL W := .call none none [] none

private def shareLoadProg : WordLangProgHOL W := .shareInst .load 1 (.var 3)

private def shareLoadBigProg : WordLangProgHOL W :=
  .shareInst .load 1 (.op .add [.var 3, .const (150 : W)])

private def shareLoad16Prog : WordLangProgHOL W := .shareInst .load16 1 (.var 3)

private def shareStore8Prog : WordLangProgHOL W := .shareInst .store8 1 (.var 3)

private def shareConstProg : WordLangProgHOL W :=
  .shareInst .load 1 (.const (5 : W))

private def assignProg : WordLangProgHOL W := .assign 1 (.const 0)

private def allocProg : WordLangProgHOL W := .alloc 1 cutsets

-- `exp_to_addr` rows (definitional, matching the HOL eval).
example : expToAddrHOL (WordLangExpHOL.var 3 : WordLangExpHOL W) =
    some (WordLangAddr.addr 3 0) := rfl
example : expToAddrHOL ((.op .add [.var 3, .const (5 : W)] : WordLangExpHOL W)) =
    some (WordLangAddr.addr 3 5) := rfl
example : expToAddrHOL ((.op .add [.const (5 : W), .var 3] : WordLangExpHOL W)) =
    none := rfl
example : expToAddrHOL ((.const (5 : W) : WordLangExpHOL W)) = none := rfl

-- `full_inst_ok_less` rows.
example : fullInstOkLess cfg goodInstProg = true := by decide
example : fullInstOkLess cfg immOkProg = true := by decide
example : fullInstOkLess cfg badProg = false := by decide
example : fullInstOkLess cfg seqBadProg = false := by decide
example : fullInstOkLess cfg loopProg = true := by decide
example : fullInstOkLess cfg ifProg = true := by decide
example : fullInstOkLess cfg mustTerminateProg = true := by decide
example : fullInstOkLess cfg callRetBadProg = false := by decide
example : fullInstOkLess cfg callHandlerBadProg = false := by decide
example : fullInstOkLess cfg callNoneHandlerBadProg = true := by decide
example : fullInstOkLess cfg callOkProg = true := by decide
example : fullInstOkLess cfg shareLoadProg = true := by decide
example : fullInstOkLess cfg shareLoadBigProg = false := by decide
example : fullInstOkLess cfg shareLoad16Prog = true := by decide
example : fullInstOkLess cfg shareStore8Prog = true := by decide
example : fullInstOkLess cfg shareConstProg = false := by decide
example : fullInstOkLess cfg assignProg = true := by decide
example : fullInstOkLess cfg allocProg = true := by decide

private def guards : List Bool :=
  [ fullInstOkLess cfg goodInstProg
  , fullInstOkLess cfg immOkProg
  , fullInstOkLess cfg badProg
  , fullInstOkLess cfg seqBadProg
  , fullInstOkLess cfg loopProg
  , fullInstOkLess cfg ifProg
  , fullInstOkLess cfg mustTerminateProg
  , fullInstOkLess cfg callRetBadProg
  , fullInstOkLess cfg callHandlerBadProg
  , fullInstOkLess cfg callNoneHandlerBadProg
  , fullInstOkLess cfg callOkProg
  , fullInstOkLess cfg shareLoadProg
  , fullInstOkLess cfg shareLoadBigProg
  , fullInstOkLess cfg shareLoad16Prog
  , fullInstOkLess cfg shareStore8Prog
  , fullInstOkLess cfg shareConstProg
  , fullInstOkLess cfg assignProg
  , fullInstOkLess cfg allocProg ]

private def expected : List Bool :=
  [true, true, false, false, true, true, true, false, false, true, true,
   true, false, true, true, false, true, true]

def runChecks : IO Bool := do
  let ok := guards == expected
  if ok then
    IO.println "PASS wordConvs full_inst_ok_less matches all 22 oracle rows"
  else
    IO.println "FAIL wordConvs full_inst_ok_less rows"
  pure ok

end Flapjack.Test.WordLangFullInstOkLessParity
