import Flapjack.Pancake.WordConvs

/-!
# `wordConvs$inst_ok_less` Lean regression

Kernel-checked observations of `instOkLess` at the 8-bit word width, matching
the direct HOL fixture `scripts/hol-probes/word_convs_inst_ok_less_probe.out`
row for row.  `instOkLess` is the weaker per-instruction well-formedness
predicate consumed by `compile_to_word_conventions2`; unlike `asm$inst_ok` it
omits operand-register checks.

Reference: `cakeml/compiler/backend/semantics/wordConvsScript.sml:208-249`.
-/

namespace Flapjack.Test.WordLangInstOkLessParity

open Flapjack
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n

private def cfg : AsmConfig 8 where
  isa := .riscv
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
  locOffset := (w8 0, w8 100)

example : instOkLess cfg (.arith (.binop .add 0 0 (.imm (w8 1)))) = true := by decide
example : instOkLess cfg (.arith (.binop .add 0 0 (.imm (w8 2)))) = false := by decide
example : instOkLess cfg (.arith (.binop .add 0 0 (.reg 5))) = true := by decide
example : instOkLess cfg (.arith (.shift .lsl 0 0 (.imm (w8 0)))) = true := by decide
example : instOkLess cfg (.arith (.shift .lsr 0 0 (.imm (w8 0)))) = false := by decide
example : instOkLess cfg (.arith (.shift .lsl 0 0 (.imm (w8 8)))) = false := by decide
example : instOkLess cfg (.arith (.div 0 1 2)) = true := by decide
example : instOkLess cfg (.arith (.longMul 0 1 0 2)) = false := by decide
example : instOkLess cfg (.arith (.longDiv 0 1 2 3 4)) = false := by decide
example : instOkLess cfg (.arith (.addCarry 0 1 2 3)) = true := by decide
example : instOkLess cfg (.arith (.addCarry 0 1 0 3)) = false := by decide
example : instOkLess cfg (.arith (.addOverflow 0 1 0 3)) = false := by decide
example : instOkLess cfg (.arith (.subOverflow 0 1 0 3)) = false := by decide
example : instOkLess cfg (.mem .load 0 (.addr 0 (w8 1))) = true := by decide
example : instOkLess cfg (.mem .load8 0 (.addr 0 (w8 1))) = true := by decide
example : instOkLess cfg (.mem .load16 0 (.addr 0 (w8 1))) = true := by decide
example : instOkLess cfg .skip = true := by decide
example : instOkLess cfg (.const 0 (w8 0)) = true := by decide
example : instOkLess cfg (.fp (.fpLess 0 1 2)) = true := by decide
example : instOkLess cfg (.fp (.fpLess 0 1 5)) = false := by decide
example : instOkLess cfg (.fp (.fpFma 0 1 2)) = false := by decide
example : instOkLess cfg (.fp (.fpMovToReg 1 1 0)) = true := by decide

private def guards : List Bool :=
  [ instOkLess cfg (.arith (.binop .add 0 0 (.imm (w8 1))))
  , instOkLess cfg (.arith (.binop .add 0 0 (.imm (w8 2))))
  , instOkLess cfg (.arith (.binop .add 0 0 (.reg 5)))
  , instOkLess cfg (.arith (.shift .lsl 0 0 (.imm (w8 0))))
  , instOkLess cfg (.arith (.shift .lsr 0 0 (.imm (w8 0))))
  , instOkLess cfg (.arith (.shift .lsl 0 0 (.imm (w8 8))))
  , instOkLess cfg (.arith (.div 0 1 2))
  , instOkLess cfg (.arith (.longMul 0 1 0 2))
  , instOkLess cfg (.arith (.longDiv 0 1 2 3 4))
  , instOkLess cfg (.arith (.addCarry 0 1 2 3))
  , instOkLess cfg (.arith (.addCarry 0 1 0 3))
  , instOkLess cfg (.arith (.addOverflow 0 1 0 3))
  , instOkLess cfg (.arith (.subOverflow 0 1 0 3))
  , instOkLess cfg (.mem .load 0 (.addr 0 (w8 1)))
  , instOkLess cfg (.mem .load8 0 (.addr 0 (w8 1)))
  , instOkLess cfg (.mem .load16 0 (.addr 0 (w8 1)))
  , instOkLess cfg .skip
  , instOkLess cfg (.const 0 (w8 0))
  , instOkLess cfg (.fp (.fpLess 0 1 2))
  , instOkLess cfg (.fp (.fpLess 0 1 5))
  , instOkLess cfg (.fp (.fpFma 0 1 2))
  , instOkLess cfg (.fp (.fpMovToReg 1 1 0)) ]

private def expected : List Bool :=
  [ true, false, true, true, false, false, true, false, false, true, false,
    false, false, true, true, true, true, true, true, false, false, true ]

def runChecks : IO Bool := do
  if guards == expected then
    IO.println "PASS wordConvs inst_ok_less matches all 22 oracle rows"
  else
    IO.println "FAIL wordConvs inst_ok_less oracle rows"
  pure (guards == expected)

end Flapjack.Test.WordLangInstOkLessParity