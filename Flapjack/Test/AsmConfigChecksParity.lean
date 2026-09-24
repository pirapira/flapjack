import Flapjack.Compiler.Backend.StackProps

/-!
Kernel-checked parity guards for the assembler configuration validity
predicates against the direct HOL oracle
`scripts/hol-probes/asm_config_checks_probe.out`.

The fixture `asmConfig8` mirrors the HOL probe configuration exactly
(8-bit words, `RISC_V`, `code_alignment = 2`, `avoid_regs = [3]`,
`reg_count = 8`, `fp_reg_count = 4`, `two_reg_arith = T`, offsets
`addr/hw/byte = (0, 100)` and `jump/cjump/loc = (0, 200)`, `valid_imm`
always true, plus the carried-but-unused `encode`/`big_endian` fields).  Every row below corresponds to one `label=T|F` line of the
oracle.

Note the HOL oracle pinned an important semantic detail: `offset_ok` compares
the bounds with HOL's signed word `<=` (HOL `<=` on words is signed, unlike
`word_ls`), which is why `jumpOffsetOk` for the 8-bit offset `200w` is `F`.
-/

namespace Flapjack.Test.AsmConfigChecksParity

open Flapjack
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackProps

private abbrev W := BitVec 8

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

private def asmConfig8 : AsmConfig 8 :=
  { isa := .riscv
    encode := fun _ => []
    bigEndian := false
    codeAlignment := 2
    linkReg := none
    avoidRegs := [3]
    regCount := 8
    fpRegCount := 4
    twoRegArith := true
    validImm := fun _ _ => true
    addrOffset := (w8 0, w8 100)
    hwOffset := (w8 0, w8 100)
    byteOffset := (w8 0, w8 100)
    jumpOffset := (w8 0, w8 100)
    cjumpOffset := (w8 0, w8 100)
    locOffset := (w8 0, w8 100) }

private def aligned0 : Bool := asmAligned 0 (w8 8)
private def aligned2 : Bool := asmAligned 2 (w8 8)
private def unaligned2 : Bool := asmAligned 2 (w8 10)
private def regOk2 : Bool := asmRegOk asmConfig8 2
private def regOk3 : Bool := asmRegOk asmConfig8 3
private def regOk8 : Bool := asmRegOk asmConfig8 8
private def fpRegOk3 : Bool := asmFpRegOk asmConfig8 3
private def fpRegOk4 : Bool := asmFpRegOk asmConfig8 4
private def regImmReg : Bool :=
  asmRegImmOk asmConfig8 (.inl .add) (.reg 2)
private def regImmXorMinus1 : Bool :=
  asmRegImmOk asmConfig8 (.inl .xor) (.imm (w8 255))
private def regImmXorOther : Bool :=
  asmRegImmOk asmConfig8 (.inl .xor) (.imm (w8 5))
private def arithBinopOk : Bool :=
  asmArithOk asmConfig8 (.binop .add 2 2 (.imm (w8 1)))
private def arithBinopTwoRegBad : Bool :=
  asmArithOk asmConfig8 (.binop .add 2 1 (.imm (w8 1)))
private def arithShiftOk : Bool :=
  asmArithOk asmConfig8 (.shift .lsl 2 2 (.imm (w8 3)))
private def arithShiftWidth : Bool :=
  asmArithOk asmConfig8 (.shift .lsl 2 2 (.imm (w8 8)))
private def arithDivOk : Bool := asmArithOk asmConfig8 (.div 1 2 3)
private def arithAddCarryOk : Bool :=
  asmArithOk asmConfig8 (.addCarry 1 2 3 4)
private def arithAddCarryBad : Bool :=
  asmArithOk asmConfig8 (.addCarry 1 2 1 4)
private def arithLongDivBad : Bool :=
  asmArithOk asmConfig8 (.longDiv 0 2 2 0 3)
private def fpLessOk : Bool := asmFpOk asmConfig8 (.fpLess 1 2 3)
private def fpFmaBad : Bool := asmFpOk asmConfig8 (.fpFma 1 2 3)
private def fpAbsTwoReg : Bool := asmFpOk asmConfig8 (.fpAbs 2 2)
private def cmpOk : Bool := asmCmpOk asmConfig8 .equal 2 (.imm (w8 1))
private def addrOffsetOk : Bool := asmAddrOffsetOk asmConfig8 (w8 8)
private def hwOffsetOk : Bool := asmHwOffsetOk asmConfig8 (w8 8)
private def byteOffsetOk : Bool := asmByteOffsetOk asmConfig8 (w8 101)
private def jumpOffsetOk : Bool := asmJumpOffsetOk asmConfig8 (w8 200)
private def jumpOffsetUnaligned : Bool := asmJumpOffsetOk asmConfig8 (w8 3)
private def instConstOk : Bool := asmInstOk asmConfig8 (.const 2 (w8 0))
private def instArithOk : Bool := asmInstOk asmConfig8 (.arith (.div 1 2 3))
private def instFpOk : Bool := asmInstOk asmConfig8 (.fp (.fpLess 1 2 3))
private def instMemLoadOk : Bool :=
  asmInstOk asmConfig8 (.mem .load 2 (.addr 2 (w8 8)))
private def instMemHwOk : Bool :=
  asmInstOk asmConfig8 (.mem .load16 2 (.addr 2 (w8 8)))
private def instMemByteOk : Bool :=
  asmInstOk asmConfig8 (.mem .load8 2 (.addr 2 (w8 8)))
private def stackAddrLoad : Bool := asmAddrOk asmConfig8 .load (.addr 2 (w8 8))
private def stackAddrHw : Bool := asmAddrOk asmConfig8 .load16 (.addr 2 (w8 8))
private def stackAddrByte : Bool := asmAddrOk asmConfig8 .store8 (.addr 2 (w8 8))
private def signedHighLeZero : Bool := decide ((w8 128).toInt ≤ (w8 0).toInt)
private def unsignedHighLeZero : Bool := decide ((w8 128) < (w8 0))
private def signedOffsetBounds : Bool := asmOffsetOk 0 (w8 0, w8 255) (w8 200)

private def asmOkInstConst : Bool := asmOk asmConfig8 (.inst (.const 2 (w8 0)))
private def asmOkJump : Bool := asmOk asmConfig8 (.jump (w8 100))
private def asmOkJumpCmp : Bool := asmOk asmConfig8 (.jumpCmp .equal 1 (.reg 2) (w8 100))
private def asmOkCallNone : Bool := asmOk asmConfig8 (.call (w8 100))
private def asmOkJumpReg : Bool := asmOk asmConfig8 (.jumpReg 3)
private def asmOkLoc : Bool := asmOk asmConfig8 (.loc 1 (w8 100))

private def asmConfigGuard : Bool :=
  aligned0 == true && aligned2 == true && unaligned2 == false &&
  regOk2 == true && regOk3 == false && regOk8 == false &&
  fpRegOk3 == true && fpRegOk4 == false &&
  regImmReg == true && regImmXorMinus1 == true && regImmXorOther == true &&
  arithBinopOk == true && arithBinopTwoRegBad == false &&
  arithShiftOk == true && arithShiftWidth == false &&
  arithDivOk == false && arithAddCarryOk == false &&
  arithAddCarryBad == false && arithLongDivBad == false &&
  fpLessOk == true && fpFmaBad == false && fpAbsTwoReg == false &&
  cmpOk == true &&
  addrOffsetOk == true && hwOffsetOk == true && byteOffsetOk == false &&
  jumpOffsetOk == false && jumpOffsetUnaligned == false &&
  instConstOk == true && instArithOk == false && instFpOk == true &&
  instMemLoadOk == true && instMemHwOk == true && instMemByteOk == true &&
  stackAddrLoad == true && stackAddrHw == true && stackAddrByte == true &&
  signedHighLeZero == true && unsignedHighLeZero == false &&
  signedOffsetBounds == false &&
  asmOkInstConst == true && asmOkJump == true && asmOkJumpCmp == true &&
  asmOkCallNone == false && asmOkJumpReg == false && asmOkLoc == true

#guard asmConfigGuard

example : asmRegImmOk asmConfig8 (.inl .xor) (.imm (w8 255)) = true := rfl
example : asmOffsetOk 2 (w8 0, w8 200) (w8 200) = false := rfl
example : asmAligned 2 (w8 200) = true := rfl

def runChecks : IO Bool := do
  if aligned0 && aligned2 && !unaligned2 then
    IO.println "PASS asm alignment clears the low bits"
  else
    IO.println "FAIL asm alignment"
  if regOk2 && !regOk3 && !regOk8 && fpRegOk3 && !fpRegOk4 then
    IO.println "PASS asm register validity respects reg_count and avoid_regs"
  else
    IO.println "FAIL asm register validity"
  if regImmReg && regImmXorMinus1 && regImmXorOther then
    IO.println "PASS asm immediate validity includes the Xor -1 exception"
  else
    IO.println "FAIL asm immediate validity"
  if arithBinopOk && !arithBinopTwoRegBad && arithShiftOk && !arithShiftWidth &&
      !arithDivOk && !arithLongDivBad then
    IO.println "PASS asm arith validity matches the HOL clauses"
  else
    IO.println "FAIL asm arith validity"
  if fpLessOk && !fpFmaBad && !fpAbsTwoReg then
    IO.println "PASS asm fp validity matches the HOL clauses"
  else
    IO.println "FAIL asm fp validity"
  if cmpOk && addrOffsetOk && hwOffsetOk && !byteOffsetOk && !jumpOffsetOk &&
      !jumpOffsetUnaligned then
    IO.println "PASS asm offset validity uses signed bounds"
  else
    IO.println "FAIL asm offset validity"
  if instConstOk && !instArithOk && instFpOk && instMemLoadOk && instMemHwOk &&
      instMemByteOk then
    IO.println "PASS asm instruction validity delegates to the predicates"
  else
    IO.println "FAIL asm instruction validity"
  if stackAddrLoad && stackAddrHw && stackAddrByte then
    IO.println "PASS stackProps addr_ok selects the memop offset kind"
  else
    IO.println "FAIL stackProps addr_ok"
  if asmOkInstConst && asmOkJump && asmOkJumpCmp && !asmOkCallNone &&
      !asmOkJumpReg && asmOkLoc then
    IO.println "PASS asm validity covers the full Inst/Jump/JumpCmp/Call/JumpReg/Loc carrier"
  else
    IO.println "FAIL asm validity over the full carrier"
  pure asmConfigGuard

end Flapjack.Test.AsmConfigChecksParity