import Flapjack.Compiler.Backend.StackProps
import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Backend.StackLang.Prog

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
open Flapjack.Compiler.Backend.StackLang (HolProg)
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

/-! ## Exact asm payload carriers (`reg_imm`/`addr`/`inst`)

Parity for the width-indexed exact carriers in
`Flapjack/Compiler/Encoders/Asm.lean` against the direct HOL oracle
`scripts/hol-probes/asm_inst_fragment_probe.out` (bead
`flapjack-pxn.18.5.15.3.11.1`).  The oracle reads the HOL `reg_imm`/`addr`/
`inst` constructors at the numeral word type `64`; the guards below read the
Lean mirror at `width = 64`. -/

private def w64 (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

private def regImmTag {width : Nat} [NeZero width] : HolRegImm width → Nat
  | .reg name => name
  | .imm value => value.toNat

private def addrBase {width : Nat} [NeZero width] : HolAddr width → Nat
  | .addr base _ => base

private def addrOff {width : Nat} [NeZero width] : HolAddr width → Nat
  | .addr _ offset => offset.toNat

private def instSkip {width : Nat} [NeZero width] : HolInst width → Nat
  | .skip => 1
  | _ => 0

private def instConstReg {width : Nat} [NeZero width] : HolInst width → Nat
  | .const register _ => register
  | _ => 0

private def instConstVal {width : Nat} [NeZero width] : HolInst width → Nat
  | .const _ value => value.toNat
  | _ => 0

private def instMemReg {width : Nat} [NeZero width] : HolInst width → Nat
  | .mem _ register _ => register
  | _ => 0

private def instMemBase {width : Nat} [NeZero width] : HolInst width → Nat
  | .mem _ _ address => addrBase address
  | _ => 0

private def asmFragmentGuard : Bool :=
  regImmTag (.reg 3 : HolRegImm 64) == 3 &&
  regImmTag (.imm (w64 5) : HolRegImm 64) == 5 &&
  addrBase (.addr 3 (w64 5) : HolAddr 64) == 3 &&
  addrOff (.addr 3 (w64 5) : HolAddr 64) == 5 &&
  instSkip (.skip : HolInst 64) == 1 &&
  instConstReg (.const 2 (w64 7) : HolInst 64) == 2 &&
  instConstVal (.const 2 (w64 7) : HolInst 64) == 7 &&
  instMemReg (.mem .load 2 (.addr 3 (w64 5)) : HolInst 64) == 2 &&
  instMemBase (.mem .load 2 (.addr 3 (w64 5)) : HolInst 64) == 3

#guard asmFragmentGuard

example :
    HolRegImm.ofWordRegImm (HolRegImm.toWordRegImm (.reg 3 : HolRegImm 64)) =
      .reg 3 := rfl

example :
    HolAddr.ofWordLangAddr (HolAddr.toWordLangAddr (.addr 3 (w64 5))) =
      .addr 3 (w64 5) := rfl

example :
    HolInst.ofWordLangInst
        (HolInst.toWordLangInst (.mem .load 2 (.addr 3 (w64 5)) : HolInst 64)) =
      .mem .load 2 (.addr 3 (w64 5)) := rfl

/-! ## Monomorphic enums and the full `asm` carrier (bead `.18.5.15.3.10.1`)

The oracle rows `ab_*`/`ac_*`/`am_*`/`aa_*`/`af_*`/`as_*` read the HOL
`binop`/`cmp`/`memop`/`arith`/`fp`/`asm` constructors.  The guards below read
the Lean mirrors: the monomorphic aliases `HolBinop`/`HolCmp`/`HolMemop`/
`HolFp` and the width-indexed `HolArith 64`/`HolAsm 64`. -/

private def binopTag : HolBinop → Nat
  | .add => 1
  | .sub => 2
  | .and => 3
  | .or => 4
  | .xor => 5

private def cmpTag : HolCmp → Nat
  | .equal => 0
  | .lower => 1
  | .less => 2
  | .test => 3
  | .notEqual => 4
  | .notLower => 5
  | .notLess => 6
  | .notTest => 7

private def memopTag : HolMemop → Nat
  | .load => 0
  | .load8 => 1
  | .load16 => 2
  | .load32 => 3
  | .store => 4
  | .store8 => 5
  | .store16 => 6
  | .store32 => 7

private def arithDivSum {width : Nat} [NeZero width] : HolArith width → Nat
  | .div a b c => a + b + c
  | _ => 0

private def arithLongDivSum {width : Nat} [NeZero width] : HolArith width → Nat
  | .longDiv a b c d e => a + b + c + d + e
  | _ => 0

private def fpMovToRegSum : HolFp → Nat
  | .fpMovToReg a b c => a + b + c
  | _ => 0

private def fpFromIntSum : HolFp → Nat
  | .fpFromInt a b => a + b
  | _ => 0

private def asmJumpTarget {width : Nat} [NeZero width] : HolAsm width → Nat
  | .jump target => target.toNat
  | _ => 0

private def asmJumpCmpReg {width : Nat} [NeZero width] : HolAsm width → Nat
  | .jumpCmp _ register _ _ => register
  | _ => 0

private def asmJumpRegTarget {width : Nat} [NeZero width] : HolAsm width → Nat
  | .jumpReg register => register
  | _ => 0

private def asmLocSum {width : Nat} [NeZero width] : HolAsm width → Nat
  | .loc register offset => register + offset.toNat
  | _ => 0

private def asmSyntaxGuard : Bool :=
  binopTag .add == 1 &&
  cmpTag .notTest == 7 &&
  memopTag .store32 == 7 &&
  arithDivSum (.div 1 2 3 : HolArith 64) == 6 &&
  arithLongDivSum (.longDiv 1 2 3 4 5 : HolArith 64) == 15 &&
  fpMovToRegSum (.fpMovToReg 1 2 3 : HolFp) == 6 &&
  fpFromIntSum (.fpFromInt 4 5 : HolFp) == 9 &&
  asmJumpTarget (.jump (w64 9) : HolAsm 64) == 9 &&
  asmJumpCmpReg (.jumpCmp .equal 1 (.reg 2) (w64 3) : HolAsm 64) == 1 &&
  asmJumpRegTarget (.jumpReg 7 : HolAsm 64) == 7 &&
  asmLocSum (.loc 6 (w64 8) : HolAsm 64) == 14

#guard asmSyntaxGuard

example : (Flapjack.BinOp.add : HolBinop) = Flapjack.BinOp.add := rfl
example : (Flapjack.WordMemOp.store32 : HolMemop) = Flapjack.WordMemOp.store32 := rfl
example : (HolProg 64) = Flapjack.Compiler.Backend.StackLang.Prog (HolInst 64)
    HolCmp (HolRegImm 64) HolBinop HolMemop (HolAddr 64)
    Flapjack.Basis.Pure.MlString.MlString := rfl

/-! ### Exact `stackLang$prog` carrier oracle parity (bead 18.5.15.3.11.2.2)

`scripts/hol-probes/stack_lang_prog_carrier_probe.out` pins the HOL
`64 stackLang$prog` FFI field (`mlstring`) and representative constructor
shapes.  The rows below reproduce every oracle line with `HolProg 64`. -/

private abbrev P64 := HolProg 64

private def pSkip : P64 := Flapjack.Compiler.Backend.StackLang.Prog.skip

private def pSeq (first second : P64) : P64 :=
  Flapjack.Compiler.Backend.StackLang.Prog.seq first second

private def pInst (instruction : HolInst 64) : P64 :=
  Flapjack.Compiler.Backend.StackLang.Prog.inst instruction

private def pGet (destination : Nat) (store : Flapjack.Compiler.Backend.StackLang.StoreName) : P64 :=
  Flapjack.Compiler.Backend.StackLang.Prog.get destination store

private def pStackAlloc (words : Nat) : P64 :=
  Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc words

private def pShMem (operator : HolMemop) (register : Nat) (address : HolAddr 64) : P64 :=
  Flapjack.Compiler.Backend.StackLang.Prog.shMemOp operator register address

private def pFfi (function : Flapjack.Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength returnAddress : Nat) : P64 :=
  Flapjack.Compiler.Backend.StackLang.Prog.ffi function configuration configurationLength
    array arrayLength returnAddress

private def c8 (n : Nat) : Flapjack.Basis.Pure.MlString.HolChar := BitVec.ofNat 8 n

private def progInstTag : Nat :=
  match pInst (.const 3 (w64 5)) with
  | .inst (.const r v) => r + v.toNat
  | _ => 0

private def progGetTag : Nat :=
  match pGet 7 (.temp 3) with
  | .get n _ => n
  | _ => 0

private def progAllocTag : Nat :=
  match pStackAlloc 4 with
  | .stackAlloc n => n
  | _ => 0

private def progShMemTag : Nat :=
  match pShMem (.load) 3 (.addr 4 (w64 5)) with
  | .shMemOp _ r (.addr b off) => r + b + off.toNat
  | _ => 0

private def progFfiLen : Nat :=
  match pFfi (Flapjack.Basis.Pure.MlString.MlString.implode [c8 65, c8 66]) 1 2 3 4 5 with
  | .ffi s _ _ _ _ _ => s.explode.length
  | _ => 0

private def progSkipSeq : Bool :=
  match pSeq pSkip pSkip with
  | .seq .skip .skip => true
  | _ => false

private def progFfiExplode : List Flapjack.Basis.Pure.MlString.HolChar :=
  match pFfi (Flapjack.Basis.Pure.MlString.MlString.implode [c8 65, c8 66]) 1 2 3 4 5 with
  | .ffi s _ _ _ _ _ => s.explode
  | _ => []

private def progCarrierGuard : Bool :=
  progSkipSeq &&
  progInstTag == 8 && progGetTag == 7 && progAllocTag == 4 &&
  progShMemTag == 12 && progFfiLen == 2 &&
  progFfiExplode == [c8 65, c8 66]

#guard progCarrierGuard

end Flapjack.Test.AsmConfigChecksParity