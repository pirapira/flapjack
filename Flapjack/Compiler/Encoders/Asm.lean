import Flapjack.HolRef
import Flapjack.Pancake.WordLang

/-!
# Faithful assembler configuration validity predicates

Counterpart of `cakeml/compiler/encoders/asm/asmScript.sml`.  This module ports
the pure Boolean validity predicates that `stackProps$stack_asm_ok_def` and
`stackProps$addr_ok_def` consume: `reg_ok`, `fp_reg_ok`, `reg_imm_ok`,
`offset_ok` and its offset overloads, `arith_ok`, `fp_ok`, `cmp_ok`, and
`inst_ok`, over the faithful `asm` carrier types already present in
`Flapjack.Pancake.WordLang` (`WordLangInst`/`WordLangArith`/`WordLangFp`/
`WordLangAddr`).

The HOL `asm_config` record is represented with all of its fields so the
quantified configuration carrier is HOL-shaped: `ISA`, `encode`
(`'a asm -> word8 list`), `big_endian`, `code_alignment`, `link_reg`,
`avoid_regs`, `reg_count`, `fp_reg_count`, `two_reg_arith`, `valid_imm`, and
the six `(min, max)` offset pairs.  `encode` and `bigEndian` are carried for
carrier fidelity even though none of the validity predicates below read them.
Lean field names are
lowerCamel (`isa`, `codeAlignment`, ...) where HOL uses `ISA`,
`code_alignment`, ...; constructor arity and field types match the HOL
carriers.

`aligned p w` is ported as `asmAligned p w` (the low `p` bits of the word are
zero, matching `alignment$aligned_def`/`alignment$align_def`); the direct HOL
probe `scripts/hol-probes/asm_config_checks_probeScript.sml` checks that
correspondence together with the predicate clauses.
-/

namespace Flapjack.Compiler.Encoders.Asm

open Flapjack

/-! HOL's signed word order as a Boolean on the width-indexed Lean word.
This is the two's-complement interpretation of HOL's polymorphic word `<`;
it is kept local to the assembler counterpart rather than importing a
particular target's comparison instance. -/
def holAsmSignedLess {width : Nat} (left right : BitVec width) : Bool :=
  let sign := 2 ^ (width - 1)
  if left.toNat < sign then
    if right.toNat < sign then decide (left.toNat < right.toNat) else false
  else if right.toNat < sign then
    true
  else
    decide (left.toNat < right.toNat)

/-! Exact width-indexed source counterpart of CakeML
`asm$word_cmp_def` (`cakeml/compiler/encoders/asm/asmScript.sml:313-321`).
The result is Boolean as in HOL; the Crep evaluator separately embeds it as
a word. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "word_cmp_def"]
def wordCmpHOL [NeZero width] (operator : Cmp)
    (left right : BitVec width) : Bool :=
  match operator with
  | .equal => left == right
  | .less => holAsmSignedLess left right
  | .lower => decide (left < right)
  | .test => AndOp.and left right == 0
  | .notEqual => !(left == right)
  | .notLess => !(holAsmSignedLess left right)
  | .notLower => !(decide (left < right))
  | .notTest => AndOp.and left right != 0

/-! Flapjack's word-valued encoding of the Boolean result used by
`crepSem$eval`'s `bitstring$v2w [word_cmp ...]` clause. -/
def wordCmpResultHOL [NeZero width] (operator : Cmp)
    (left right : BitVec width) : BitVec width :=
  if wordCmpHOL operator left right then 1 else 0

/-- HOL `architecture` (`asmScript.sml:149-151`).  Distinct from the RISC-V
state-model `Flapjack.RiscV.Architecture`. -/
inductive AsmArchitecture where
  | armv7
  | armv8
  | mips
  | riscv
  | ag32
  | x86_64
  deriving DecidableEq, Repr

/-- HOL `asmScript.sml:139-146`:
`asm = Inst ('a inst) | Jump ('a word) | JumpCmp cmp reg ('a reg_imm) ('a word)
       | Call ('a word) | JumpReg reg | Loc reg ('a word)`.
The assembler's `encode` field consumes this full datatype, not just the
`Inst` payload. -/
inductive AsmData (width : Nat) where
  | inst (value : WordLangInst (BitVec width))
  | jump (target : BitVec width)
  | jumpCmp (operator : Cmp) (source : Nat) (right : WordRegImm (BitVec width))
      (target : BitVec width)
  | call (target : BitVec width)
  | jumpReg (target : Nat)
  | loc (register : Nat) (offset : BitVec width)
  deriving Repr

/-- The `asm_config` projections read by the HOL validity predicates
(`asmScript.sml:153-172`). -/
structure AsmConfig (width : Nat) where
  isa : AsmArchitecture
  encode : AsmData width → List UInt8
  bigEndian : Bool
  codeAlignment : Nat
  linkReg : Option Nat
  avoidRegs : List Nat
  regCount : Nat
  fpRegCount : Nat
  twoRegArith : Bool
  validImm : Sum BinOp Cmp → BitVec width → Bool
  addrOffset : BitVec width × BitVec width
  hwOffset : BitVec width × BitVec width
  byteOffset : BitVec width × BitVec width
  jumpOffset : BitVec width × BitVec width
  cjumpOffset : BitVec width × BitVec width
  locOffset : BitVec width × BitVec width

/-- HOL `alignment$aligned_def`: `aligned p w` clears the low `p` bits. -/
def asmAligned {width : Nat} (alignment : Nat) (value : BitVec width) : Bool :=
  value.toNat % 2 ^ alignment = 0

@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "reg_ok_def"]
def asmRegOk {width : Nat} (config : AsmConfig width) (register : Nat) : Bool :=
  register < config.regCount && !config.avoidRegs.contains register

@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "fp_reg_ok_def"]
def asmFpRegOk {width : Nat} (config : AsmConfig width) (register : Nat) : Bool :=
  register < config.fpRegCount

@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "reg_imm_ok_def"]
def asmRegImmOk {width : Nat} (config : AsmConfig width) (operator : Sum BinOp Cmp) :
    WordRegImm (BitVec width) → Bool
  | .reg register => asmRegOk config register
  | .imm value =>
      (operator == .inl .xor && value == -1) || config.validImm operator value

/-- HOL `offset_ok_def` uses the signed word comparison `<=` (HOL's `<=` on
words is signed, unlike `word_ls`), so the bounds are compared as integers. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "offset_ok_def"]
def asmOffsetOk {width : Nat} (alignment : Nat)
    (bounds : BitVec width × BitVec width) (offset : BitVec width) : Bool :=
  bounds.1.toInt ≤ offset.toInt && offset.toInt ≤ bounds.2.toInt &&
    asmAligned alignment offset

def asmAddrOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk 0 config.addrOffset offset

def asmHwOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk 0 config.hwOffset offset

def asmByteOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk 0 config.byteOffset offset

def asmJumpOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk config.codeAlignment config.jumpOffset offset

def asmCjumpOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk config.codeAlignment config.cjumpOffset offset

def asmLocOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk config.codeAlignment config.locOffset offset

/-- HOL `asmScript$arith_ok_def` (`asmScript.sml:191-229`). -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "arith_ok_def"]
def asmArithOk {width : Nat} (config : AsmConfig width) :
    WordLangArith (BitVec width) → Bool
  | .binop operator destination source right =>
      (!config.twoRegArith || destination == source ||
          (operator == .or && right == .reg source)) &&
        asmRegOk config destination && asmRegOk config source &&
        asmRegImmOk config (.inl operator) right
  | .shift operator destination source right =>
      (!config.twoRegArith || destination == source) &&
        asmRegOk config destination && asmRegOk config source &&
        (match right with
         | .imm value => (!(value == 0) || operator == .lsl) && value.toNat < width
         | .reg register =>
             asmRegOk config register && (!(config.isa == .x86_64) || register == 1))
  | .div destination dividend divisor =>
      asmRegOk config destination && asmRegOk config dividend &&
        asmRegOk config divisor &&
        (config.isa == .armv8 || config.isa == .mips || config.isa == .riscv)
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      asmRegOk config destinationLeft && asmRegOk config destinationRight &&
        asmRegOk config sourceLeft && asmRegOk config sourceRight &&
        (!(config.isa == .x86_64) ||
          (destinationLeft == 2 && destinationRight == 0 && sourceLeft == 0)) &&
        (!(config.isa == .armv7) || !(destinationLeft == destinationRight)) &&
        (!(config.isa == .armv8 || config.isa == .riscv || config.isa == .ag32) ||
          (!(destinationLeft == sourceLeft) && !(destinationLeft == sourceRight)))
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      (config.isa == .x86_64) && destinationLeft == 0 && destinationRight == 2 &&
        sourceLeft == 2 && sourceRight == 0 && asmRegOk config quotient
  | .addCarry destination result sourceLeft sourceRight =>
      (!config.twoRegArith || destination == result) &&
        asmRegOk config destination && asmRegOk config result &&
        asmRegOk config sourceLeft && asmRegOk config sourceRight &&
        (!(config.isa == .mips || config.isa == .riscv) ||
          (!(destination == sourceLeft) && !(destination == sourceRight)))
  | .addOverflow destination result sourceLeft sourceRight =>
      (!config.twoRegArith || destination == result) &&
        asmRegOk config destination && asmRegOk config result &&
        asmRegOk config sourceLeft && asmRegOk config sourceRight &&
        (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))
  | .subOverflow destination result sourceLeft sourceRight =>
      (!config.twoRegArith || destination == result) &&
        asmRegOk config destination && asmRegOk config result &&
        asmRegOk config sourceLeft && asmRegOk config sourceRight &&
        (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))

/-- HOL `asmScript$fp_ok_def` (`asmScript.sml:231-268`). -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "fp_ok_def"]
def asmFpOk {width : Nat} (config : AsmConfig width) : WordLangFp → Bool
  | .fpLess destination left right =>
      asmRegOk config destination && asmFpRegOk config left && asmFpRegOk config right
  | .fpLessEqual destination left right =>
      asmRegOk config destination && asmFpRegOk config left && asmFpRegOk config right
  | .fpEqual destination left right =>
      asmRegOk config destination && asmFpRegOk config left && asmFpRegOk config right
  | .fpAbs destination source =>
      (!config.twoRegArith || !(destination == source)) &&
        asmFpRegOk config destination && asmFpRegOk config source
  | .fpNeg destination source =>
      (!config.twoRegArith || !(destination == source)) &&
        asmFpRegOk config destination && asmFpRegOk config source
  | .fpSqrt destination source =>
      asmFpRegOk config destination && asmFpRegOk config source
  | .fpAdd destination left right =>
      (!config.twoRegArith || destination == left) && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fpSub destination left right =>
      (!config.twoRegArith || destination == left) && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fpMul destination left right =>
      (!config.twoRegArith || destination == left) && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fpDiv destination left right =>
      (!config.twoRegArith || destination == left) && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fpFma destination left right =>
      (config.isa == .armv7) && 2 < config.fpRegCount && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fpMov destination source =>
      asmFpRegOk config destination && asmFpRegOk config source
  | .fpMovToReg destinationInteger second sourceFloat =>
      asmRegOk config destinationInteger &&
        (!(width == 32) || (!(destinationInteger == second) && asmRegOk config second)) &&
        asmFpRegOk config sourceFloat
  | .fpMovFromReg destinationFloat destinationInteger second =>
      asmRegOk config destinationInteger &&
        (!(width == 32) || (!(destinationInteger == second) && asmRegOk config second)) &&
        asmFpRegOk config destinationFloat
  | .fpToInt destination source =>
      asmFpRegOk config destination && asmFpRegOk config source
  | .fpFromInt destination source =>
      asmFpRegOk config destination && asmFpRegOk config source

/-- HOL `asmScript$cmp_ok_def` (`asmScript.sml:270-272`). -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "cmp_ok_def"]
def asmCmpOk {width : Nat} (config : AsmConfig width) (operator : Cmp)
    (register : Nat) (right : WordRegImm (BitVec width)) : Bool :=
  asmRegOk config register && asmRegImmOk config (.inr operator) right

/-- HOL `asmScript$inst_ok_def` (`asmScript.sml:286-299`). -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "inst_ok_def"]
def asmInstOk {width : Nat} (config : AsmConfig width) : WordLangInst (BitVec width) → Bool
  | .skip => true
  | .const destination _ => asmRegOk config destination
  | .arith operation => asmArithOk config operation
  | .fp operation => asmFpOk config operation
  | .mem operator destination (.addr base offset) =>
      asmRegOk config destination && asmRegOk config base &&
        (if operator == .load || operator == .store || operator == .load32 ||
            operator == .store32 then
          asmAddrOffsetOk config offset
         else if operator == .load16 || operator == .store16 then
          asmHwOffsetOk config offset && !(config.isa == .ag32)
         else
          asmByteOffsetOk config offset)

/-- HOL `asmScript$asm_ok_def` (`asmScript.sml:301-313`). -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "asm_ok_def"]
def asmOk {width : Nat} (config : AsmConfig width) : AsmData width → Bool
  | .inst inner => asmInstOk config inner
  | .jump target => asmJumpOffsetOk config target
  | .jumpCmp operator source right target =>
      asmCjumpOffsetOk config target && asmCmpOk config operator source right
  | .call target =>
      (match config.linkReg with
        | some register => asmRegOk config register
        | none => false) &&
        asmJumpOffsetOk config target
  | .jumpReg target => asmRegOk config target
  | .loc register offset => asmRegOk config register && asmLocOffsetOk config offset


/-! ## RISC-V configuration

Exact 64-bit field values of HOL `riscv_config_def`
(`cakeml/compiler/encoders/riscv/riscv_targetScript.sml:277-304`).

`encode` is carried with the HOL field type but is a placeholder: the HOL
value is `riscv_enc = LIST_BIND riscv_encode ∘ riscv_ast`, whose instruction
encoder is not ported here. No validity predicate in this module (or in
`stackProps$stack_asm_ok`) reads `encode`, so every check-relevant projection
is exact; the encoder port is tracked by bead `flapjack-pxn.18.5.15.9.11`.
Because one field still differs from the HOL record value no `@[hol]` tag is
attached. -/

/-- HOL `min12` (`sw2sw (INT_MINw : word12) : word64`). -/
def riscvMin12 : BitVec 64 := BitVec.ofInt 64 (-2048)

/-- HOL `max12` (`sw2sw (INT_MAXw : word12) : word64`). -/
def riscvMax12 : BitVec 64 := BitVec.ofInt 64 2047

/-- HOL `min21` (`sw2sw (INT_MINw : 21 word) : word64`). -/
def riscvMin21 : BitVec 64 := BitVec.ofInt 64 (-1048576)

/-- HOL `max21` (`sw2sw (INT_MAXw : 21 word) : word64`). -/
def riscvMax21 : BitVec 64 := BitVec.ofInt 64 1048575

/-- HOL `min32` (`sw2sw (INT_MINw : word32) : word64`). -/
def riscvMin32 : BitVec 64 := BitVec.ofInt 64 (-2147483648)

/-- The `jump_offset`/`loc_offset` maximum `0x7FFFF7FFw`. -/
def riscvJumpMax : BitVec 64 := BitVec.ofNat 64 0x7FFFF7FF

/-- HOL `riscv_config.valid_imm`: `Sub` uses a strict lower bound, everything
else a non-strict one, both signed word comparisons. -/
def riscvValidImm : Sum BinOp Cmp → BitVec 64 → Bool := fun operator value =>
  (match operator with
    | .inl .sub => decide (riscvMin12.toInt < value.toInt)
    | _ => decide (riscvMin12.toInt ≤ value.toInt)) &&
  decide (value.toInt ≤ riscvMax12.toInt)

/-- The RISC-V assembler configuration at 64-bit. Check fields match HOL
`riscv_config` exactly (see `scripts/hol-probes/riscv_config_probe.out`);
`encode` is the documented placeholder. -/
def riscvConfig : AsmConfig 64 where
  isa := .riscv
  encode := fun _ => []
  bigEndian := false
  codeAlignment := 2
  linkReg := some 1
  avoidRegs := [0, 2, 3, 4, 31]
  regCount := 32
  fpRegCount := 0
  twoRegArith := false
  validImm := riscvValidImm
  addrOffset := (riscvMin12, riscvMax12)
  hwOffset := (riscvMin12, riscvMax12)
  byteOffset := (riscvMin12, riscvMax12)
  jumpOffset := (riscvMin32, riscvJumpMax)
  cjumpOffset := (riscvMin21 + 8, riscvMax21 + 4)
  locOffset := (riscvMin32, riscvJumpMax)

end Flapjack.Compiler.Encoders.Asm
