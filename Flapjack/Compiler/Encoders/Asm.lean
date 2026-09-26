import Flapjack.HolRef
import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Backend.StackLang

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

/-! ## Exact width-indexed asm payload carriers

`stackLangScript.sml:24-67` types its word-carrying constructors
(`Inst ('a inst)`, `If cmp num ('a reg_imm) ...`, `ShMemOp memop num ('a addr)`)
through the HOL assembly carriers `asm$inst`, `asm$reg_imm`, `asm$addr`.  HOL
parameterises these by the word dimension `'a` (`imm = 'a word`), so the
faithful Lean counterparts are width-indexed; the generic mirrors in
`Flapjack.Pancake.WordLang` (`WordLangInst`, `WordRegImm`, `WordLangAddr`) are
still polymorphic in the word-value type and stay untagged.  The isomorphisms
below connect the exact carriers to those production carriers.

Exact HOL `asm$binop` (`cakeml/compiler/encoders/asm/asmScript.sml:78-80`):
`binop = Add | Sub | And | Or | Xor`.  Monomorphic and width-independent, so
the Lean mirror is the existing faithful `Flapjack.BinOp`; the alias below is
the exact-tagged name. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "binop"]
abbrev HolBinop := Flapjack.BinOp

/-- Exact HOL `asm$cmp` (`cakeml/compiler/encoders/asm/asmScript.sml:82-84`):
`cmp = Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest`.
Monomorphic and width-independent; the Lean mirror is the existing faithful
`Flapjack.Cmp`. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "cmp"]
abbrev HolCmp := Flapjack.Cmp

/-- Exact HOL `asm$memop` (`cakeml/compiler/encoders/asm/asmScript.sml:125-128`):
`memop = Load | Load8 | Load16 | Load32 | Store | Store8 | Store16 | Store32`.
Monomorphic and width-independent; the Lean mirror is the existing faithful
`Flapjack.WordMemOp`. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "memop"]
abbrev HolMemop := Flapjack.WordMemOp

/-- Exact HOL `asm$arith` (`cakeml/compiler/encoders/asm/asmScript.sml:86-95`):
`Binop binop reg reg ('a reg_imm) | Shift shift reg reg ('a reg_imm) | Div reg
reg reg | LongMul reg reg reg reg | LongDiv reg reg reg reg reg | AddCarry reg
reg reg reg | AddOverflow reg reg reg reg | SubOverflow reg reg reg reg`, with
`shift = ast$shift` (`cakeml/semantics/astScript.sml:21`).  The width-indexed
Lean mirror is definitionally the production generic `WordLangArith` at
`BitVec width`; the alias records the exact instantiation. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "arith"]
abbrev HolArith (width : Nat) [NeZero width] := WordLangArith (BitVec width)

/-- Exact HOL `asm$fp` (`cakeml/compiler/encoders/asm/asmScript.sml:97-119`),
16 constructors over `reg`/`fp_reg` (`num`).  Monomorphic and width-independent;
the Lean mirror is the existing faithful `Flapjack.WordLangFp`. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "fp"]
abbrev HolFp := WordLangFp

/-- Exact HOL `asm$reg_imm` (`cakeml/compiler/encoders/asm/asmScript.sml:74-76`):
`reg_imm = Reg reg | Imm ('a imm)` with `imm = 'a word`.  This is the payload
type of stackLang's `If`. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "reg_imm"]
inductive HolRegImm (width : Nat) [NeZero width] where
  | reg (name : Nat)
  | imm (value : BitVec width)
  deriving Repr

/-- Exact HOL `asm$addr` (`cakeml/compiler/encoders/asm/asmScript.sml:121-123`):
`addr = Addr reg ('a word)`.  This is the payload type of stackLang's
`ShMemOp`. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "addr"]
inductive HolAddr (width : Nat) [NeZero width] where
  | addr (base : Nat) (offset : BitVec width)
  deriving Repr

/-- Exact HOL `asm$inst` (`cakeml/compiler/encoders/asm/asmScript.sml:130-136`):
`inst = Skip | Const reg ('a word) | Arith ('a arith) | Mem memop reg ('a addr)
| FP fp`.  This is the payload type of stackLang's `Inst`.  `HolArith` and
`HolFp` are the exact `arith`/`fp` mirrors. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "inst"]
inductive HolInst (width : Nat) [NeZero width] where
  | skip
  | const (destination : Nat) (value : BitVec width)
  | arith (operation : HolArith width)
  | mem (operator : HolMemop) (destination : Nat) (address : HolAddr width)
  | fp (operation : HolFp)
  deriving Repr

namespace HolRegImm

/-- Forget the width index to the production `reg_imm` mirror. -/
def toWordRegImm {width : Nat} [NeZero width] : HolRegImm width → WordRegImm (BitVec width)
  | .reg name => .reg name
  | .imm value => .imm value

/-- Recover the exact carrier from the production `reg_imm` mirror. -/
def ofWordRegImm {width : Nat} [NeZero width] : WordRegImm (BitVec width) → HolRegImm width
  | .reg name => .reg name
  | .imm value => .imm value

@[simp] theorem of_to {width : Nat} [NeZero width] (carrier : HolRegImm width) :
    ofWordRegImm (toWordRegImm carrier) = carrier := by
  cases carrier <;> rfl

@[simp] theorem to_of {width : Nat} [NeZero width] (carrier : WordRegImm (BitVec width)) :
    toWordRegImm (ofWordRegImm carrier) = carrier := by
  cases carrier <;> rfl

end HolRegImm

namespace HolAddr

/-- Forget the width index to the production `addr` mirror. -/
def toWordLangAddr {width : Nat} [NeZero width] : HolAddr width → WordLangAddr (BitVec width)
  | .addr base offset => .addr base offset

/-- Recover the exact carrier from the production `addr` mirror. -/
def ofWordLangAddr {width : Nat} [NeZero width] : WordLangAddr (BitVec width) → HolAddr width
  | .addr base offset => .addr base offset

@[simp] theorem of_to {width : Nat} [NeZero width] (carrier : HolAddr width) :
    ofWordLangAddr (toWordLangAddr carrier) = carrier := by
  cases carrier <;> rfl

@[simp] theorem to_of {width : Nat} [NeZero width] (carrier : WordLangAddr (BitVec width)) :
    toWordLangAddr (ofWordLangAddr carrier) = carrier := by
  cases carrier <;> rfl

end HolAddr

namespace HolInst

/-- Forget the width index to the production `inst` mirror. -/
def toWordLangInst {width : Nat} [NeZero width] : HolInst width → WordLangInst (BitVec width)
  | .skip => .skip
  | .const destination value => .const destination value
  | .arith operation => .arith operation
  | .mem operator destination address => .mem operator destination address.toWordLangAddr
  | .fp operation => .fp operation

/-- Recover the exact carrier from the production `inst` mirror. -/
def ofWordLangInst {width : Nat} [NeZero width] : WordLangInst (BitVec width) → HolInst width
  | .skip => .skip
  | .const destination value => .const destination value
  | .arith operation => .arith operation
  | .mem operator destination address => .mem operator destination (HolAddr.ofWordLangAddr address)
  | .fp operation => .fp operation

@[simp] theorem of_to {width : Nat} [NeZero width] (carrier : HolInst width) :
    ofWordLangInst (toWordLangInst carrier) = carrier := by
  cases carrier with
  | skip => rfl
  | const destination value => rfl
  | arith operation => rfl
  | mem operator destination address => simp [toWordLangInst, ofWordLangInst]
  | fp operation => rfl

@[simp] theorem to_of {width : Nat} [NeZero width] (carrier : WordLangInst (BitVec width)) :
    toWordLangInst (ofWordLangInst carrier) = carrier := by
  cases carrier with
  | skip => rfl
  | const destination value => rfl
  | arith operation => rfl
  | mem operator destination address => simp [toWordLangInst, ofWordLangInst]
  | fp operation => rfl

end HolInst

/-- Exact HOL `asm$asm` (`cakeml/compiler/encoders/asm/asmScript.sml:138-145`):
`asm = Inst ('a inst) | Jump ('a word) | JumpCmp cmp reg ('a reg_imm) ('a word)
| Call ('a word) | JumpReg reg | Loc reg ('a word)`.  The width-indexed Lean
mirror uses the exact `HolInst`/`HolRegImm`/`HolCmp` carriers; the production
`AsmData` below is the generic-field carrier consumed by the assembler's
`encode` field. -/
@[hol "cakeml/compiler/encoders/asm/asmScript.sml" "asm"]
inductive HolAsm (width : Nat) [NeZero width] where
  | inst (value : HolInst width)
  | jump (target : BitVec width)
  | jumpCmp (operator : HolCmp) (source : Nat) (right : HolRegImm width)
      (target : BitVec width)
  | call (target : BitVec width)
  | jumpReg (target : Nat)
  | loc (register : Nat) (offset : BitVec width)
  deriving Repr


/-- HOL `asmScript.sml:139-146`:
`asm = Inst ('a inst) | Jump ('a word) | JumpCmp cmp reg ('a reg_imm) ('a word)
       | Call ('a word) | JumpReg reg | Loc reg ('a word)`.
The assembler's `encode` field consumes this full datatype, not just the
`Inst` payload.  This is the production generic-field rendering of the exact
`HolAsm` above (same constructor arity; fields instantiated at the generic
`WordLangInst`/`WordRegImm`/`Cmp` carriers rather than the exact `Hol*` ones). -/
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

/--
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    The HOL tag was withdrawn. -/
def asmRegOk {width : Nat} (config : AsmConfig width) (register : Nat) : Bool :=
  register < config.regCount && !config.avoidRegs.contains register

/--
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    The HOL tag was withdrawn. -/
def asmFpRegOk {width : Nat} (config : AsmConfig width) (register : Nat) : Bool :=
  register < config.fpRegCount

/--
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    The HOL tag was withdrawn. -/
def asmRegImmOk {width : Nat} (config : AsmConfig width) (operator : Sum BinOp Cmp) :
    WordRegImm (BitVec width) → Bool
  | .reg register => asmRegOk config register
  | .imm value =>
      (operator == .inl .xor && value == -1) || config.validImm operator value

/-- HOL `offset_ok_def` uses the signed word comparison `<=` (HOL's `<=` on
words is signed, unlike `word_ls`), so the bounds are compared as integers.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
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

/-- HOL `asmScript$arith_ok_def` (`asmScript.sml:191-229`).
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
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

/-- HOL `asmScript$fp_ok_def` (`asmScript.sml:231-268`).
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
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

/-- HOL `asmScript$cmp_ok_def` (`asmScript.sml:270-272`).
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def asmCmpOk {width : Nat} (config : AsmConfig width) (operator : Cmp)
    (register : Nat) (right : WordRegImm (BitVec width)) : Bool :=
  asmRegOk config register && asmRegImmOk config (.inr operator) right

/-- HOL `asmScript$inst_ok_def` (`asmScript.sml:286-299`).
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
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

/-- HOL `asmScript$asm_ok_def` (`asmScript.sml:301-313`).
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
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

`encode` is carried with the HOL field type but is a placeholder, so the
definition is named `riscvConfigForChecks`: the HOL value is
`riscv_enc = LIST_BIND riscv_encode ∘ riscv_ast`, whose instruction encoder is
not ported here, and a caller that read `encode` would silently emit empty
code. No validity predicate in this module (or in `stackProps$stack_asm_ok`)
reads `encode`, so every check-relevant projection is exact, but the record as
a whole is NOT a complete port and no `@[hol]` tag is attached. The exact
`riscv_ast`/`riscv_enc` field and production bridge is tracked by bead
`flapjack-pxn.18.5.15.9.11.1`. -/

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

/-- The RISC-V assembler configuration at 64-bit, for the check predicates
only. Check fields match HOL `riscv_config` exactly (see
`scripts/hol-probes/riscv_config_probe.out`); `encode` is the documented
placeholder, so this record is not a complete HOL `riscv_config` port and
carries no `@[hol]` tag. -/
def riscvConfigForChecks : AsmConfig 64 where
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
