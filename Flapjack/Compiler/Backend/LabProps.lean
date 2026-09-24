import Flapjack.Compiler.Backend.LabLang
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Backend.StackToLab

/-!
# Cake labProps pre-encoding predicates

The source clauses are `labPropsScript.sml:1247-1257`. The section/list
traversal and treatment of each line constructor are ported directly. HOL's
imported `asm`, `asm_config`, `asm_ok`, and `cbw_to_asm` definitions are
represented by the constructor/check operations below; this file does not
claim that the callbacks are the full HOL assembler configuration.
-/

namespace Flapjack.Compiler.Backend.LabProps

open Flapjack.Compiler.Backend.LabLang

/-- Imported HOL asm operations needed by `line_ok_pre` and its CBW adapter.

`instMem` constructs the HOL `Inst (Mem op r address)` asm carrier, and
`asmOk` is the supplied `asm_ok` predicate for the chosen configuration. -/
structure AsmChecks (Asm Memop Addr Word : Type) where
  zeroWord : Word
  addr : Nat → Word → Addr
  store8 : Memop
  instMem : Memop → Nat → Addr → Asm
  asmOk : Asm → Bool

/-- HOL `lab_to_target$cbw_to_asm` over explicit imported asm constructors. -/
def cbwToAsm {Asm Memop Addr Word : Type}
    (checks : AsmChecks Asm Memop Addr Word)
    (instruction : AsmOrCbw Asm Memop Addr) : Asm :=
  match instruction with
  | .asmi asm => asm
  | .cbw left right => checks.instMem checks.store8 right (checks.addr left checks.zeroWord)
  | .shareMem operator register address => checks.instMem operator register address

/-- HOL `labProps$line_ok_pre_def`; byte contents and length are ignored. -/
def lineOkPre {Asm Memop Addr Cmp RegImm MlString Word : Type}
    (checks : AsmChecks Asm Memop Addr Word)
    (line : Line (AsmOrCbw Asm Memop Addr)
      (AsmWithLab Cmp RegImm MlString) Word) : Bool :=
  match line with
  | .asm instruction _bytes _length => checks.asmOk (cbwToAsm checks instruction)
  | _ => true

/-- HOL `labProps$sec_ok_pre_def`. -/
def secOkPre {Asm Memop Addr Cmp RegImm MlString Word : Type}
    (checks : AsmChecks Asm Memop Addr Word)
    (sec : Section (Line (AsmOrCbw Asm Memop Addr)
      (AsmWithLab Cmp RegImm MlString) Word)) : Bool :=
  sec.lines.all (lineOkPre checks)

/-- HOL `labProps$all_enc_ok_pre` overload, pointwise over sections. -/
def allEncOkPre {Asm Memop Addr Cmp RegImm MlString Word : Type}
    (checks : AsmChecks Asm Memop Addr Word)
    (sections : List (Section (Line (AsmOrCbw Asm Memop Addr)
      (AsmWithLab Cmp RegImm MlString) Word))) : Bool :=
  sections.all (secOkPre checks)

/-- Concrete instantiation of the `line_ok_pre` callback record from a faithful
`AsmConfig`, so `line_ok_pre`/`sec_ok_pre`/`all_enc_ok_pre` can be stated over
the same configuration `c` that `stackProps$stack_asm_ok_def` consumes. This
fills the configuration gap noted for bead `flapjack-pxn.18.5.15.9.5`; the
`flatten`-side precondition proof remains open there. -/
def asmConfigChecks {width : Nat}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width) :
    AsmChecks (Flapjack.Compiler.Encoders.Asm.AsmData width) WordMemOp
      (WordLangAddr (BitVec width)) (BitVec width) where
  zeroWord := 0
  addr := fun base offset => .addr base offset
  store8 := .store8
  instMem := fun operator register address => .inst (.mem operator register address)
  asmOk := Flapjack.Compiler.Encoders.Asm.asmOk config

/-- HOL `cbw_to_asm_def` at the concrete configuration: `Cbw` becomes
`Inst (Mem Store8 right (Addr left 0w))` and `ShareMem` becomes
`Inst (Mem op r ad)`. -/
theorem cbwToAsm_asmConfigChecks {width : Nat}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (instruction : AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width)
      WordMemOp (WordLangAddr (BitVec width))) :
    cbwToAsm (asmConfigChecks config) instruction =
      match instruction with
      | .asmi asm => asm
      | .cbw left right => .inst (.mem .store8 right (.addr left 0))
      | .shareMem operator register address => .inst (.mem operator register address) := by
  cases instruction <;> rfl

/-- HOL `labProps$line_ok_pre_def` over a concrete assembler configuration. -/
def lineOkPreConfig {width : Nat}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (line : Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width)
      WordMemOp (WordLangAddr (BitVec width)))
      (AsmWithLab Cmp Nat MlString) (BitVec width)) : Bool :=
  lineOkPre (asmConfigChecks config) line

/-- HOL `labProps$sec_ok_pre_def` over a concrete assembler configuration. -/
def secOkPreConfig {width : Nat}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (sec : Section (Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width)
      WordMemOp (WordLangAddr (BitVec width)))
      (AsmWithLab Cmp Nat MlString) (BitVec width))) : Bool :=
  secOkPre (asmConfigChecks config) sec

/-- HOL `labProps$all_enc_ok_pre` over a concrete assembler configuration. -/
def allEncOkPreConfig {width : Nat}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (sections : List (Section (Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width)
      WordMemOp (WordLangAddr (BitVec width)))
      (AsmWithLab Cmp Nat MlString) (BitVec width)))) : Bool :=
  allEncOkPre (asmConfigChecks config) sections


/-- Concrete `FlattenOps` for the pipeline's assembler carrier: the embedded
constructors are `asm$Skip`, `asm$Inst`, `asm$JumpReg`, `asm$Reg`, `asm$Lower`
and the `negate` table from `cakeml/compiler/backend/stack_to_labScript.sml:24-32`,
all over the faithful `AsmData`/`WordLangInst`/`WordRegImm` carriers. These
constructors are independent of the `asm_config` record, so no configuration
argument is required. -/
def flattenOps {width : Nat} :
    StackToLab.FlattenOps (WordLangInst (BitVec width)) Flapjack.Cmp
      (WordRegImm (BitVec width)) (Encoders.Asm.AsmData width) where
  skip := .inst .skip
  embedInst := fun instruction => .inst instruction
  jumpReg := fun register => .jumpReg register
  reg := fun register => .reg register
  lower := .lower
  negate := fun operator =>
    match operator with
    | .less => .notLess
    | .equal => .notEqual
    | .lower => .notLower
    | .test => .notTest
    | .notLess => .less
    | .notEqual => .equal
    | .notLower => .lower
    | .notTest => .test

end Flapjack.Compiler.Backend.LabProps

