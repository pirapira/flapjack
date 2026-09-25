import Flapjack.Compiler.Backend.LabLang
import Flapjack.Compiler.Backend.LabSem
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Backend.StackToLab
import Flapjack.Compiler.Backend.StackProps

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

/-- Executable Boolean counterpart of HOL `sec_ends_with_label`. The tagged
predicate below has HOL's proposition-valued statement shape. -/
def secEndsWithLabel {AsmOrCbw AsmWithLab Word : Type}
    (sec : Section (Line AsmOrCbw AsmWithLab Word)) : Bool :=
  match sec.lines.reverse with
  | [] => false
  | line :: _ => LabSem.isLabel line

/-- HOL `labProps$sec_ends_with_label_def` (`labPropsScript.sml:81`):
`sec_ends_with_label (Section _ ls) ⇔ ¬NULL ls ∧ is_Label (LAST ls)`. The
reverse-head rendering has the same nonempty/final-line cases and returns a
proposition, as HOL's predicate does. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_ends_with_label_def"]
def secEndsWithLabelHOL {AsmOrCbw AsmWithLab Word : Type}
    (sec : Section (Line AsmOrCbw AsmWithLab Word)) : Prop :=
  match sec.lines.reverse with
  | [] => False
  | line :: _ => LabSem.isLabel line = true

/-- The executable Boolean check and HOL-shaped predicate agree. -/
theorem secEndsWithLabelHOL_iff_bool {AsmOrCbw AsmWithLab Word : Type}
    (sec : Section (Line AsmOrCbw AsmWithLab Word)) :
    secEndsWithLabelHOL sec ↔ secEndsWithLabel sec = true := by
  unfold secEndsWithLabelHOL secEndsWithLabel
  cases sec.lines.reverse with
  | nil => simp
  | cons line rest => simp

/-! Structural lemmas about the section/encoding predicates (needed by
`compile_all_enc_ok_pre`). -/
section EncodingAllLemmas

variable {Asm Memop Addr Cmp RegImm MlString Word : Type}
variable (checks : AsmChecks Asm Memop Addr Word)

theorem allEncOkPre_cons (head : Section (Line (AsmOrCbw Asm Memop Addr)
      (AsmWithLab Cmp RegImm MlString) Word))
    (tail : List (Section (Line (AsmOrCbw Asm Memop Addr)
      (AsmWithLab Cmp RegImm MlString) Word))) :
    allEncOkPre checks (head :: tail) =
      (secOkPre checks head && allEncOkPre checks tail) := by
  simp [allEncOkPre]

end EncodingAllLemmas

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

/-! HOL `labProps$line_ok_pre_def` over a concrete assembler configuration.

The exact HOL instantiation is `'a labLang$line` at `'a = BitVec width`, whose
carrier is `Line (AsmOrCbw (AsmData width) WordMemOp (WordLangAddr (BitVec
width))) (AsmWithLab Cmp (HolRegImm width) MlString) (BitVec width)`:
`AsmData width` is the tagged `asm` port, `WordMemOp` the eight-constructor
`asm$memop`, `WordLangAddr (BitVec width)` HOL `addr`, `HolRegImm width` HOL
`reg_imm`, and the message type is the exact `MlString`. Because this definition
is generic in `RegImm`/`MlString`, an all-instantiations `@[hol]` tag would
over-claim; the tag is deliberately withheld pending review (bead
`flapjack-pxn.18.5.15.9.5.5`). `secOkPreConfig`/`allEncOkPreConfig`.
Direct HOL `EVAL` rows: `scripts/hol-probes/lab_props_line_ok_pre_probe.out`
(14 rows); Lean fixtures: `Flapjack/Test/LabPropsLineOkPreParity.lean`. -/
def lineOkPreConfig {width : Nat} {RegImm MlString : Type}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (line : Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width)
      WordMemOp (WordLangAddr (BitVec width)))
      (AsmWithLab Cmp RegImm MlString) (BitVec width)) : Bool :=
  lineOkPre (asmConfigChecks config) line

/-- HOL `labProps$sec_ok_pre_def` over a concrete assembler configuration. -/
def secOkPreConfig {width : Nat} {RegImm MlString : Type}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (sec : Section (Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width)
      WordMemOp (WordLangAddr (BitVec width)))
      (AsmWithLab Cmp RegImm MlString) (BitVec width))) : Bool :=
  secOkPre (asmConfigChecks config) sec

/-- HOL `labProps$all_enc_ok_pre` over a concrete assembler configuration. -/
def allEncOkPreConfig {width : Nat} {RegImm MlString : Type}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (sections : List (Section (Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width)
      WordMemOp (WordLangAddr (BitVec width)))
      (AsmWithLab Cmp RegImm MlString) (BitVec width)))) : Bool :=
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


/-! ## `line_ok_pre` reductions at a concrete configuration

These evaluate HOL `line_ok_pre` on the line shapes emitted by `flatten`,
tying the emitted assembler constructors to `asm_ok`. -/
section LineOkPreReductions

private abbrev LineC (width : Nat) (RegImm : Type) (MlString : Type) : Type :=
  Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width) WordMemOp
      (WordLangAddr (BitVec width)))
    (AsmWithLab Cmp RegImm MlString) (BitVec width)

variable {width : Nat} {RegImm : Type} {MlString : Type}

theorem lineOkPreConfig_asm_asmi (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (asm : Flapjack.Compiler.Encoders.Asm.AsmData width) (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.asmi asm) bytes length : LineC width RegImm MlString) =
      Flapjack.Compiler.Encoders.Asm.asmOk config asm := by
  simp [lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm]

theorem lineOkPreConfig_asm_cbw (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (left right : Nat) (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.cbw left right) bytes length : LineC width RegImm MlString) =
      Flapjack.Compiler.Encoders.Asm.asmOk config (.inst (.mem .store8 right (.addr left 0))) := by
  simp [lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm]

theorem lineOkPreConfig_asm_shareMem (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (operator : WordMemOp) (register : Nat) (address : WordLangAddr (BitVec width))
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.shareMem operator register address) bytes length : LineC width RegImm MlString) =
      Flapjack.Compiler.Encoders.Asm.asmOk config (.inst (.mem operator register address)) := by
  simp [lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm]

theorem lineOkPreConfig_label (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (sectionId label length : Nat) :
    lineOkPreConfig config (.label sectionId label length : LineC width RegImm MlString) = true := by
  simp [lineOkPreConfig, lineOkPre]

theorem lineOkPreConfig_asm_asmi_inst (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width) (instruction : WordLangInst (BitVec width))
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.asmi (.inst instruction)) bytes length : LineC width RegImm MlString) =
      Flapjack.Compiler.Encoders.Asm.asmInstOk config instruction := by
  simp [lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm, Encoders.Asm.asmOk]

theorem lineOkPreConfig_asm_asmi_jump (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width) (target : BitVec width)
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.asmi (.jump target)) bytes length : LineC width RegImm MlString) =
      Flapjack.Compiler.Encoders.Asm.asmJumpOffsetOk config target := by
  simp [lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm, Encoders.Asm.asmOk]

theorem lineOkPreConfig_asm_asmi_jumpReg (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width) (target : Nat)
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.asmi (.jumpReg target)) bytes length : LineC width RegImm MlString) =
      Flapjack.Compiler.Encoders.Asm.asmRegOk config target := by
  simp [lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm, Encoders.Asm.asmOk]

theorem lineOkPreConfig_asm_asmi_loc (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width) (register : Nat) (offset : BitVec width)
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.asmi (.loc register offset)) bytes length : LineC width RegImm MlString) =
      (Flapjack.Compiler.Encoders.Asm.asmRegOk config register && Flapjack.Compiler.Encoders.Asm.asmLocOffsetOk config offset) := by
  simp [lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm, Encoders.Asm.asmOk]

theorem lineOkPreConfig_asm_asmi_inst_skip (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.asmi (.inst .skip)) bytes length : LineC width RegImm MlString) = true := by
  simp [lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm, Encoders.Asm.asmOk, Encoders.Asm.asmInstOk]

theorem lineOkPreConfig_flattenOps_skip (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.asmi flattenOps.skip) bytes length : LineC width RegImm MlString) = true := by
  simp [flattenOps, lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm, Encoders.Asm.asmOk, Encoders.Asm.asmInstOk]

theorem lineOkPreConfig_flattenOps_embedInst (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (instruction : WordLangInst (BitVec width)) (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.asmi (flattenOps.embedInst instruction)) bytes length : LineC width RegImm MlString) =
      Flapjack.Compiler.Encoders.Asm.asmInstOk config instruction := by
  simp [flattenOps, lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm, Encoders.Asm.asmOk]

theorem lineOkPreConfig_flattenOps_jumpReg (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width) (register : Nat)
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.asm (.asmi (flattenOps.jumpReg register)) bytes length : LineC width RegImm MlString) =
      Flapjack.Compiler.Encoders.Asm.asmRegOk config register := by
  simp [flattenOps, lineOkPreConfig, lineOkPre, asmConfigChecks, cbwToAsm, Encoders.Asm.asmOk]

theorem lineOkPreConfig_labAsm (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (instruction : AsmWithLab Cmp RegImm MlString) (zero : BitVec width)
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreConfig config (.labAsm instruction zero bytes length : LineC width RegImm MlString) = true := by
  simp [lineOkPreConfig, lineOkPre]

end LineOkPreReductions

/-! Base-case corollaries: for each non-recursive `Prog` constructor the single
line emitted by `flatten` satisfies `line_ok_pre`, matching the HOL leaf cases of
`flatten_line_ok_pre` (`stack_to_labProofScript.sml:3629-3671`). -/
section FlattenBaseLinesAll

variable {width : Nat}

private abbrev FlattenProg (width : Nat) : Type :=
  StackLang.Prog (WordLangInst (BitVec width)) Flapjack.Cmp (WordRegImm (BitVec width))
    Flapjack.BinOp WordMemOp (WordLangAddr (BitVec width)) String

theorem flatten_tick_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.tick : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_tick]
  simp [lineOkPreConfig_flattenOps_skip]

theorem flatten_inst_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (instruction : WordLangInst (BitVec width)) (sectionId next : Nat)
    (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.inst instruction : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = Flapjack.Compiler.Encoders.Asm.asmInstOk config instruction := by
  rw [StackToLab.flatten_inst]
  simp [lineOkPreConfig_flattenOps_embedInst]

theorem flatten_halt_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (label sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.halt label : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_halt]
  simp [lineOkPreConfig_labAsm]

theorem flatten_raise_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (register sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.raise register : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = Flapjack.Compiler.Encoders.Asm.asmRegOk config register := by
  rw [StackToLab.flatten_raise]
  simp [lineOkPreConfig_flattenOps_jumpReg]

theorem flatten_ret_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (register sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.ret register : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = Flapjack.Compiler.Encoders.Asm.asmRegOk config register := by
  rw [StackToLab.flatten_ret]
  simp [lineOkPreConfig_flattenOps_jumpReg]

theorem flatten_rawCall_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (target sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.rawCall target : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_rawCall]
  simp [lineOkPreConfig_labAsm]

theorem flatten_locValue_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (register label entry sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.locValue register label entry : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_locValue]
  simp [lineOkPreConfig_labAsm]

theorem flatten_break_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (index sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.break index : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_break]
  simp [lineOkPreConfig_labAsm]

theorem flatten_continue_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (index sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.continue index : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_continue]
  simp [lineOkPreConfig_labAsm]

theorem flatten_shMemOp_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (operator : WordMemOp) (register : Nat) (address : WordLangAddr (BitVec width))
    (sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.shMemOp operator register address : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) =
      Flapjack.Compiler.Encoders.Asm.asmOk config (.inst (.mem operator register address)) := by
  rw [StackToLab.flatten_shMemOp]
  simp [lineOkPreConfig_asm_shareMem]

theorem flatten_codeBufferWrite_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (left right sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.codeBufferWrite left right : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) =
      Flapjack.Compiler.Encoders.Asm.asmOk config (.inst (.mem .store8 right (.addr left 0))) := by
  rw [StackToLab.flatten_codeBufferWrite]
  simp [lineOkPreConfig_asm_cbw]


/-- Generic composition step for the `flatten` line-ok induction: the `Seq`
case appends the two recursive outputs (with an optional `Label` when `tail`).
The hypotheses are universally quantified over the updated label counter, as in
HOL's `flatten_ind`. -/
theorem flatten_seq_lines_all {Asm Memop Addr Cmp RegImm MlString Word : Type}
    (_checks : AsmChecks Asm Memop Addr Word)
    {Inst Binop AsmInst : Type} (ops : StackToLab.FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)
    (tail : Bool) (first second : Flapjack.Compiler.Backend.StackLang.Prog Inst Cmp RegImm Binop Memop Addr MlString)
    (sectionId next : Nat) (conts breaks : List Nat)
    (P : StackToLab.FlatLine Memop Addr Cmp RegImm MlString AsmInst Word → Bool)
    (ih1 : ∀ n, (StackToLab.flatten ops zero false first sectionId n conts breaks).1.all P = true)
    (ih2 : ∀ n, (StackToLab.flatten ops zero false second sectionId n conts breaks).1.all P = true)
    (hlabel : P (.label sectionId 1 0) = true) :
    (StackToLab.flatten ops zero tail (.seq first second) sectionId next conts breaks).1.all P = true := by
  simp only [StackToLab.flatten]
  cases h1 : StackToLab.flatten ops zero false first sectionId next conts breaks with
  | mk xs r1 =>
    cases r1 with
    | mk r1x nx =>
      cases h2 : StackToLab.flatten ops zero false second sectionId nx conts breaks with
      | mk ys r2 =>
        cases r2 with
        | mk r2x ny =>
          have ih1' : xs.all P = true := by simpa [h1] using ih1 next
          have ih2' : ys.all P = true := by simpa [h2] using ih2 nx
          by_cases ht : tail
          · simp only [ht, if_true, List.all_append, List.all_cons, List.all_nil, ih1', ih2', hlabel]
            decide
          · simp only [ht, Bool.false_eq_true, if_false, List.all_append, ih1', ih2']
            decide

theorem flatten_loop_lines_all {Asm Memop Addr Cmp RegImm MlString Word : Type}
    (_checks : AsmChecks Asm Memop Addr Word) {Inst Binop AsmInst : Type}
    (ops : StackToLab.FlattenOps Inst Cmp RegImm AsmInst) (zero : Word) (tail : Bool)
    (body : Flapjack.Compiler.Backend.StackLang.Prog Inst Cmp RegImm Binop Memop Addr MlString)
    (sectionId next : Nat) (conts breaks : List Nat)
    (P : StackToLab.FlatLine Memop Addr Cmp RegImm MlString AsmInst Word -> Bool)
    (ih : (StackToLab.flatten ops zero false body sectionId (next + 2) (next :: conts)
        ((next + 1) :: breaks)).1.all P = true)
    (hlabel : forall k, P (.label sectionId k 0) = true)
    (hjump : forall k, P (.labAsm (.jump (.lab sectionId k)) zero [] 0) = true) :
    (StackToLab.flatten ops zero tail (.loop body) sectionId next conts breaks).1.all P = true := by
  simp only [StackToLab.flatten]
  cases h : StackToLab.flatten ops zero false body sectionId (next + 2) (next :: conts)
      ((next + 1) :: breaks) with
  | mk xs r1 =>
    cases r1 with
    | mk r1x nxb =>
      have ih' : xs.all P = true := by simpa [h] using ih
      simp only [List.all_cons, List.all_nil, List.all_append, ih', hlabel, hjump]
      decide

/-- Generic composition step for the `flatten` line-ok induction: the `Ite`
case selects one of six label/`jumpCmp` sequences. Every line it emits is a
`Label` or a `LabAsm`, so no instruction-validity obligation arises; the two
recursive outputs are discharged by the universally quantified hypotheses. -/
theorem flatten_ite_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (condition : Flapjack.Cmp) (register : Nat)
    (right : Flapjack.WordRegImm (BitVec width))
    (thenBranch elseBranch : FlattenProg width) (sectionId next : Nat)
    (conts breaks : List Nat)
    (ihThen : ∀ n, (StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false thenBranch
        sectionId n conts breaks).1.all (lineOkPreConfig config) = true)
    (ihElse : ∀ n, (StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false elseBranch
        sectionId n conts breaks).1.all (lineOkPreConfig config) = true) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.ite condition register right thenBranch elseBranch : FlattenProg width)
        sectionId next conts breaks).1.all (lineOkPreConfig config)) = true := by
  simp only [StackToLab.flatten]
  cases h1 : StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false thenBranch
      sectionId next conts breaks with
  | mk xs r1 =>
    cases r1 with
    | mk nr1 nx =>
      cases h2 : StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false elseBranch
          sectionId nx conts breaks with
      | mk ys r2 =>
        cases r2 with
        | mk nr2 ny =>
          have ihT : xs.all (lineOkPreConfig config) = true := by simpa only [h1] using ihThen next
          have ihE : ys.all (lineOkPreConfig config) = true := by simpa only [h2] using ihElse nx
          by_cases hc1 : (StackToLab.stackIsSkip thenBranch && StackToLab.stackIsSkip elseBranch) = true
          · simp only [if_pos hc1]
            rfl
          · by_cases hc2 : StackToLab.stackIsSkip thenBranch = true
            · simp only [if_neg hc1, if_pos hc2, List.all_append, List.all_cons, List.all_nil,
                ihE, lineOkPreConfig_labAsm, lineOkPreConfig_label]
              rfl
            · by_cases hc3 : StackToLab.stackIsSkip elseBranch = true
              · simp only [if_neg hc1, if_neg hc2, if_pos hc3, List.all_append, List.all_cons,
                  List.all_nil, ihT, lineOkPreConfig_labAsm, lineOkPreConfig_label]
                rfl
              · by_cases hc4 : nr1 = true
                · simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_pos hc4, List.all_append,
                    List.all_cons, List.all_nil, ihT, ihE, lineOkPreConfig_labAsm,
                    lineOkPreConfig_label]
                  rfl
                · by_cases hc5 : nr2 = true
                  · simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_pos hc5,
                      List.all_append, List.all_cons, List.all_nil, ihT, ihE,
                      lineOkPreConfig_labAsm, lineOkPreConfig_label]
                    rfl
                  · simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5,
                      List.all_append, List.all_cons, List.all_nil, ihT, ihE,
                      lineOkPreConfig_labAsm, lineOkPreConfig_label]
                    rfl

private abbrev FlatLineC (width : Nat) : Type :=
  StackToLab.FlatLine WordMemOp (WordLangAddr (BitVec width)) Flapjack.Cmp
    (WordRegImm (BitVec width)) String (Flapjack.Compiler.Encoders.Asm.AsmData width) (BitVec width)

theorem flatten_call_none_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (target : Sum Nat Nat) (handler : Option (FlattenProg width × Nat × Nat))
    (sectionId next : Nat) (conts breaks : List Nat)
    (hjump : lineOkPreConfig config
      (StackToLab.compileJump (flattenOps (width := width)) (0 : BitVec width) target : FlatLineC width) = true) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.call none target handler : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten]
  simp only [List.all_cons, List.all_nil]
  rw [hjump]
  rfl

theorem flatten_call_some_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (returnProgram : FlattenProg width) (linkRegister returnSection returnLabel : Nat)
    (target : Sum Nat Nat) (handler : Option (FlattenProg width × Nat × Nat))
    (sectionId next : Nat) (conts breaks : List Nat)
    (hjump : lineOkPreConfig config
      (StackToLab.compileJump (flattenOps (width := width)) (0 : BitVec width) target : FlatLineC width) = true)
    (ihRet : ∀ n, (StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false returnProgram
        sectionId n conts breaks).1.all (lineOkPreConfig config) = true)
    (ihHandler : ∀ (handlerProgram : FlattenProg width) (_handlerSection _handlerLabel n : Nat),
      (StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false handlerProgram
        sectionId n conts breaks).1.all (lineOkPreConfig config) = true) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.call (some (returnProgram, linkRegister, returnSection, returnLabel)) target handler : FlattenProg width)
        sectionId next conts breaks).1.all (lineOkPreConfig config)) = true := by
  simp only [StackToLab.flatten]
  cases h1 : StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false returnProgram
      sectionId next conts breaks with
  | mk xs r1 => cases r1 with | mk nr1 nx =>
    have ihR : xs.all (lineOkPreConfig config) = true := by simpa only [h1] using ihRet next
    cases handler with
    | none =>
        simp only [List.all_append, List.all_cons, List.all_nil, ihR, hjump,
          lineOkPreConfig_labAsm, lineOkPreConfig_label]
        rfl
    | some triple =>
        obtain ⟨handlerProgram, handlerSection, handlerLabel⟩ := triple
        cases h2 : StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false handlerProgram
            sectionId nx conts breaks with
        | mk ys r2 => cases r2 with | mk nr2 ny =>
          have ihH : ys.all (lineOkPreConfig config) = true := by
            simpa only [h2] using ihHandler handlerProgram handlerSection handlerLabel nx
          simp only [h2, List.all_append, List.all_cons, List.all_nil, ihR, ihH, hjump,
            lineOkPreConfig_labAsm, lineOkPreConfig_label]
          rfl

/-- `Call (some ...) _ none` variant of the composition step: the bundled
`flatten_call_some_lines_all` requires a handler obligation even when the
handler is `none`, which the `stackAsmOk`-carrying induction cannot supply for
an arbitrary handler program.  This variant keeps only the return obligation. -/
theorem flatten_call_some_none_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (returnProgram : FlattenProg width) (linkRegister returnSection returnLabel : Nat)
    (target : Sum Nat Nat) (sectionId next : Nat) (conts breaks : List Nat)
    (hjump : lineOkPreConfig config
      (StackToLab.compileJump (flattenOps (width := width)) (0 : BitVec width) target : FlatLineC width) = true)
    (ihRet : ∀ n, (StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false returnProgram
        sectionId n conts breaks).1.all (lineOkPreConfig config) = true) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.call (some (returnProgram, linkRegister, returnSection, returnLabel)) target none : FlattenProg width)
        sectionId next conts breaks).1.all (lineOkPreConfig config)) = true := by
  simp only [StackToLab.flatten]
  cases h1 : StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false returnProgram
      sectionId next conts breaks with
  | mk xs r1 => cases r1 with | mk nr1 nx =>
    have ihR : xs.all (lineOkPreConfig config) = true := by simpa only [h1] using ihRet next
    simp only [List.all_append, List.all_cons, List.all_nil, ihR, hjump,
      lineOkPreConfig_labAsm, lineOkPreConfig_label]
    rfl

/-- `Call (some ...) _ (some ...)` variant of the composition step taking the
handler obligation at any label counter, so the `stackAsmOk`-carrying
induction can discharge it from the handler program's own hypothesis. -/
theorem flatten_call_some_some_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (returnProgram : FlattenProg width) (linkRegister returnSection returnLabel : Nat)
    (target : Sum Nat Nat) (handlerProgram : FlattenProg width) (handlerSection handlerLabel : Nat)
    (sectionId next : Nat) (conts breaks : List Nat)
    (hjump : lineOkPreConfig config
      (StackToLab.compileJump (flattenOps (width := width)) (0 : BitVec width) target : FlatLineC width) = true)
    (ihRet : ∀ n, (StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false returnProgram
        sectionId n conts breaks).1.all (lineOkPreConfig config) = true)
    (ihHandler : ∀ n, (StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false handlerProgram
        sectionId n conts breaks).1.all (lineOkPreConfig config) = true) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.call (some (returnProgram, linkRegister, returnSection, returnLabel)) target
          (some (handlerProgram, handlerSection, handlerLabel)) : FlattenProg width)
        sectionId next conts breaks).1.all (lineOkPreConfig config)) = true := by
  simp only [StackToLab.flatten]
  cases h1 : StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false returnProgram
      sectionId next conts breaks with
  | mk xs r1 => cases r1 with | mk nr1 nx =>
    have ihR : xs.all (lineOkPreConfig config) = true := by simpa only [h1] using ihRet next
    cases h2 : StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) false handlerProgram
        sectionId nx conts breaks with
    | mk ys r2 => cases r2 with | mk nr2 ny =>
      have ihH : ys.all (lineOkPreConfig config) = true := by
        simpa only [h2] using ihHandler nx
      simp only [List.all_append, List.all_cons, List.all_nil, ihR, ihH, hjump,
        lineOkPreConfig_labAsm, lineOkPreConfig_label]
      rfl

theorem lineOkPreConfig_compileJump_inl (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (sectionId : Nat) :
    lineOkPreConfig config
      (StackToLab.compileJump (flattenOps (width := width)) (0 : BitVec width) (.inl sectionId) : FlatLineC width) = true := by
  simp [StackToLab.compileJump, lineOkPreConfig_labAsm]

theorem lineOkPreConfig_compileJump_inr (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (register : Nat) :
    lineOkPreConfig config
      (StackToLab.compileJump (flattenOps (width := width)) (0 : BitVec width) (.inr register) : FlatLineC width) =
        Flapjack.Compiler.Encoders.Asm.asmRegOk config register := by
  simp [StackToLab.compileJump, lineOkPreConfig_flattenOps_jumpReg]

theorem flatten_jumpLower_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (left right target sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.jumpLower left right target : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten]
  simp [lineOkPreConfig_labAsm]

theorem flatten_ffi_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (function : String) (sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.ffi function 0 0 0 0 next : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten]
  simp [lineOkPreConfig_labAsm, lineOkPreConfig_label]

theorem flatten_install_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail
        (.install 0 0 0 0 next : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten]
  simp [lineOkPreConfig_labAsm, lineOkPreConfig_label]

end FlattenBaseLinesAll

/-
Compatibility facts pulling the per-constructor validity information out of
`StackProps.stackAsmOk` instantiated with the real `asm_config` predicates, so
the `flatten_line_ok_pre` induction can discharge its hypotheses from HOL's
`stack_asm_ok c p` and `byte_offset_ok c 0w` premises. -/
section StackAsmOkBridge

variable {width : Nat} (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)

theorem stackAsmOk_asmChecksOfConfig_inst
    (instruction : WordLangInst (BitVec width))
    (h : StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.inst instruction : FlattenProg width) = true) :
    Flapjack.Compiler.Encoders.Asm.asmInstOk config instruction = true := by
  simpa [StackProps.stackAsmOk, StackProps.asmChecksOfConfig] using h

theorem stackAsmOk_asmChecksOfConfig_shMemOp
    (operator : WordMemOp) (register : Nat) (address : WordLangAddr (BitVec width))
    (h : StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.shMemOp operator register address : FlattenProg width) = true) :
    (Flapjack.Compiler.Encoders.Asm.asmRegOk config register &&
      StackProps.asmAddrOk config operator address) = true := by
  simpa [StackProps.stackAsmOk, StackProps.asmChecksOfConfig] using h

theorem stackAsmOk_asmChecksOfConfig_raise
    (register : Nat)
    (h : StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.raise register : FlattenProg width) = true) :
    (register < config.regCount && !config.avoidRegs.contains register) = true := by
  simpa [StackProps.stackAsmOk, StackProps.asmChecksOfConfig] using h

theorem stackAsmOk_asmChecksOfConfig_ret
    (register : Nat)
    (h : StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.ret register : FlattenProg width) = true) :
    (register < config.regCount && !config.avoidRegs.contains register) = true := by
  simpa [StackProps.stackAsmOk, StackProps.asmChecksOfConfig] using h

theorem stackAsmOk_asmChecksOfConfig_codeBufferWrite
    (left right : Nat)
    (h : StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.codeBufferWrite left right : FlattenProg width) = true) :
    (left < config.regCount && right < config.regCount &&
      !config.avoidRegs.contains left && !config.avoidRegs.contains right) = true := by
  simpa [StackProps.stackAsmOk, StackProps.asmChecksOfConfig] using h

/- Decomposition lemmas for the recursive `stackAsmOk` constructors, used by the
`flatten_line_ok_pre` induction to split a program obligation into its
sub-program obligations. -/

theorem stackAsmOk_asmChecksOfConfig_seq
    (first second : FlattenProg width) :
    (StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.seq first second : FlattenProg width) = true) ↔
      (StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) first = true ∧
        StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) second = true) := by
  simp [StackProps.stackAsmOk, StackProps.asmChecksOfConfig, Bool.and_eq_true]

theorem stackAsmOk_asmChecksOfConfig_ite
    (condition : Cmp) (register : Nat) (right : WordRegImm (BitVec width))
    (thenBranch elseBranch : FlattenProg width) :
    (StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.ite condition register right thenBranch elseBranch : FlattenProg width) = true) ↔
      (StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) thenBranch = true ∧
        StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) elseBranch = true) := by
  simp [StackProps.stackAsmOk, StackProps.asmChecksOfConfig, Bool.and_eq_true]

theorem stackAsmOk_asmChecksOfConfig_loop
    (body : FlattenProg width) :
    (StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.loop body : FlattenProg width) = true) ↔
      StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) body = true := by
  simp [StackProps.stackAsmOk, StackProps.asmChecksOfConfig]

theorem stackAsmOk_asmChecksOfConfig_call_some_inl_none
    (returnProgram : FlattenProg width) (linkRegister returnSection returnLabel sectionId : Nat) :
    (StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.call (some (returnProgram, linkRegister, returnSection, returnLabel))
          (.inl sectionId) none : FlattenProg width) = true) ↔
      StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) returnProgram = true := by
  simp [StackProps.stackAsmOk, StackProps.asmChecksOfConfig]

theorem stackAsmOk_asmChecksOfConfig_call_some_inl_some
    (returnProgram : FlattenProg width) (linkRegister returnSection returnLabel sectionId : Nat)
    (handlerProgram : FlattenProg width) (handlerSection handlerLabel : Nat) :
    (StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
        (.call (some (returnProgram, linkRegister, returnSection, returnLabel))
          (.inl sectionId) (some (handlerProgram, handlerSection, handlerLabel)) :
            FlattenProg width) = true) ↔
      (StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) returnProgram = true ∧
        StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) handlerProgram = true) := by
  simp [StackProps.stackAsmOk, StackProps.asmChecksOfConfig, Bool.and_eq_true]

theorem stackAsmOk_asmChecksOfConfig_call_none_inl
    (sectionId : Nat) (handler : Option (FlattenProg width × Nat × Nat)) :
    StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
      (.call none (.inl sectionId) handler : FlattenProg width) = true := by
  simp [StackProps.stackAsmOk, StackProps.asmChecksOfConfig]

theorem stackAsmOk_asmChecksOfConfig_call_none_inr
    (register : Nat) (handler : Option (FlattenProg width × Nat × Nat)) :
    StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
      (.call none (.inr register) handler : FlattenProg width) =
      Flapjack.Compiler.Encoders.Asm.asmRegOk config register := by
  simp [StackProps.stackAsmOk, StackProps.asmChecksOfConfig, Flapjack.Compiler.Encoders.Asm.asmRegOk]

theorem stackAsmOk_asmChecksOfConfig_call_some_inr_none
    (returnProgram : FlattenProg width) (linkRegister returnSection returnLabel register : Nat) :
    StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
      (.call (some (returnProgram, linkRegister, returnSection, returnLabel))
        (.inr register) none : FlattenProg width) =
      (Flapjack.Compiler.Encoders.Asm.asmRegOk config register &&
        StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) returnProgram) := by
  simp [StackProps.stackAsmOk, StackProps.asmChecksOfConfig, Flapjack.Compiler.Encoders.Asm.asmRegOk]

theorem stackAsmOk_asmChecksOfConfig_call_some_inr_some
    (returnProgram : FlattenProg width) (linkRegister returnSection returnLabel register : Nat)
    (handlerProgram : FlattenProg width) (handlerSection handlerLabel : Nat) :
    StackProps.stackAsmOk (StackProps.asmChecksOfConfig config)
      (.call (some (returnProgram, linkRegister, returnSection, returnLabel))
        (.inr register) (some (handlerProgram, handlerSection, handlerLabel)) :
          FlattenProg width) =
      (Flapjack.Compiler.Encoders.Asm.asmRegOk config register &&
        StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) returnProgram &&
        StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) handlerProgram) := by
  simp [StackProps.stackAsmOk, StackProps.asmChecksOfConfig, Flapjack.Compiler.Encoders.Asm.asmRegOk,
    Bool.and_assoc]

end StackAsmOkBridge

/-
Flat-representation form of HOL `stack_to_labProofScript.sml:3629-3671`
`flatten_line_ok_pre` (the top-level `flatten` induction).  Lean
`StackToLab.flatten` already concatenates the emitted line lists with `++`,
whereas the HOL statement uses `misc$append` over a `line list list`; this
theorem is therefore untagged.  The recursive cases delegate to the landed
`flatten_<ctor>_lines_all` composition lemmas and the `stackAsmOk` bridge. -/
section FlattenLineOkPre

variable {width : Nat}

theorem flatten_line_ok_pre (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (program : FlattenProg width) (tail : Bool) (sectionId next : Nat)
    (conts breaks : List Nat)
    (hbyte : Flapjack.Compiler.Encoders.Asm.asmByteOffsetOk config (0 : BitVec width) = true)
    (hok : StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) program = true) :
    ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail program
      sectionId next conts breaks).1.all (lineOkPreConfig config)) = true := by
  have hmain : ∀ (n : Nat),
      (∀ (program : FlattenProg width), sizeOf program ≤ n →
        ∀ (tail : Bool) (sectionId next : Nat) (conts breaks : List Nat),
          StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) program = true →
          Flapjack.Compiler.Encoders.Asm.asmByteOffsetOk config (0 : BitVec width) = true →
          ((StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail program
            sectionId next conts breaks).1.all (lineOkPreConfig config)) = true) := by
    intro n
    exact Nat.strongRecOn n (fun n ih => by
      intro program hle tail sectionId next conts breaks hok hbyte
      cases program with
      | skip => simp [StackToLab.flatten]
      | get _ _ => simp [StackToLab.flatten]
      | «set» _ _ => simp [StackToLab.flatten]
      | opCurrHeap _ _ _ => simp [StackToLab.flatten]
      | alloc _ => simp [StackToLab.flatten]
      | storeConsts _ _ _ => simp [StackToLab.flatten]
      | dataBufferWrite _ _ => simp [StackToLab.flatten]
      | stackAlloc _ => simp [StackToLab.flatten]
      | stackFree _ => simp [StackToLab.flatten]
      | stackStore _ _ => simp [StackToLab.flatten]
      | stackStoreAny _ _ => simp [StackToLab.flatten]
      | stackLoad _ _ => simp [StackToLab.flatten]
      | stackLoadAny _ _ => simp [StackToLab.flatten]
      | stackGetSize _ => simp [StackToLab.flatten]
      | stackSetSize _ => simp [StackToLab.flatten]
      | bitmapLoad _ _ => simp [StackToLab.flatten]
      | inst instruction =>
          rw [flatten_inst_lines_all config tail instruction sectionId next conts breaks]
          exact stackAsmOk_asmChecksOfConfig_inst config instruction hok
      | raise exception =>
          rw [flatten_raise_lines_all config tail exception sectionId next conts breaks]
          simpa [Flapjack.Compiler.Encoders.Asm.asmRegOk]
            using stackAsmOk_asmChecksOfConfig_raise config exception hok
      | ret value =>
          rw [flatten_ret_lines_all config tail value sectionId next conts breaks]
          simpa [Flapjack.Compiler.Encoders.Asm.asmRegOk]
            using stackAsmOk_asmChecksOfConfig_ret config value hok
      | shMemOp operator register address =>
          rw [flatten_shMemOp_lines_all config tail operator register address sectionId next conts breaks]
          cases address with
          | addr base offset =>
              simpa [Flapjack.Compiler.Encoders.Asm.asmOk, Flapjack.Compiler.Encoders.Asm.asmInstOk,
                Flapjack.Compiler.Encoders.Asm.asmRegOk, StackProps.asmAddrOk, Bool.and_assoc]
                using stackAsmOk_asmChecksOfConfig_shMemOp config operator register (.addr base offset) hok
      | codeBufferWrite left right =>
          rw [flatten_codeBufferWrite_lines_all config tail left right sectionId next conts breaks]
          have h := stackAsmOk_asmChecksOfConfig_codeBufferWrite config left right hok
          simp_all [Flapjack.Compiler.Encoders.Asm.asmOk, Flapjack.Compiler.Encoders.Asm.asmInstOk,
            Flapjack.Compiler.Encoders.Asm.asmRegOk]
      | tick => exact flatten_tick_lines_all config tail sectionId next conts breaks
      | halt register => exact flatten_halt_lines_all config tail register sectionId next conts breaks
      | rawCall target => exact flatten_rawCall_lines_all config tail target sectionId next conts breaks
      | locValue register label entry =>
          exact flatten_locValue_lines_all config tail register label entry sectionId next conts breaks
      | «break» label => exact flatten_break_lines_all config tail label sectionId next conts breaks
      | «continue» label => exact flatten_continue_lines_all config tail label sectionId next conts breaks
      | jumpLower left right target =>
          exact flatten_jumpLower_lines_all config tail left right target sectionId next conts breaks
      | ffi function _ _ _ _ returnAddress =>
          rw [StackToLab.flatten]
          simp [lineOkPreConfig_labAsm, lineOkPreConfig_label]
      | install _ _ _ _ returnAddress =>
          rw [StackToLab.flatten]
          simp [lineOkPreConfig_labAsm, lineOkPreConfig_label]
      | seq first second =>
          obtain ⟨h1ok, h2ok⟩ :=
            (stackAsmOk_asmChecksOfConfig_seq config first second).1 hok
          have hlt1 : sizeOf first < n := by
            have hsz : sizeOf first < sizeOf (StackLang.Prog.seq first second) := by
              decreasing_trivial
            omega
          have hlt2 : sizeOf second < n := by
            have hsz : sizeOf second < sizeOf (StackLang.Prog.seq first second) := by
              decreasing_trivial
            omega
          exact flatten_seq_lines_all (asmConfigChecks config) (flattenOps (width := width))
            (0 : BitVec width) tail first second sectionId next conts breaks (lineOkPreConfig config)
            (fun k => ih (sizeOf first) hlt1 first (Nat.le_refl _) false sectionId k conts breaks h1ok hbyte)
            (fun k => ih (sizeOf second) hlt2 second (Nat.le_refl _) false sectionId k conts breaks h2ok hbyte)
            (lineOkPreConfig_label config sectionId 1 0)
      | ite condition register right thenBranch elseBranch =>
          obtain ⟨htok, heok⟩ :=
            (stackAsmOk_asmChecksOfConfig_ite config condition register right thenBranch elseBranch).1 hok
          have hltt : sizeOf thenBranch < n := by
            have hsz : sizeOf thenBranch <
                sizeOf (StackLang.Prog.ite condition register right thenBranch elseBranch) := by
              decreasing_trivial
            omega
          have hlte : sizeOf elseBranch < n := by
            have hsz : sizeOf elseBranch <
                sizeOf (StackLang.Prog.ite condition register right thenBranch elseBranch) := by
              decreasing_trivial
            omega
          exact flatten_ite_lines_all config tail condition register right thenBranch elseBranch
            sectionId next conts breaks
            (fun k => ih (sizeOf thenBranch) hltt thenBranch (Nat.le_refl _) false sectionId k conts breaks htok hbyte)
            (fun k => ih (sizeOf elseBranch) hlte elseBranch (Nat.le_refl _) false sectionId k conts breaks heok hbyte)
      | loop body =>
          have hbok : StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) body = true :=
            (stackAsmOk_asmChecksOfConfig_loop config body).1 hok
          have hlt : sizeOf body < n := by
            have hsz : sizeOf body < sizeOf (StackLang.Prog.loop body) := by
              decreasing_trivial
            omega
          exact flatten_loop_lines_all (asmConfigChecks config) (flattenOps (width := width))
            (0 : BitVec width) tail body sectionId next conts breaks (lineOkPreConfig config)
            (ih (sizeOf body) hlt body (Nat.le_refl _) false sectionId (next + 2)
              (next :: conts) ((next + 1) :: breaks) hbok hbyte)
            (fun k => lineOkPreConfig_label config sectionId k 0)
            (fun k => lineOkPreConfig_labAsm config (.jump (.lab sectionId k)) (0 : BitVec width) [] 0)
      | call returnHandler target handler =>
          cases returnHandler with
          | none =>
              cases target with
              | inl targetSection =>
                  exact flatten_call_none_lines_all config tail (.inl targetSection) handler
                    sectionId next conts breaks
                    (lineOkPreConfig_compileJump_inl config targetSection)
              | inr register =>
                  have hreg : Flapjack.Compiler.Encoders.Asm.asmRegOk config register = true := by
                    rw [stackAsmOk_asmChecksOfConfig_call_none_inr config register handler] at hok
                    exact hok
                  exact flatten_call_none_lines_all config tail (.inr register) handler
                    sectionId next conts breaks
                    (by rw [lineOkPreConfig_compileJump_inr config register]; exact hreg)
          | some rhs =>
              obtain ⟨returnProgram, linkRegister, returnSection, returnLabel⟩ := rhs
              have hltRet : sizeOf returnProgram < n := by
                have hsz : sizeOf returnProgram <
                    sizeOf (StackLang.Prog.call
                      (some (returnProgram, linkRegister, returnSection, returnLabel)) target handler) := by
                  decreasing_trivial
                omega
              cases target with
              | inl targetSection =>
                  cases handler with
                  | none =>
                      have hrok :=
                        (stackAsmOk_asmChecksOfConfig_call_some_inl_none config returnProgram
                          linkRegister returnSection returnLabel targetSection).1 hok
                      exact flatten_call_some_none_lines_all config tail returnProgram linkRegister
                        returnSection returnLabel (.inl targetSection) sectionId next conts breaks
                        (lineOkPreConfig_compileJump_inl config targetSection)
                        (fun k => ih (sizeOf returnProgram) hltRet returnProgram (Nat.le_refl _)
                          false sectionId k conts breaks hrok hbyte)
                  | some hs =>
                      obtain ⟨handlerProgram, handlerSection, handlerLabel⟩ := hs
                      obtain ⟨hrok, hhok⟩ :=
                        (stackAsmOk_asmChecksOfConfig_call_some_inl_some config returnProgram
                          linkRegister returnSection returnLabel targetSection handlerProgram
                          handlerSection handlerLabel).1 hok
                      have hltHan : sizeOf handlerProgram < n := by
                        have hsz : sizeOf handlerProgram <
                            sizeOf (StackLang.Prog.call
                              (some (returnProgram, linkRegister, returnSection, returnLabel))
                              (.inl targetSection) (some (handlerProgram, handlerSection, handlerLabel))) := by
                          decreasing_trivial
                        omega
                      exact flatten_call_some_some_lines_all config tail returnProgram linkRegister
                        returnSection returnLabel (.inl targetSection) handlerProgram handlerSection
                        handlerLabel sectionId next conts breaks
                        (lineOkPreConfig_compileJump_inl config targetSection)
                        (fun k => ih (sizeOf returnProgram) hltRet returnProgram (Nat.le_refl _)
                          false sectionId k conts breaks hrok hbyte)
                        (fun k => ih (sizeOf handlerProgram) hltHan handlerProgram (Nat.le_refl _)
                          false sectionId k conts breaks hhok hbyte)
              | inr register =>
                  cases handler with
                  | none =>
                      rw [stackAsmOk_asmChecksOfConfig_call_some_inr_none config returnProgram
                          linkRegister returnSection returnLabel register] at hok
                      simp only [Bool.and_eq_true] at hok
                      obtain ⟨hreg, hrok⟩ := hok
                      exact flatten_call_some_none_lines_all config tail returnProgram linkRegister
                        returnSection returnLabel (.inr register) sectionId next conts breaks
                        (by rw [lineOkPreConfig_compileJump_inr config register]; exact hreg)
                        (fun k => ih (sizeOf returnProgram) hltRet returnProgram (Nat.le_refl _)
                          false sectionId k conts breaks hrok hbyte)
                  | some hs =>
                      obtain ⟨handlerProgram, handlerSection, handlerLabel⟩ := hs
                      rw [stackAsmOk_asmChecksOfConfig_call_some_inr_some config returnProgram
                          linkRegister returnSection returnLabel register handlerProgram
                          handlerSection handlerLabel] at hok
                      simp only [Bool.and_eq_true] at hok
                      obtain ⟨⟨hreg, hrok⟩, hhok⟩ := hok
                      have hltHan : sizeOf handlerProgram < n := by
                        have hsz : sizeOf handlerProgram <
                            sizeOf (StackLang.Prog.call
                              (some (returnProgram, linkRegister, returnSection, returnLabel))
                              (.inr register) (some (handlerProgram, handlerSection, handlerLabel))) := by
                          decreasing_trivial
                        omega
                      exact flatten_call_some_some_lines_all config tail returnProgram linkRegister
                        returnSection returnLabel (.inr register) handlerProgram handlerSection
                        handlerLabel sectionId next conts breaks
                        (by rw [lineOkPreConfig_compileJump_inr config register]; exact hreg)
                        (fun k => ih (sizeOf returnProgram) hltRet returnProgram (Nat.le_refl _)
                          false sectionId k conts breaks hrok hbyte)
                        (fun k => ih (sizeOf handlerProgram) hltHan handlerProgram (Nat.le_refl _)
                          false sectionId k conts breaks hhok hbyte)
      )
  exact hmain (sizeOf program) program (Nat.le_refl _) tail sectionId next conts breaks hok hbyte

/-- Flat-representation form of HOL `stack_to_labProofScript.sml`
`compile_all_enc_ok_pre`: every section produced by `prog_to_section` for a list
of `stack_asm_ok` programs satisfies `line_ok_pre`.  Untagged for the same
`misc$append` versus `++` representation reason as `flatten_line_ok_pre`. -/
theorem compile_all_enc_ok_pre (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (programs : List (Nat × FlattenProg width))
    (hbyte : Flapjack.Compiler.Encoders.Asm.asmByteOffsetOk config (0 : BitVec width) = true)
    (hok : programs.all (fun entry =>
      StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) entry.2) = true) :
    (programs.map (fun entry => StackToLab.progToSection (flattenOps (width := width))
      (0 : BitVec width) entry.1 entry.2)).all (secOkPreConfig config) = true := by
  induction programs with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨sectionId, program⟩ := head
    rw [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨hokHead, hokTail⟩ := hok
    rw [List.map_cons, List.all_cons]
    have hsec : secOkPreConfig config
        (StackToLab.progToSection (flattenOps (width := width)) (0 : BitVec width) sectionId program)
        = true := by
      simp only [StackToLab.progToSection, secOkPreConfig, secOkPre, List.all_append, List.all_cons,
        List.all_nil, Bool.and_eq_true]
      constructor
      · exact flatten_line_ok_pre config program true sectionId
          (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] [] hbyte hokHead
      · simp [lineOkPre]
    rw [hsec, ih hokTail]
    rfl


/-- Untagged Flapjack representation bridge/analogue of HOL
`stack_to_labProofScript.sml` `flatten_line_ok_pre`, whose statement is
`byte_offset_ok c 0w /\ stack_asm_ok c p /\ flatten t p n m cs bs = (ls,a,b)
==> EVERY (line_ok_pre c) (append ls)`. Here the conclusion is stated over
`flattenApp`/`appListAppend` with the Lean side conditions
`lineOkPreConfig`, `stackAsmOk (asmChecksOfConfig config)` and `asmByteOffsetOk`.

No `@[hol]` tag: the remaining representation gap is that `flattenApp` is
parameterised by `ops : FlattenOps ...` whereas HOL `flatten` is a single global
function over the imported assembler constructors (and the flat production
`flatten` is a separate Lean artefact). Derived from the flat
`flatten_line_ok_pre` through `flattenApp_appListFlatten_eq_flatten`. -/
theorem flattenApp_line_ok_pre (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (program : FlattenProg width) (tail : Bool) (sectionId next : Nat)
    (conts breaks : List Nat) (ls : AppList (FlatLineC width)) (a : Bool) (b : Nat)
    (hbyte : Flapjack.Compiler.Encoders.Asm.asmByteOffsetOk config (0 : BitVec width) = true)
    (hok : StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) program = true)
    (hflatten : StackToLab.flattenApp (flattenOps (width := width)) (0 : BitVec width) tail program
      sectionId next conts breaks = (ls, a, b)) :
    (appListAppend ls).all (lineOkPreConfig config) = true := by
  have hbridge := StackToLab.flattenApp_appListFlatten_eq_flatten (flattenOps (width := width))
    (0 : BitVec width) tail program sectionId next conts breaks
  have hflat := flatten_line_ok_pre config program tail sectionId next conts breaks hbyte hok
  rw [hflatten] at hbridge
  have hfst : appListAppend ls =
      (StackToLab.flatten (flattenOps (width := width)) (0 : BitVec width) tail program
        sectionId next conts breaks).1 := by
    simpa [appListFlatten] using congrArg Prod.fst hbridge
  rw [hfst]
  exact hflat


/-- Untagged Flapjack representation bridge/analogue of HOL
`stack_to_labProofScript.sml` `compile_all_enc_ok_pre`: every section produced by
the app-list `progToSectionApp` for a list of `stack_asm_ok` programs satisfies
`secOkPreConfig`, via `progToSectionApp_lines` and the flat
`compile_all_enc_ok_pre`. Not tagged for the same `ops` parameterisation gap as
`flattenApp_line_ok_pre`. -/
theorem compile_all_enc_ok_pre_app (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (programs : List (Nat × FlattenProg width))
    (hbyte : Flapjack.Compiler.Encoders.Asm.asmByteOffsetOk config (0 : BitVec width) = true)
    (hok : programs.all (fun entry =>
      StackProps.stackAsmOk (StackProps.asmChecksOfConfig config) entry.2) = true) :
    (programs.map (fun entry => StackToLab.progToSectionApp (flattenOps (width := width))
      (0 : BitVec width) entry.1 entry.2)).all (secOkPreConfig config) = true := by
  induction programs with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨sectionId, program⟩ := head
    rw [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨hokHead, hokTail⟩ := hok
    rw [List.map_cons, List.all_cons]
    have hsecEq : secOkPreConfig config
        (StackToLab.progToSectionApp (flattenOps (width := width)) (0 : BitVec width)
          sectionId program)
        = secOkPreConfig config
          (StackToLab.progToSection (flattenOps (width := width)) (0 : BitVec width)
            sectionId program) := by
      simp only [secOkPreConfig, secOkPre, StackToLab.progToSectionApp_lines]
    have hsecFlat : secOkPreConfig config
        (StackToLab.progToSection (flattenOps (width := width)) (0 : BitVec width)
          sectionId program) = true := by
      simp only [StackToLab.progToSection, secOkPreConfig, secOkPre, List.all_append,
        List.all_cons, List.all_nil, Bool.and_eq_true]
      constructor
      · exact flatten_line_ok_pre config program true sectionId
          (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] [] hbyte hokHead
      · simp [lineOkPre]
    have hsec : secOkPreConfig config
        (StackToLab.progToSectionApp (flattenOps (width := width)) (0 : BitVec width)
          sectionId program) = true := by
      rw [hsecEq]; exact hsecFlat
    rw [hsec, ih hokTail]
    rfl

end FlattenLineOkPre

/-! ## `sec_ends_with_label` and the `prog_to_section` label invariant

HOL `labProps$sec_ends_with_label_def` plus the proof-script corollary
`stack_to_labProofScript.sml:3620` `EVERY_sec_ends_with_label_MAP_prog_to_section`.
The corollary is stated as an untagged Flapjack analogue because `progToSection`
is parameterised by `ops : FlattenOps ...`, whereas HOL `prog_to_section` uses the
fixed global `flatten` (the same representation gap recorded for the app-list
bridges). -/
section SecEndsWithLabel

/-- A section whose lines are an arbitrary prefix followed by a `Label` ends with
a label. Structural core of `EVERY_sec_ends_with_label_MAP_prog_to_section`,
independent of the `FlattenOps` parameterisation. -/
theorem secEndsWithLabel_append_label {AsmOrCbw AsmWithLab Word : Type}
    (lines : List (Line AsmOrCbw AsmWithLab Word)) (sectionId label length : Nat) :
    secEndsWithLabel
        ({ sectionId := sectionId
           lines := lines ++ [.label sectionId label length] } :
          Section (Line AsmOrCbw AsmWithLab Word)) = true := by
  simp [secEndsWithLabel, LabSem.isLabel]

/-- `progToSection` output ends with a label. Untagged analogue of HOL
`EVERY_sec_ends_with_label_MAP_prog_to_section` (`stack_to_labProofScript.sml:3620`). -/
theorem secEndsWithLabel_progToSection
    {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
    (ops : StackToLab.FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)
    (sectionId : Nat)
    (program : StackLang.Prog Inst Cmp RegImm Binop Memop Addr MlString) :
    secEndsWithLabel
        (StackToLab.progToSection ops zero sectionId program) = true := by
  simp only [StackToLab.progToSection]
  exact secEndsWithLabel_append_label _ sectionId _ _

/-- HOL `EVERY_sec_ends_with_label_MAP_prog_to_section`
(`stack_to_labProofScript.sml:3620`): every section produced for a program list
ends with a label. Untagged because `progToSection` carries the `FlattenOps`
parameter absent from HOL's fixed global `flatten`. -/
theorem everySecEndsWithLabel_map_progToSection
    {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
    (ops : StackToLab.FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)
    (programs : List (Nat × StackLang.Prog Inst Cmp RegImm Binop Memop Addr MlString)) :
    (programs.map
        (fun entry => StackToLab.progToSection ops zero entry.1 entry.2)).all
      secEndsWithLabel = true := by
  rw [List.all_eq_true]
  intro sec hmem
  simp only [List.mem_map] at hmem
  obtain ⟨entry, _hentry, rfl⟩ := hmem
  exact secEndsWithLabel_progToSection ops zero entry.1 entry.2

end SecEndsWithLabel

end Flapjack.Compiler.Backend.LabProps
