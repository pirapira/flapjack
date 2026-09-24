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

/-- HOL `labProps$line_ok_pre_def` over a concrete assembler configuration. -/
def lineOkPreConfig {width : Nat} {RegImm : Type}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (line : Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width)
      WordMemOp (WordLangAddr (BitVec width)))
      (AsmWithLab Cmp RegImm MlString) (BitVec width)) : Bool :=
  lineOkPre (asmConfigChecks config) line

/-- HOL `labProps$sec_ok_pre_def` over a concrete assembler configuration. -/
def secOkPreConfig {width : Nat} {RegImm : Type}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (sec : Section (Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData width)
      WordMemOp (WordLangAddr (BitVec width)))
      (AsmWithLab Cmp RegImm MlString) (BitVec width))) : Bool :=
  secOkPre (asmConfigChecks config) sec

/-- HOL `labProps$all_enc_ok_pre` over a concrete assembler configuration. -/
def allEncOkPreConfig {width : Nat} {RegImm : Type}
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
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.tick : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_tick]
  simp [lineOkPreConfig_flattenOps_skip]

theorem flatten_inst_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (instruction : WordLangInst (BitVec width)) (sectionId next : Nat)
    (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.inst instruction : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = Flapjack.Compiler.Encoders.Asm.asmInstOk config instruction := by
  rw [StackToLab.flatten_inst]
  simp [lineOkPreConfig_flattenOps_embedInst]

theorem flatten_halt_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (label sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.halt label : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_halt]
  simp [lineOkPreConfig_labAsm]

theorem flatten_raise_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (register sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.raise register : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = Flapjack.Compiler.Encoders.Asm.asmRegOk config register := by
  rw [StackToLab.flatten_raise]
  simp [lineOkPreConfig_flattenOps_jumpReg]

theorem flatten_ret_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (register sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.ret register : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = Flapjack.Compiler.Encoders.Asm.asmRegOk config register := by
  rw [StackToLab.flatten_ret]
  simp [lineOkPreConfig_flattenOps_jumpReg]

theorem flatten_rawCall_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (target sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.rawCall target : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_rawCall]
  simp [lineOkPreConfig_labAsm]

theorem flatten_locValue_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (register label entry sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.locValue register label entry : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_locValue]
  simp [lineOkPreConfig_labAsm]

theorem flatten_break_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (index sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.break index : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_break]
  simp [lineOkPreConfig_labAsm]

theorem flatten_continue_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (index sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.continue index : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten_continue]
  simp [lineOkPreConfig_labAsm]

theorem flatten_shMemOp_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (operator : WordMemOp) (register : Nat) (address : WordLangAddr (BitVec width))
    (sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.shMemOp operator register address : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) =
      Flapjack.Compiler.Encoders.Asm.asmOk config (.inst (.mem operator register address)) := by
  rw [StackToLab.flatten_shMemOp]
  simp [lineOkPreConfig_asm_shareMem]

theorem flatten_codeBufferWrite_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (left right sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
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

theorem flatten_jumpLower_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (left right target sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.jumpLower left right target : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten]
  simp [lineOkPreConfig_labAsm]

theorem flatten_ffi_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (function : String) (sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.ffi function 0 0 0 0 next : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten]
  simp [lineOkPreConfig_labAsm, lineOkPreConfig_label]

theorem flatten_install_lines_all (config : Flapjack.Compiler.Encoders.Asm.AsmConfig width)
    (tail : Bool) (sectionId next : Nat) (conts breaks : List Nat) :
    ((StackToLab.flatten (flattenOps (width := width)) 0 tail
        (.install 0 0 0 0 next : FlattenProg width) sectionId next conts breaks).1.all
        (lineOkPreConfig config)) = true := by
  rw [StackToLab.flatten]
  simp [lineOkPreConfig_labAsm, lineOkPreConfig_label]

end FlattenBaseLinesAll

end Flapjack.Compiler.Backend.LabProps



