import Flapjack.Compiler.Backend.LabLang

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

end Flapjack.Compiler.Backend.LabProps
