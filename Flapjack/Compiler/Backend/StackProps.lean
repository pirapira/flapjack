import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Encoders.Asm

/-!
# StackLang validity predicate port boundary

`stackPropsTheory.stack_asm_ok_def` (`stackPropsScript.sml:812-829`) recursively inspects Stack programs and
delegates `inst_ok`, `reg_ok`, and `addr_ok` to the assembler configuration.
This file ports those recursive clauses over `StackLang.Prog` while
exposing those three HOL predicates and the two configuration fields used
directly as an explicit projection record. It does not claim that this record
is the full HOL `asm_config`, or that the callbacks are related to the HOL
definitions. That configuration bridge remains open.
-/

namespace Flapjack.Compiler.Backend.StackProps

open StackLang
open Flapjack.Compiler.Encoders.Asm

/-- The projections consumed by the HOL `stack_asm_ok` clauses. -/
structure AsmChecks (Inst Memop Addr : Type) where
  regCount : Nat
  avoidRegs : List Nat
  instOk : Inst → Bool
  regOk : Nat → Bool
  addrOk : Memop → Addr → Bool

/-- Recursive clauses of HOL `stackProps$stack_asm_ok_def`.

`inl` call targets are labels and are unrestricted; `inr` targets are
registers checked against `reg_count` and `avoid_regs`. A handler without a
return continuation is ignored, matching the source clause. -/
def stackAsmOk {Inst Cmp RegImm Binop Memop Addr MlString : Type}
    (checks : AsmChecks Inst Memop Addr) :
    StackLang.Prog Inst Cmp RegImm Binop Memop Addr MlString → Bool
  | .inst instruction => checks.instOk instruction
  | .shMemOp operator register address =>
      checks.regOk register && checks.addrOk operator address
  | .codeBufferWrite left right =>
      left < checks.regCount && right < checks.regCount &&
        !checks.avoidRegs.contains left && !checks.avoidRegs.contains right
  | .seq first second => stackAsmOk checks first && stackAsmOk checks second
  | .ite _ _ _ thenBranch elseBranch =>
      stackAsmOk checks thenBranch && stackAsmOk checks elseBranch
  | .loop body => stackAsmOk checks body
  | .raise register | .ret register =>
      register < checks.regCount && !checks.avoidRegs.contains register
  | .call returnHandler target handler =>
      let targetOk := match target with
        | .inl _ => true
        | .inr register =>
            register < checks.regCount && !checks.avoidRegs.contains register
      let continuationsOk := match returnHandler with
        | none => true
        | some (program, _, _, _) =>
            stackAsmOk checks program &&
              match handler with
              | none => true
              | some (handlerProgram, _, _) => stackAsmOk checks handlerProgram
      targetOk && continuationsOk
  | _ => true
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-- HOL `stackProps$addr_ok_def` (`stackPropsScript.sml:801-810`), over the
faithful `asm` address carrier.  `Load`/`Store`/`Load32`/`Store32` use the
word address offset; `Load16`/`Store16` use the halfword offset and are
unavailable on `Ag32`; every other memory operation uses the byte offset.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def asmAddrOk {width : Nat} (config : AsmConfig width) :
    WordMemOp → WordLangAddr (BitVec width) → Bool
  | operator, .addr base offset =>
      asmRegOk config base &&
        (if operator == .load || operator == .store || operator == .load32 ||
            operator == .store32 then
          asmAddrOffsetOk config offset
         else if operator == .load16 || operator == .store16 then
          asmHwOffsetOk config offset && !(config.isa == .ag32)
         else
          asmByteOffsetOk config offset)

/-- The HOL `stack_asm_ok` callback record instantiated with the real
`asm_config` validity predicates instead of opaque callbacks. -/
def asmChecksOfConfig {width : Nat} (config : AsmConfig width) :
    AsmChecks (WordLangInst (BitVec width)) WordMemOp (WordLangAddr (BitVec width)) :=
  { regCount := config.regCount
    avoidRegs := config.avoidRegs
    instOk := asmInstOk config
    regOk := asmRegOk config
    addrOk := asmAddrOk config }


end Flapjack.Compiler.Backend.StackProps
