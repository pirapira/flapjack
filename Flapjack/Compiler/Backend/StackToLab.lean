import Flapjack.Compiler.Backend.LabLang
import Flapjack.Compiler.Backend.StackAlloc
import Flapjack.Compiler.Backend.StackLang

/-!
# Cake stack_to_lab flatten

This ports the local `flatten` quotation in
`cakeml/compiler/backend/stack_to_labScript.sml`. The HOL source uses several
imported carrier constructors (for example, `Skip`, `JumpReg`, and `Reg`) whose
Lean carrier types are kept explicit here through `FlattenOps`. Supplying those
constructors does not assert an adapter to Flapjack's executable assembler.
-/

namespace Flapjack.Compiler.Backend.StackToLab

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackLang

/-- Imported assembler constructors used by the HOL `flatten` quotation. -/
structure FlattenOps (Inst Cmp RegImm AsmInst : Type) where
  skip : AsmInst
  embedInst : Inst → AsmInst
  jumpReg : Nat → AsmInst
  reg : Nat → RegImm
  lower : Cmp
  negate : Cmp → Cmp

abbrev FlatLine (Memop Addr Cmp RegImm MlString AsmInst Word : Type) :=
  Line (AsmOrCbw AsmInst Memop Addr) (AsmWithLab Cmp RegImm MlString) Word

private def findLab (index : Nat) (labs : List Nat) : Nat :=
  (labs[index]?).getD 0

private def isSkip {Inst Cmp RegImm Binop Memop Addr MlString : Type} :
    Prog Inst Cmp RegImm Binop Memop Addr MlString → Bool
  | .skip => true
  | _ => false

private def compileJump (ops : FlattenOps Inst Cmp RegImm AsmInst)
    (zero : Word) (target : Sum Nat Nat) : FlatLine Memop Addr Cmp RegImm MlString AsmInst Word :=
  match target with
  | .inl sectionId => .labAsm (.jump (.lab sectionId 0)) zero [] 0
  | .inr register => .asm (.asmi (ops.jumpReg register)) [] 0

/-- HOL `stack_to_lab$flatten`, preserving label allocation and result flag. -/
def flatten {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
    (ops : FlattenOps Inst Cmp RegImm AsmInst) (zero : Word) :
    Bool → Prog Inst Cmp RegImm Binop Memop Addr MlString → Nat → Nat →
      List Nat → List Nat →
      List (FlatLine Memop Addr Cmp RegImm MlString AsmInst Word) × Bool × Nat
  | tail, program, sectionId, next, conts, breaks =>
    match program with
    | .tick => ([.asm (.asmi ops.skip) [] 0], false, next)
    | .inst instruction => ([.asm (.asmi (ops.embedInst instruction)) [] 0], false, next)
    | .halt _ => ([.labAsm .halt zero [] 0], true, next)
    | .seq first second =>
        let (xs, nr1, next) := flatten ops zero false first sectionId next conts breaks
        let (ys, nr2, next) := flatten ops zero false second sectionId next conts breaks
        ((if tail then xs ++ [.label sectionId 1 0] ++ ys else xs ++ ys), nr1 || nr2, next)
    | .ite condition register right thenBranch elseBranch =>
        let (xs, nr1, next) := flatten ops zero false thenBranch sectionId next conts breaks
        let (ys, nr2, next) := flatten ops zero false elseBranch sectionId next conts breaks
        if isSkip thenBranch && isSkip elseBranch then
          ([], false, next)
        else if isSkip thenBranch then
          ([.labAsm (.jumpCmp condition register right (.lab sectionId next)) zero [] 0] ++
            ys ++ [.label sectionId next 0], false, next + 1)
        else if isSkip elseBranch then
          ([.labAsm (.jumpCmp (ops.negate condition) register right (.lab sectionId next)) zero [] 0] ++
            xs ++ [.label sectionId next 0], false, next + 1)
        else if nr1 then
          ([.labAsm (.jumpCmp (ops.negate condition) register right (.lab sectionId next)) zero [] 0] ++
            xs ++ [.label sectionId next 0] ++ ys, nr2, next + 1)
        else if nr2 then
          ([.labAsm (.jumpCmp condition register right (.lab sectionId next)) zero [] 0] ++
            ys ++ [.label sectionId next 0] ++ xs, nr1, next + 1)
        else
          ([.labAsm (.jumpCmp condition register right (.lab sectionId next)) zero [] 0] ++
            ys ++ [.labAsm (.jump (.lab sectionId (next + 1))) zero [] 0,
              .label sectionId next 0] ++ xs ++ [.label sectionId (next + 1) 0],
            nr1 && nr2, next + 2)
    | .loop body =>
        let continueLabel := next
        let breakLabel := next + 1
        let (xs, _, nextAfterBody) := flatten ops zero false body sectionId (next + 2)
          (continueLabel :: conts) (breakLabel :: breaks)
        ([.label sectionId continueLabel 0] ++ xs ++
          [.labAsm (.jump (.lab sectionId continueLabel)) zero [] 0,
            .label sectionId breakLabel 0], false, nextAfterBody)
    | .raise register => ([.asm (.asmi (ops.jumpReg register)) [] 0], true, next)
    | .ret register => ([.asm (.asmi (ops.jumpReg register)) [] 0], true, next)
    | .break index =>
        ([.labAsm (.jump (.lab sectionId (findLab index breaks))) zero [] 0], true, next)
    | .continue index =>
        ([.labAsm (.jump (.lab sectionId (findLab index conts))) zero [] 0], true, next)
    | .rawCall target => ([.labAsm (.jump (.lab target 1)) zero [] 0], true, next)
    | .call none target _ => ([compileJump ops zero target], true, next)
    | .call (some (returnProgram, linkRegister, returnSection, returnLabel)) target handler =>
        let (xs, nr1, next) := flatten ops zero false returnProgram sectionId next conts breaks
        let prelude := [.labAsm (.locValue linkRegister (.lab returnSection returnLabel)) zero [] 0,
          compileJump ops zero target, .label returnSection returnLabel 0] ++ xs
        match handler with
        | none => (prelude, nr1, next)
        | some (handlerProgram, handlerSection, handlerLabel) =>
            let (ys, nr2, next) := flatten ops zero false handlerProgram sectionId next conts breaks
            (prelude ++ [.labAsm (.jump (.lab sectionId next)) zero [] 0,
              .label handlerSection handlerLabel 0] ++ ys ++ [.label sectionId next 0],
              nr1 && nr2, next + 1)
    | .jumpLower left right target =>
        ([.labAsm (.jumpCmp ops.lower left (ops.reg right) (.lab target 0)) zero [] 0], false, next)
    | .ffi function _ _ _ _ returnAddress =>
        ([.labAsm (.locValue returnAddress (.lab sectionId next)) zero [] 0,
          .labAsm (.callFFI function) zero [] 0, .label sectionId next 0], false, next + 1)
    | .locValue register label entry =>
        ([.labAsm (.locValue register (.lab label entry)) zero [] 0], false, next)
    | .install _ _ _ _ returnAddress =>
        ([.labAsm (.locValue returnAddress (.lab sectionId next)) zero [] 0,
          .labAsm .install zero [] 0, .label sectionId next 0], false, next + 1)
    | .shMemOp operator register address =>
        ([.asm (.shareMem operator register address) [] 0], false, next)
    | .codeBufferWrite left right => ([.asm (.cbw left right) [] 0], false, next)
    | _ => ([], false, next)
termination_by _tail program _section _next _conts _breaks => sizeOf program
decreasing_by all_goals decreasing_trivial


/-! Base cases of `flatten`: the non-recursive constructors emit exactly their
HOL source lines. These are the leaf cases used by the `flatten_line_ok_pre`
induction. -/
section FlattenBase

variable {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
variable (ops : FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)

theorem flatten_tick (tail : Bool) (sectionId next : Nat) (conts breaks : List Nat) :
    flatten ops zero tail (.tick : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.asm (.asmi ops.skip) [] 0], false, next) := by
  rw [flatten]

theorem flatten_inst (tail : Bool) (instruction : Inst) (sectionId next : Nat)
    (conts breaks : List Nat) :
    flatten ops zero tail (.inst instruction : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.asm (.asmi (ops.embedInst instruction)) [] 0], false, next) := by
  rw [flatten]

theorem flatten_halt (tail : Bool) (label sectionId next : Nat) (conts breaks : List Nat) :
    flatten ops zero tail (.halt label : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.labAsm .halt zero [] 0], true, next) := by
  rw [flatten]

theorem flatten_raise (tail : Bool) (register sectionId next : Nat) (conts breaks : List Nat) :
    flatten ops zero tail (.raise register : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.asm (.asmi (ops.jumpReg register)) [] 0], true, next) := by
  rw [flatten]

theorem flatten_ret (tail : Bool) (register sectionId next : Nat) (conts breaks : List Nat) :
    flatten ops zero tail (.ret register : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.asm (.asmi (ops.jumpReg register)) [] 0], true, next) := by
  rw [flatten]

theorem flatten_rawCall (tail : Bool) (target sectionId next : Nat) (conts breaks : List Nat) :
    flatten ops zero tail (.rawCall target : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.labAsm (.jump (.lab target 1)) zero [] 0], true, next) := by
  rw [flatten]

theorem flatten_locValue (tail : Bool) (register label entry sectionId next : Nat)
    (conts breaks : List Nat) :
    flatten ops zero tail (.locValue register label entry : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.labAsm (.locValue register (.lab label entry)) zero [] 0], false, next) := by
  rw [flatten]

theorem flatten_shMemOp (tail : Bool) (operator : Memop) (register : Nat) (address : Addr)
    (sectionId next : Nat) (conts breaks : List Nat) :
    flatten ops zero tail (.shMemOp operator register address : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.asm (.shareMem operator register address) [] 0], false, next) := by
  rw [flatten]

theorem flatten_codeBufferWrite (tail : Bool) (left right sectionId next : Nat)
    (conts breaks : List Nat) :
    flatten ops zero tail (.codeBufferWrite left right : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.asm (.cbw left right) [] 0], false, next) := by
  rw [flatten]

theorem flatten_break (tail : Bool) (index sectionId next : Nat) (conts breaks : List Nat) :
    flatten ops zero tail (.break index : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.labAsm (.jump (.lab sectionId (findLab index breaks))) zero [] 0], true, next) := by
  rw [flatten]

theorem flatten_continue (tail : Bool) (index sectionId next : Nat) (conts breaks : List Nat) :
    flatten ops zero tail (.continue index : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks =
      ([.labAsm (.jump (.lab sectionId (findLab index conts))) zero [] 0], true, next) := by
  rw [flatten]

end FlattenBase

private def isSeq {Inst Cmp RegImm Binop Memop Addr MlString : Type} :
    Prog Inst Cmp RegImm Binop Memop Addr MlString → Bool
  | .seq _ _ => true
  | _ => false

/-- HOL `stack_to_lab$prog_to_section`, using `next_lab` and the flattened
lines. The outer label is `m` only when the source program itself is `Seq`;
all other roots receive label `1`. -/
def progToSection {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
    (ops : FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)
    (sectionId : Nat) (program : Prog Inst Cmp RegImm Binop Memop Addr MlString) :
    Section (FlatLine Memop Addr Cmp RegImm MlString AsmInst Word) :=
  let (lines, _, next) :=
    flatten ops zero true program sectionId
      (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] []
  { sectionId := sectionId
    lines := lines ++ [.label sectionId (if isSeq program then next else 1) 0] }

end Flapjack.Compiler.Backend.StackToLab
