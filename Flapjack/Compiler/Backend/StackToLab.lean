import Flapjack.Compiler.Backend.LabLang
import Flapjack.Compiler.Backend.StackAlloc
import Flapjack.Compiler.Backend.StackLang
import Flapjack.Misc.AppList

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

def stackIsSkip {Inst Cmp RegImm Binop Memop Addr MlString : Type} :
    Prog Inst Cmp RegImm Binop Memop Addr MlString → Bool
  | .skip => true
  | _ => false

def compileJump (ops : FlattenOps Inst Cmp RegImm AsmInst)
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
        if stackIsSkip thenBranch && stackIsSkip elseBranch then
          ([], false, next)
        else if stackIsSkip thenBranch then
          ([.labAsm (.jumpCmp condition register right (.lab sectionId next)) zero [] 0] ++
            ys ++ [.label sectionId next 0], false, next + 1)
        else if stackIsSkip elseBranch then
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


/-- HOL `stack_to_lab$flatten`, with the HOL `misc$app_list` codomain.

The HOL source builds its output as an `app_list` concatenation tree (`List`,
`Append`, `Nil`) and flattens it with `misc$append`. This is the identical
function with that codomain, so the exact HOL hypothesis `flatten t p n m cs bs
= (ls, a, b)` can be stated. `flatten` is the flat production form. -/
def flattenApp {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
    (ops : FlattenOps Inst Cmp RegImm AsmInst) (zero : Word) :
    Bool → Prog Inst Cmp RegImm Binop Memop Addr MlString → Nat → Nat →
      List Nat → List Nat →
      AppList (FlatLine Memop Addr Cmp RegImm MlString AsmInst Word) × Bool × Nat
  | tail, program, sectionId, next, conts, breaks =>
    match program with
    | .tick => (.list [.asm (.asmi ops.skip) [] 0], false, next)
    | .inst instruction => (.list [.asm (.asmi (ops.embedInst instruction)) [] 0], false, next)
    | .halt _ => (.list [.labAsm .halt zero [] 0], true, next)
    | .seq first second =>
        let (xs, nr1, next) := flattenApp ops zero false first sectionId next conts breaks
        let (ys, nr2, next) := flattenApp ops zero false second sectionId next conts breaks
        ((if tail then .append xs (.append (.list [.label sectionId 1 0]) ys) else .append xs ys),
          nr1 || nr2, next)
    | .ite condition register right thenBranch elseBranch =>
        let (xs, nr1, next) := flattenApp ops zero false thenBranch sectionId next conts breaks
        let (ys, nr2, next) := flattenApp ops zero false elseBranch sectionId next conts breaks
        if stackIsSkip thenBranch && stackIsSkip elseBranch then
          (.list [], false, next)
        else if stackIsSkip thenBranch then
          (.append (.list [.labAsm (.jumpCmp condition register right (.lab sectionId next)) zero [] 0])
            (.append ys (.list [.label sectionId next 0])), false, next + 1)
        else if stackIsSkip elseBranch then
          (.append (.list [.labAsm (.jumpCmp (ops.negate condition) register right (.lab sectionId next)) zero [] 0])
            (.append xs (.list [.label sectionId next 0])), false, next + 1)
        else if nr1 then
          (.append (.list [.labAsm (.jumpCmp (ops.negate condition) register right (.lab sectionId next)) zero [] 0])
            (.append xs (.append (.list [.label sectionId next 0]) ys)), nr2, next + 1)
        else if nr2 then
          (.append (.list [.labAsm (.jumpCmp condition register right (.lab sectionId next)) zero [] 0])
            (.append ys (.append (.list [.label sectionId next 0]) xs)), nr1, next + 1)
        else
          (.append (.list [.labAsm (.jumpCmp condition register right (.lab sectionId next)) zero [] 0])
            (.append ys (.append (.list [.labAsm (.jump (.lab sectionId (next + 1))) zero [] 0,
                .label sectionId next 0])
              (.append xs (.list [.label sectionId (next + 1) 0])))), nr1 && nr2, next + 2)
    | .loop body =>
        let continueLabel := next
        let breakLabel := next + 1
        let (xs, _, nextAfterBody) := flattenApp ops zero false body sectionId (next + 2)
          (continueLabel :: conts) (breakLabel :: breaks)
        (.append (.list [.label sectionId continueLabel 0])
          (.append xs
            (.list [.labAsm (.jump (.lab sectionId continueLabel)) zero [] 0,
              .label sectionId breakLabel 0])), false, nextAfterBody)
    | .raise register => (.list [.asm (.asmi (ops.jumpReg register)) [] 0], true, next)
    | .ret register => (.list [.asm (.asmi (ops.jumpReg register)) [] 0], true, next)
    | .break index =>
        (.list [.labAsm (.jump (.lab sectionId (findLab index breaks))) zero [] 0], true, next)
    | .continue index =>
        (.list [.labAsm (.jump (.lab sectionId (findLab index conts))) zero [] 0], true, next)
    | .rawCall target => (.list [.labAsm (.jump (.lab target 1)) zero [] 0], true, next)
    | .call none target _ => (.list [compileJump ops zero target], true, next)
    | .call (some (returnProgram, linkRegister, returnSection, returnLabel)) target handler =>
        let (xs, nr1, next) := flattenApp ops zero false returnProgram sectionId next conts breaks
        let prelude := .append
          (.list [.labAsm (.locValue linkRegister (.lab returnSection returnLabel)) zero [] 0,
            compileJump ops zero target, .label returnSection returnLabel 0]) xs
        match handler with
        | none => (prelude, nr1, next)
        | some (handlerProgram, handlerSection, handlerLabel) =>
            let (ys, nr2, next) := flattenApp ops zero false handlerProgram sectionId next conts breaks
            (.append prelude
              (.append (.list [.labAsm (.jump (.lab sectionId next)) zero [] 0,
                  .label handlerSection handlerLabel 0])
                (.append ys (.list [.label sectionId next 0]))), nr1 && nr2, next + 1)
    | .jumpLower left right target =>
        (.list [.labAsm (.jumpCmp ops.lower left (ops.reg right) (.lab target 0)) zero [] 0], false, next)
    | .ffi function _ _ _ _ returnAddress =>
        (.list [.labAsm (.locValue returnAddress (.lab sectionId next)) zero [] 0,
          .labAsm (.callFFI function) zero [] 0, .label sectionId next 0], false, next + 1)
    | .locValue register label entry =>
        (.list [.labAsm (.locValue register (.lab label entry)) zero [] 0], false, next)
    | .install _ _ _ _ returnAddress =>
        (.list [.labAsm (.locValue returnAddress (.lab sectionId next)) zero [] 0,
          .labAsm .install zero [] 0, .label sectionId next 0], false, next + 1)
    | .shMemOp operator register address =>
        (.list [.asm (.shareMem operator register address) [] 0], false, next)
    | .codeBufferWrite left right => (.list [.asm (.cbw left right) [] 0], false, next)
    | _ => (.list [], false, next)
termination_by _tail program _section _next _conts _breaks => sizeOf program
decreasing_by all_goals decreasing_trivial


/-! The representation bridge: flattening the HOL `app_list` output of
`flattenApp` with `misc$append`/`appListAppend` gives the flat production
output of `flatten`. Non-recursive constructors are proved pointwise here; the
recursive composition cases are built on these. -/
section FlattenAppBridge

variable {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
variable (ops : FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)

theorem flattenApp_tick (tail : Bool) (sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail (.tick : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail (.tick : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_inst (tail : Bool) (instruction : Inst) (sectionId next : Nat)
    (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.inst instruction : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.inst instruction : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_halt (tail : Bool) (register sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.halt register : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.halt register : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_raise (tail : Bool) (exception sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.raise exception : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.raise exception : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_ret (tail : Bool) (value sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.ret value : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.ret value : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_break (tail : Bool) (label sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.break label : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.break label : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_continue (tail : Bool) (label sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.continue label : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.continue label : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_rawCall (tail : Bool) (target sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.rawCall target : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.rawCall target : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_call_none (tail : Bool) (target : Sum Nat Nat)
    (handler : Option (Prog Inst Cmp RegImm Binop Memop Addr MlString × Nat × Nat))
    (sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.call none target handler : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.call none target handler : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_jumpLower (tail : Bool) (left right target sectionId next : Nat)
    (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.jumpLower left right target : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.jumpLower left right target : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_ffi (tail : Bool) (function : MlString)
    (configuration configurationLength array arrayLength returnAddress sectionId next : Nat)
    (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.ffi function configuration configurationLength array arrayLength returnAddress :
          Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.ffi function configuration configurationLength array arrayLength returnAddress :
          Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_locValue (tail : Bool) (destination label entry sectionId next : Nat)
    (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.locValue destination label entry : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.locValue destination label entry : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_install (tail : Bool)
    (codeBuffer codeLength dataBuffer dataLength returnAddress sectionId next : Nat)
    (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.install codeBuffer codeLength dataBuffer dataLength returnAddress :
          Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.install codeBuffer codeLength dataBuffer dataLength returnAddress :
          Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_shMemOp (tail : Bool) (operator : Memop) (register : Nat) (address : Addr)
    (sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.shMemOp operator register address : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.shMemOp operator register address : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_codeBufferWrite (tail : Bool) (address value sectionId next : Nat)
    (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.codeBufferWrite address value : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.codeBufferWrite address value : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

/-- Representative of the `_ => List []` catch-all constructors (e.g. `skip`,
`get`, `set`, `alloc`, the `stack*` family). -/
theorem flattenApp_skip (tail : Bool) (sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail
        (.skip : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks) =
      flatten ops zero tail
        (.skip : Prog Inst Cmp RegImm Binop Memop Addr MlString)
        sectionId next conts breaks := by
  simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux]

theorem flattenApp_seq (tail : Bool) (first second : Prog Inst Cmp RegImm Binop Memop Addr MlString)
    (sectionId next : Nat) (conts breaks : List Nat)
    (ihFirst : ∀ n, appListFlatten (flattenApp ops zero false first sectionId n conts breaks)
      = flatten ops zero false first sectionId n conts breaks)
    (ihSecond : ∀ n, appListFlatten (flattenApp ops zero false second sectionId n conts breaks)
      = flatten ops zero false second sectionId n conts breaks) :
    appListFlatten (flattenApp ops zero tail (.seq first second) sectionId next conts breaks)
      = flatten ops zero tail (.seq first second) sectionId next conts breaks := by
  simp only [flattenApp, flatten]
  cases hA : flattenApp ops zero false first sectionId next conts breaks with
  | mk xs rA =>
    cases rA with
    | mk nr1 nx =>
      cases hB : flattenApp ops zero false second sectionId nx conts breaks with
      | mk ys rB =>
        cases rB with
        | mk nr2 ny =>
          cases hF : flatten ops zero false first sectionId next conts breaks with
          | mk xsf rF =>
            cases rF with
            | mk nrf nxf =>
              cases hG : flatten ops zero false second sectionId nxf conts breaks with
              | mk ysf rG =>
                cases rG with
                | mk nrg nyf =>
                  have h1 := ihFirst next
                  rw [hA, hF] at h1
                  simp only [appListFlatten] at h1
                  have hxs : appListAppend xs = xsf := congrArg Prod.fst h1
                  have hnr1 : nr1 = nrf := congrArg (fun p => p.2.1) h1
                  have hnx : nx = nxf := congrArg (fun p => p.2.2) h1
                  have h2 := ihSecond nx
                  rw [← hnx] at hG
                  rw [hB, hG] at h2
                  simp only [appListFlatten] at h2
                  have hys : appListAppend ys = ysf := congrArg Prod.fst h2
                  have hnr2 : nr2 = nrg := congrArg (fun p => p.2.1) h2
                  have hny : ny = nyf := congrArg (fun p => p.2.2) h2
                  rw [hnr1, hnr2, hny]
                  by_cases ht : tail = true
                  · simp only [if_pos ht, appListFlatten, appListAppend, appendAux]
                    congr 1
                    rw [appendAux_thm]
                    simp only [appListAppend] at hxs hys ⊢
                    rw [hxs, hys, List.append_assoc]
                  · simp only [if_neg ht, appListFlatten, appListAppend, appendAux]
                    congr 1
                    rw [appendAux_thm]
                    simp only [appListAppend] at hxs hys ⊢
                    rw [hxs, hys]

theorem flattenApp_loop (tail : Bool) (body : Prog Inst Cmp RegImm Binop Memop Addr MlString)
    (sectionId next : Nat) (conts breaks : List Nat)
    (ihBody : ∀ (n : Nat) (c b : List Nat),
      appListFlatten (flattenApp ops zero false body sectionId n c b)
        = flatten ops zero false body sectionId n c b) :
    appListFlatten (flattenApp ops zero tail (.loop body) sectionId next conts breaks)
      = flatten ops zero tail (.loop body) sectionId next conts breaks := by
  simp only [flattenApp, flatten]
  cases hA : flattenApp ops zero false body sectionId (next + 2) (next :: conts) ((next + 1) :: breaks) with
  | mk xs rA =>
    cases rA with
    | mk nr1 nx =>
      cases hF : flatten ops zero false body sectionId (next + 2) (next :: conts) ((next + 1) :: breaks) with
      | mk xsf rF =>
        cases rF with
        | mk nrf nxf =>
          have h1 := ihBody (next + 2) (next :: conts) ((next + 1) :: breaks)
          rw [hA, hF] at h1
          simp only [appListFlatten] at h1
          injection h1 with hxs hrest
          injection hrest with _hnr hnx
          simp only [appListFlatten, appListAppend, appendAux]
          rw [appendAux_thm]
          simp only [appListAppend] at hxs
          rw [hxs, hnx, List.append_nil, List.append_assoc]

theorem flattenApp_call_some (tail : Bool)
    (returnProgram : Prog Inst Cmp RegImm Binop Memop Addr MlString)
    (linkRegister returnSection returnLabel : Nat) (target : Sum Nat Nat)
    (handler : Option (Prog Inst Cmp RegImm Binop Memop Addr MlString × Nat × Nat))
    (sectionId next : Nat) (conts breaks : List Nat)
    (ihReturn : ∀ (n : Nat),
      appListFlatten (flattenApp ops zero false returnProgram sectionId n conts breaks)
        = flatten ops zero false returnProgram sectionId n conts breaks)
    (ihHandler : ∀ (hp : Prog Inst Cmp RegImm Binop Memop Addr MlString) (_hs _hl n : Nat),
      sizeOf hp < sizeOf (.call (some (returnProgram, linkRegister, returnSection, returnLabel))
        target handler : Prog Inst Cmp RegImm Binop Memop Addr MlString) →
      appListFlatten (flattenApp ops zero false hp sectionId n conts breaks)
        = flatten ops zero false hp sectionId n conts breaks) :
    appListFlatten (flattenApp ops zero tail
        (.call (some (returnProgram, linkRegister, returnSection, returnLabel)) target handler)
        sectionId next conts breaks)
      = flatten ops zero tail
        (.call (some (returnProgram, linkRegister, returnSection, returnLabel)) target handler)
        sectionId next conts breaks := by
  simp only [flattenApp, flatten]
  cases hA : flattenApp ops zero false returnProgram sectionId next conts breaks with
  | mk xs rA =>
    cases rA with
    | mk nr1 nx =>
      cases hF : flatten ops zero false returnProgram sectionId next conts breaks with
      | mk xsf rF =>
        cases rF with
        | mk nrf nxf =>
          have h1 := ihReturn next
          rw [hA, hF] at h1
          simp only [appListFlatten] at h1
          injection h1 with hxs hrest
          injection hrest with hnr1 hnx
          rw [hnx]
          cases handler with
          | none =>
            simp only [appListFlatten, appListAppend, appendAux]
            simp only [appListAppend] at hxs
            rw [hxs, hnr1]
          | some triple =>
            obtain ⟨handlerProgram, handlerSection, handlerLabel⟩ := triple
            simp only []
            cases hB : flattenApp ops zero false handlerProgram sectionId nxf conts breaks with
            | mk ys rB =>
              cases rB with
              | mk nr2 ny =>
                cases hG : flatten ops zero false handlerProgram sectionId nxf conts breaks with
                | mk ysf rG =>
                  cases rG with
                  | mk nrg nyf =>
                    have h2 := ihHandler handlerProgram handlerSection handlerLabel nxf (by decreasing_trivial)
                    rw [hB, hG] at h2
                    simp only [appListFlatten] at h2
                    injection h2 with hys hrest2
                    injection hrest2 with hnr2 hny
                    simp only []
                    simp only [appListFlatten, appListAppend, appendAux]
                    rw [appendAux_thm]
                    simp only [appListAppend] at hxs hys
                    rw [hxs]
                    rw [appendAux_thm]
                    rw [hys, hnr1, hnr2, hny]
                    simp only [List.append_nil, List.append_assoc]

theorem flattenApp_ite (tail : Bool) (condition : Cmp) (register : Nat) (right : RegImm)
    (thenBranch elseBranch : Prog Inst Cmp RegImm Binop Memop Addr MlString)
    (sectionId next : Nat) (conts breaks : List Nat)
    (ihThen : ∀ (n : Nat),
      appListFlatten (flattenApp ops zero false thenBranch sectionId n conts breaks)
        = flatten ops zero false thenBranch sectionId n conts breaks)
    (ihElse : ∀ (n : Nat),
      appListFlatten (flattenApp ops zero false elseBranch sectionId n conts breaks)
        = flatten ops zero false elseBranch sectionId n conts breaks) :
    appListFlatten (flattenApp ops zero tail (.ite condition register right thenBranch elseBranch)
        sectionId next conts breaks)
      = flatten ops zero tail (.ite condition register right thenBranch elseBranch)
        sectionId next conts breaks := by
  simp only [flattenApp, flatten]
  cases hA : flattenApp ops zero false thenBranch sectionId next conts breaks with
  | mk xs rA =>
    cases rA with
    | mk nr1 nx =>
      cases hB : flattenApp ops zero false elseBranch sectionId nx conts breaks with
      | mk ys rB =>
        cases rB with
        | mk nr2 ny =>
          cases hF : flatten ops zero false thenBranch sectionId next conts breaks with
          | mk xsf rF =>
            cases rF with
            | mk nrf nxf =>
              cases hG : flatten ops zero false elseBranch sectionId nxf conts breaks with
              | mk ysf rG =>
                cases rG with
                | mk nrg nyf =>
                  have h1 := ihThen next
                  rw [hA, hF] at h1
                  simp only [appListFlatten] at h1
                  have hxs : appListAppend xs = xsf := congrArg Prod.fst h1
                  have hnr1 : nr1 = nrf := congrArg (fun p => p.2.1) h1
                  have hnx : nx = nxf := congrArg (fun p => p.2.2) h1
                  have h2 := ihElse nx
                  rw [← hnx] at hG
                  rw [hB, hG] at h2
                  simp only [appListFlatten] at h2
                  have hys : appListAppend ys = ysf := congrArg Prod.fst h2
                  have hnr2 : nr2 = nrg := congrArg (fun p => p.2.1) h2
                  have hny : ny = nyf := congrArg (fun p => p.2.2) h2
                  rw [hnx, hnr1, hnr2, hny]
                  by_cases hc1 : (stackIsSkip thenBranch && stackIsSkip elseBranch) = true
                  · simp only [if_pos hc1, appListFlatten, appListAppend, appendAux, List.nil_append]
                  · by_cases hc2 : stackIsSkip thenBranch = true
                    · simp only [if_neg hc1, if_pos hc2, appListFlatten, appListAppend, appendAux]
                      simp only [appListAppend] at hys
                      rw [appendAux_thm]
                      rw [hys]
                      simp only [List.append_assoc, List.append_nil]
                    · by_cases hc3 : stackIsSkip elseBranch = true
                      · simp only [if_neg hc1, if_neg hc2, if_pos hc3, appListFlatten,
                          appListAppend, appendAux]
                        simp only [appListAppend] at hxs
                        rw [appendAux_thm]
                        rw [hxs]
                        simp only [List.append_assoc, List.append_nil]
                      · by_cases hc4 : nrf = true
                        · simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_pos hc4,
                            appListFlatten, appListAppend, appendAux]
                          simp only [appListAppend] at hxs hys
                          rw [appendAux_thm]
                          rw [hxs]
                          rw [appendAux_thm]
                          rw [hys]
                          simp only [List.append_assoc, List.append_nil]
                        · by_cases hc5 : nrg = true
                          · simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_pos hc5,
                              appListFlatten, appListAppend, appendAux]
                            simp only [appListAppend] at hxs hys
                            rw [appendAux_thm]
                            rw [hys]
                            rw [appendAux_thm]
                            rw [hxs]
                            simp only [List.append_assoc, List.append_nil]
                          · simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5,
                              appListFlatten, appListAppend, appendAux]
                            simp only [appListAppend] at hxs hys
                            rw [appendAux_thm]
                            rw [hys]
                            rw [appendAux_thm]
                            rw [hxs]
                            simp only [List.append_assoc, List.append_nil]
/-- Untagged Flapjack representation bridge (not a HOL port): the `appListFlatten`
of the `app_list` `flattenApp` output equals the flat production `flatten` output.
HOL has a single global `flatten` over the imported assembler constructors,
whereas `flattenApp` is parameterised by `ops : FlattenOps ...`; no `@[hol]` tag
is attached.

The recursion is over `sizeOf program` and the result is a `Prop` equality, so a
recursive `def` would trip `linter.defProp`. It is stated as a theorem with
well-founded recursion (`Nat.strongRecOn`), avoiding any linter suppression. -/
theorem flattenAppBridgeAux
    (tail : Bool) (program : Prog Inst Cmp RegImm Binop Memop Addr MlString)
    (sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail program sectionId next conts breaks)
      = flatten ops zero tail program sectionId next conts breaks :=
  Nat.strongRecOn (sizeOf program)
    (motive := fun k => ∀ (program : Prog Inst Cmp RegImm Binop Memop Addr MlString),
      sizeOf program ≤ k → ∀ (tail : Bool) (sectionId next : Nat) (conts breaks : List Nat),
        appListFlatten (flattenApp ops zero tail program sectionId next conts breaks)
          = flatten ops zero tail program sectionId next conts breaks)
    (fun _ ih => by
      intro program hle tail sectionId next conts breaks
      cases program with
      | seq first second =>
        exact flattenApp_seq ops zero tail first second sectionId next conts breaks
          (fun k => ih (sizeOf first)
            (by have h : sizeOf first < sizeOf (Prog.seq first second) := (by decreasing_trivial); omega)
            first (Nat.le_refl _) false sectionId k conts breaks)
          (fun k => ih (sizeOf second)
            (by have h : sizeOf second < sizeOf (Prog.seq first second) := (by decreasing_trivial); omega)
            second (Nat.le_refl _) false sectionId k conts breaks)
      | ite condition register right thenBranch elseBranch =>
        exact flattenApp_ite ops zero tail condition register right thenBranch elseBranch
          sectionId next conts breaks
          (fun k => ih (sizeOf thenBranch)
            (by have h : sizeOf thenBranch < sizeOf (Prog.ite condition register right thenBranch elseBranch) := (by decreasing_trivial); omega)
            thenBranch (Nat.le_refl _) false sectionId k conts breaks)
          (fun k => ih (sizeOf elseBranch)
            (by have h : sizeOf elseBranch < sizeOf (Prog.ite condition register right thenBranch elseBranch) := (by decreasing_trivial); omega)
            elseBranch (Nat.le_refl _) false sectionId k conts breaks)
      | loop body =>
        exact flattenApp_loop ops zero tail body sectionId next conts breaks
          (fun k c b => ih (sizeOf body)
            (by have h : sizeOf body < sizeOf (Prog.loop body) := (by decreasing_trivial); omega)
            body (Nat.le_refl _) false sectionId k c b)
      | call returnHandler target handler =>
        cases returnHandler with
        | none =>
          exact flattenApp_call_none ops zero tail target handler sectionId next conts breaks
        | some triple =>
          obtain ⟨returnProgram, linkRegister, returnSection, returnLabel⟩ := triple
          exact flattenApp_call_some ops zero tail returnProgram linkRegister returnSection returnLabel
            target handler sectionId next conts breaks
            (fun k => ih (sizeOf returnProgram)
              (by have h : sizeOf returnProgram < sizeOf (Prog.call (some (returnProgram, linkRegister, returnSection, returnLabel)) target handler) := (by decreasing_trivial); omega)
              returnProgram (Nat.le_refl _) false sectionId k conts breaks)
            (fun hp _hs _hl k _hbound => ih (sizeOf hp)
              (by have h : sizeOf hp < sizeOf (Prog.call (some (returnProgram, linkRegister, returnSection, returnLabel)) target handler) := (by decreasing_trivial); omega)
              hp (Nat.le_refl _) false sectionId k conts breaks)
      | tick | skip | inst _ | get _ _ | «set» _ _ | opCurrHeap _ _ _ | jumpLower _ _ _
        | alloc _ | storeConsts _ _ _ | raise _ | ret _ | «break» _ | «continue» _
        | ffi _ _ _ _ _ _ | locValue _ _ _ | install _ _ _ _ _ | shMemOp _ _ _
        | codeBufferWrite _ _ | dataBufferWrite _ _ | rawCall _ | stackAlloc _ | stackFree _
        | stackStore _ _ | stackStoreAny _ _ | stackLoad _ _ | stackLoadAny _ _
        | stackGetSize _ | stackSetSize _ | bitmapLoad _ _ | halt _ =>
        simp [flattenApp, flatten, appListFlatten, appListAppend, appendAux])
    program (Nat.le_refl _) tail sectionId next conts breaks

theorem flattenApp_appListFlatten_eq_flatten
    (tail : Bool) (program : Prog Inst Cmp RegImm Binop Memop Addr MlString)
    (sectionId next : Nat) (conts breaks : List Nat) :
    appListFlatten (flattenApp ops zero tail program sectionId next conts breaks)
      = flatten ops zero tail program sectionId next conts breaks :=
  flattenAppBridgeAux ops zero tail program sectionId next conts breaks

end FlattenAppBridge


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


/-- Untagged Flapjack representation bridge for HOL `stack_to_labScript.sml`
`prog_to_section_def` over the `app_list` representation: the section lines are
`append (Append lines (List [Label ...]))` of the `flattenApp` output. Not tagged
because `flattenApp` is parameterised by `ops : FlattenOps ...` whereas HOL
`prog_to_section` uses the fixed global `flatten`. -/
def progToSectionApp {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
    (ops : FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)
    (sectionId : Nat) (program : Prog Inst Cmp RegImm Binop Memop Addr MlString) :
    Section (FlatLine Memop Addr Cmp RegImm MlString AsmInst Word) :=
  let (lines, _, next) :=
    flattenApp ops zero true program sectionId
      (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] []
  { sectionId := sectionId
    lines := appListAppend (.append lines (.list [.label sectionId (if isSeq program then next else 1) 0])) }

/-- The app-list `progToSectionApp` has the same flat lines as the production
`progToSection`, via `flattenApp_appListFlatten_eq_flatten`. -/
theorem progToSectionApp_lines {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
    (ops : FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)
    (sectionId : Nat) (program : Prog Inst Cmp RegImm Binop Memop Addr MlString) :
    (progToSectionApp ops zero sectionId program).lines
      = (progToSection ops zero sectionId program).lines := by
  simp only [progToSectionApp, progToSection]
  cases hA : flattenApp ops zero true program sectionId
      (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] [] with
  | mk lines rA =>
    cases rA with
    | mk a nextA =>
      cases hF : flatten ops zero true program sectionId
          (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] [] with
      | mk linesF rF =>
        cases rF with
        | mk aF nextF =>
          have h1 := flattenApp_appListFlatten_eq_flatten ops zero true program sectionId
            (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] []
          rw [hA, hF] at h1
          simp only [appListFlatten] at h1
          have hlines : appListAppend lines = linesF := congrArg Prod.fst h1
          have hnext : nextA = nextF := congrArg (fun p => p.2.2) h1
          have hsplit :
              appListAppend (AppList.append lines
                  (.list [.label sectionId (if isSeq program then nextA else 1) 0]))
                = linesF ++ [.label sectionId (if isSeq program then nextF else 1) 0] := by
            have hthm := appListAppend_thm lines
              (.list [.label sectionId (if isSeq program then nextA else 1) 0])
              [.label sectionId (if isSeq program then nextA else 1) 0]
            rw [hthm.1, hthm.2.1, hnext, hlines]
          exact hsplit

end Flapjack.Compiler.Backend.StackToLab
