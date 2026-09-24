import Flapjack.Compiler.Backend.StackLang
import Flapjack.Pancake.WordLang
import Flapjack.FiniteMap.Basic
import Flapjack.HolRef

/-!
# Faithful Cake `stack_names` renaming transformation

Counterpart of `cakeml/compiler/backend/stack_namesScript.sml`.  This module
ports the pure register-renaming transformation used by the `stack_names`
backend phase:

* `ri_find_name_def`, `inst_find_name_def`, `dest_find_name_def`,
* `comp_def` (HOL defines `comp` through a quotation; the Lean name is
  `progComp`), `prog_comp_def`, `compile_def`,
* `names_ok_def`.

HOL's `find_name` is the `misc$tlookup` overload, i.e.
`find_name f r = (FLOOKUP f r).getD r`, here `findName`.  The definitions are
polymorphic in the machine word (`'a` in HOL) and only inspect registers, so
the Lean port keeps the word carrier as a parameter `α` (the register map is
`Nat |-> Nat`).

The imported carrier shapes are the faithful width-indexed
`Flapjack.WordLangInst`/`WordRegImm`/`WordLangAddr` (`asm$inst` and friends)
and `Flapjack.Compiler.Backend.StackLang.Prog`.  Every clause mirrors its HOL
counterpart one-for-one, including the trailing catch-all arms.
-/

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack

/-- `misc$tlookup` instantiated at the register map: rename a register when it
is in the domain, otherwise keep it.  HOL writes this overload as
`find_name`. -/
def findName (names : FiniteMap Nat Nat) (register : Nat) : Nat :=
  match FLOOKUP names register with
  | some value => value
  | none => register

/-- HOL `ri_find_name_def` (`stack_namesScript.sml:16-19`). -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "ri_find_name_def"]
def riFindName {α : Type} (names : FiniteMap Nat Nat) : WordRegImm α → WordRegImm α
  | .reg register => .reg (findName names register)
  | .imm value => .imm value

/-- HOL `inst_find_name_def` (`stack_namesScript.sml:21-49`). -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "inst_find_name_def"]
def instFindName {α : Type} (names : FiniteMap Nat Nat) : WordLangInst α → WordLangInst α
  | .skip => .skip
  | .const destination value => .const (findName names destination) value
  | .arith (.binop operator destination source right) =>
      .arith (.binop operator (findName names destination) (findName names source) (riFindName names right))
  | .arith (.shift operator destination source right) =>
      .arith (.shift operator (findName names destination) (findName names source) (riFindName names right))
  | .arith (.div r1 r2 r3) =>
      .arith (.div (findName names r1) (findName names r2) (findName names r3))
  | .arith (.addCarry r1 r2 r3 r4) =>
      .arith (.addCarry (findName names r1) (findName names r2) (findName names r3) (findName names r4))
  | .arith (.addOverflow r1 r2 r3 r4) =>
      .arith (.addOverflow (findName names r1) (findName names r2) (findName names r3) (findName names r4))
  | .arith (.subOverflow r1 r2 r3 r4) =>
      .arith (.subOverflow (findName names r1) (findName names r2) (findName names r3) (findName names r4))
  | .arith (.longMul r1 r2 r3 r4) =>
      .arith (.longMul (findName names r1) (findName names r2) (findName names r3) (findName names r4))
  | .arith (.longDiv r1 r2 r3 r4 r5) =>
      .arith (.longDiv (findName names r1) (findName names r2) (findName names r3) (findName names r4) (findName names r5))
  | .mem operator register (.addr base offset) =>
      .mem operator (findName names register) (.addr (findName names base) offset)
  | .fp (.fpLess r f1 f2) => .fp (.fpLess (findName names r) f1 f2)
  | .fp (.fpLessEqual r f1 f2) => .fp (.fpLessEqual (findName names r) f1 f2)
  | .fp (.fpEqual r f1 f2) => .fp (.fpEqual (findName names r) f1 f2)
  | .fp (.fpMovToReg r1 r2 d) => .fp (.fpMovToReg (findName names r1) (findName names r2) d)
  | .fp (.fpMovFromReg d r1 r2) => .fp (.fpMovFromReg d (findName names r1) (findName names r2))
  | instruction => instruction

/-- HOL `dest_find_name_def` (`stack_namesScript.sml:51-54`). -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "dest_find_name_def"]
def destFindName (names : FiniteMap Nat Nat) : Sum Nat Nat → Sum Nat Nat
  | .inr register => .inr (findName names register)
  | other => other

/-- HOL `comp_def` (`stack_namesScript.sml:56-99`).  HOL names the declaration
`comp`; the Lean name records the program-level role. -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "comp_def"]
def progComp {α MlString : Type} (names : FiniteMap Nat Nat) :
    StackLang.Prog (WordLangInst α) Cmp (WordRegImm α) BinOp WordMemOp (WordLangAddr α) MlString →
    StackLang.Prog (WordLangInst α) Cmp (WordRegImm α) BinOp WordMemOp (WordLangAddr α) MlString
  | .halt register => .halt (findName names register)
  | .raise exception => .raise (findName names exception)
  | .break label => .break label
  | .continue label => .continue label
  | .ret value => .ret (findName names value)
  | .inst instruction => .inst (instFindName names instruction)
  | .locValue destination label entry => .locValue (findName names destination) label entry
  | .seq first second => .seq (progComp names first) (progComp names second)
  | .ite operator register right thenBranch elseBranch =>
      .ite operator (findName names register) (riFindName names right)
        (progComp names thenBranch) (progComp names elseBranch)
  | .loop body => .loop (progComp names body)
  | .call returnHandler target handler =>
      .call (match returnHandler with
             | none => none
             | some (returnProgram, linkRegister, l1, l2) =>
                 some (progComp names returnProgram, findName names linkRegister, l1, l2))
        (destFindName names target)
        (match handler with
         | none => none
         | some (handlerProgram, l1, l2) => some (progComp names handlerProgram, l1, l2))
  | .install r1 r2 r3 r4 r5 =>
      .install (findName names r1) (findName names r2) (findName names r3)
        (findName names r4) (findName names r5)
  | .shMemOp operator register (.addr base offset) =>
      .shMemOp operator (findName names register) (.addr (findName names base) offset)
  | .codeBufferWrite r1 r2 => .codeBufferWrite (findName names r1) (findName names r2)
  | .ffi function r1 r2 r3 r4 r5 =>
      .ffi function (findName names r1) (findName names r2) (findName names r3)
        (findName names r4) (findName names r5)
  | .jumpLower r1 r2 target => .jumpLower (findName names r1) (findName names r2) target
  | program => program

/-- HOL `prog_comp_def` (`stack_namesScript.sml:101-103`). -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "prog_comp_def"]
def progCompEntry {α MlString : Type} (names : FiniteMap Nat Nat)
    (entry : Nat × StackLang.Prog (WordLangInst α) Cmp (WordRegImm α) BinOp WordMemOp (WordLangAddr α) MlString) :
    Nat × StackLang.Prog (WordLangInst α) Cmp (WordRegImm α) BinOp WordMemOp (WordLangAddr α) MlString :=
  (entry.1, progComp names entry.2)

/-- HOL `compile_def` (`stack_namesScript.sml:105-107`). -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "compile_def"]
def compile {α MlString : Type} (names : FiniteMap Nat Nat)
    (program : List (Nat × StackLang.Prog (WordLangInst α) Cmp (WordRegImm α) BinOp WordMemOp (WordLangAddr α) MlString)) :
    List (Nat × StackLang.Prog (WordLangInst α) Cmp (WordRegImm α) BinOp WordMemOp (WordLangAddr α) MlString) :=
  program.map (progCompEntry names)

/-- HOL `names_ok_def` (`stack_namesScript.sml:111-116`). -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "names_ok_def"]
def namesOk (names : FiniteMap Nat Nat) (regCount : Nat) (avoidRegs : List Nat) : Bool :=
  let xs := (List.range (regCount - avoidRegs.length)).map (findName names)
  decide xs.Nodup && xs.all (fun x => x < regCount && !(avoidRegs.contains x))

end Flapjack.Compiler.Backend.StackNames
