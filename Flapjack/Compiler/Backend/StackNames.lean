import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Backend.StackCarrier
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
`find_name f r = (FLOOKUP f r).getD r`, here `findName`.  The register map is
`Nat |-> Nat`.

HOL's transformations are polymorphic in `'a`, but `'a` is an actual word type
carried by `Reg`/`Imm`/`inst`/`addr`; the tagged ports are therefore
width-indexed at `BitVec width` (with `[NeZero width]`), and the
program-level transformations are stated over the canonical shared-word
carrier `StackCarrier.ProgW (BitVec width)`, whose single parameter matches
HOL's `'a`.  Only the executable Boolean `namesOk` remains untagged, with the
tagged proposition-valued `namesOkHOL` beside it.
-/

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack
open Flapjack.Compiler.Backend.StackCarrier

/-- `misc$tlookup` instantiated at the register map: rename a register when it
is in the domain, otherwise keep it.  HOL writes this overload as
`find_name`. -/
def findName (names : FiniteMap Nat Nat) (register : Nat) : Nat :=
  match FLOOKUP names register with
  | some value => value
  | none => register

/-- HOL `ri_find_name_def` (`stack_namesScript.sml:16-19`), polymorphic in the
word type as in HOL (width-indexed, since HOL's `'a` is an actual word): rename the register of a register-immediate. -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "ri_find_name_def"]
def riFindName {width : Nat} [NeZero width] (names : FiniteMap Nat Nat) :
    WordRegImm (BitVec width) → WordRegImm (BitVec width)
  | .reg register => .reg (findName names register)
  | .imm value => .imm value

/-- HOL `inst_find_name_def` (`stack_namesScript.sml:21-49`), polymorphic in
the word type as in HOL (width-indexed, since HOL's `'a` is an actual word): rename every register of an instruction. -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "inst_find_name_def"]
def instFindName {width : Nat} [NeZero width] (names : FiniteMap Nat Nat) :
    WordLangInst (BitVec width) → WordLangInst (BitVec width)
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

/-- HOL `comp_def` (`stack_namesScript.sml:56-99`): rename registers throughout
a program.  Stated over the canonical shared-word carrier `ProgW`, whose single
type parameter matches HOL's `'a`. -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "comp_def"]
def progComp {width : Nat} [NeZero width] (names : FiniteMap Nat Nat) :
    ProgW (BitVec width) → ProgW (BitVec width)
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

/-- HOL `prog_comp_def` (`stack_namesScript.sml:101-103`) over `ProgW`. -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "prog_comp_def"]
def progCompEntry {width : Nat} [NeZero width] (names : FiniteMap Nat Nat)
    (entry : Nat × ProgW (BitVec width)) : Nat × ProgW (BitVec width) :=
  (entry.1, progComp names entry.2)

/-- HOL `compile_def` (`stack_namesScript.sml:105-107`) over `ProgW`. -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "compile_def"]
def compile {width : Nat} [NeZero width] (names : FiniteMap Nat Nat)
    (program : List (Nat × ProgW (BitVec width))) : List (Nat × ProgW (BitVec width)) :=
  program.map (progCompEntry names)

/-- HOL `MAP_FST_compile` (`stack_namesProofScript.sml:268-272`): renaming
preserves the function identifiers of a program. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "MAP_FST_compile"]
theorem map_fst_compile {width : Nat} [NeZero width] (names : FiniteMap Nat Nat)
    (program : List (Nat × ProgW (BitVec width))) :
    (compile names program).map Prod.fst = program.map Prod.fst := by
  induction program with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨n, p⟩ := head
      simp [compile, progCompEntry]

/-- Executable Boolean counterpart of HOL `names_ok`; the tagged predicate
below retains HOL's proposition-valued result. -/
def namesOk (names : FiniteMap Nat Nat) (regCount : Nat) (avoidRegs : List Nat) : Bool :=
  let xs := (List.range (regCount - avoidRegs.length)).map (findName names)
  decide xs.Nodup && xs.all (fun x => x < regCount && !(avoidRegs.contains x))

/-- Exact proposition-shaped port of HOL `names_ok_def`
(`stack_namesScript.sml:111-116`): generated names are distinct, below the
register bound, and disjoint from the avoided registers. -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "names_ok_def"]
def namesOkHOL (names : FiniteMap Nat Nat) (regCount : Nat)
    (avoidRegs : List Nat) : Prop :=
  let xs := (List.range (regCount - avoidRegs.length)).map (findName names)
  xs.Nodup ∧ xs.all (fun x => x < regCount && !(avoidRegs.contains x)) = true

/-- The executable Boolean check implements the HOL-shaped predicate. -/
theorem namesOkHOL_iff_bool (names : FiniteMap Nat Nat) (regCount : Nat)
    (avoidRegs : List Nat) :
    namesOkHOL names regCount avoidRegs ↔ namesOk names regCount avoidRegs = true := by
  simp [namesOkHOL, namesOk, Bool.and_eq_true]

end Flapjack.Compiler.Backend.StackNames
