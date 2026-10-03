import Flapjack.Compiler.Backend.StackNames.InstructionNames

namespace Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/stack_namesScript.sml" "comp_def"
  (words_as_type_indexed_bitvec)]
def progCompHOL {width : Nat} [NeZero width] (names : Flapjack.Spt Nat) :
    HolProg width → HolProg width
  | .halt register => .halt (findNameSpt names register)
  | .raise exception => .raise (findNameSpt names exception)
  | .break label => .break label
  | .continue label => .continue label
  | .ret value => .ret (findNameSpt names value)
  | .inst instruction =>
      .inst (instFindNameHOL names instruction)
  | .locValue destination label entry => .locValue (findNameSpt names destination) label entry
  | .seq first second => .seq (progCompHOL names first) (progCompHOL names second)
  | .ite operator register right thenBranch elseBranch =>
      .ite operator (findNameSpt names register)
        (riFindNameHOL names right)
        (progCompHOL names thenBranch) (progCompHOL names elseBranch)
  | .loop body => .loop (progCompHOL names body)
  | .call returnHandler target handler =>
      .call (match returnHandler with
             | none => none
             | some (returnProgram, linkRegister, l1, l2) =>
                 some (progCompHOL names returnProgram, findNameSpt names linkRegister, l1, l2))
        (destFindNameHOL names target)
        (match handler with
         | none => none
         | some (handlerProgram, l1, l2) => some (progCompHOL names handlerProgram, l1, l2))
  | .install r1 r2 r3 r4 r5 =>
      .install (findNameSpt names r1) (findNameSpt names r2) (findNameSpt names r3)
        (findNameSpt names r4) (findNameSpt names r5)
  | .shMemOp operator register (.addr base offset) =>
      .shMemOp operator (findNameSpt names register) (.addr (findNameSpt names base) offset)
  | .codeBufferWrite r1 r2 => .codeBufferWrite (findNameSpt names r1) (findNameSpt names r2)
  | .ffi function r1 r2 r3 r4 r5 =>
      .ffi function (findNameSpt names r1) (findNameSpt names r2) (findNameSpt names r3)
        (findNameSpt names r4) (findNameSpt names r5)
  | .jumpLower r1 r2 target => .jumpLower (findNameSpt names r1) (findNameSpt names r2) target
  | program => program

/-- Exact-name-tree correspondence to the existing raw lookup compiler.
This is Flapjack infrastructure; no target evaluation or equality premise. -/
theorem progCompHOL_eq_lookupHelper {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (program : HolProg width) :
    progCompHOL names program = progComp (fun key => Flapjack.sptLookup key names) program := by
  induction program using progCompHOL.induct <;>
    try simp_all [progCompHOL, progComp, findNameSpt_eq_lookupHelper,
      ← instFindNameHOL_toWord, ← riFindNameHOL_toWord]

  case case11 rh target handler ihHandler ihReturn =>
    cases rh with
    | none =>
      cases handler with
      | none => simp [progCompHOL, progComp, destFindNameHOL_eq_lookupHelper]
      | some h =>
        obtain ⟨body, l1, l2⟩ := h
        simp_all [progCompHOL, progComp, destFindNameHOL_eq_lookupHelper]
    | some ret =>
      obtain ⟨body, reg, l1, l2⟩ := ret
      cases handler with
      | none => simp_all [progCompHOL, progComp, destFindNameHOL_eq_lookupHelper, findNameSpt_eq_lookupHelper]
      | some h =>
        obtain ⟨body, l1, l2⟩ := h
        simp_all [progCompHOL, progComp, destFindNameHOL_eq_lookupHelper, findNameSpt_eq_lookupHelper]

@[hol "cakeml/compiler/backend/stack_namesScript.sml" "prog_comp_def"
  (words_as_type_indexed_bitvec)]
def progCompEntryHOL {width : Nat} [NeZero width] {Name : Type} (names : Flapjack.Spt Nat)
    (entry : Name × HolProg width) : Name × HolProg width :=
  (entry.1, progCompHOL names entry.2)

/-- HOL's section names are an arbitrary type `'a`; executed callers use `Nat`. -/
@[hol "cakeml/compiler/backend/stack_namesScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
def compileHOL {width : Nat} [NeZero width] {Name : Type} (names : Flapjack.Spt Nat)
    (program : List (Name × HolProg width)) : List (Name × HolProg width) :=
  program.map (progCompEntryHOL names)

@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "MAP_FST_compile"
  (words_as_type_indexed_bitvec)]
theorem map_fst_compileHOL {width : Nat} [NeZero width] {Name : Type} (names : Flapjack.Spt Nat)
    (program : List (Name × HolProg width)) :
    (compileHOL names program).map Prod.fst = program.map Prod.fst := by
  simp [compileHOL, progCompEntryHOL, List.map_map]

end Flapjack.Compiler.Backend.StackNames
