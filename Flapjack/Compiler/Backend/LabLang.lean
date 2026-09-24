/-!
# Faithful Cake LabLang syntax

Generic datatype carriers and constructor shapes from
`cakeml/compiler/backend/labLangScript.sml` (`lab`: line 16, `asm_with_lab`:
23, `asm_or_cbw`: 34, `line`: 39, `sec`: 48). This module does not identify
these types with the executable `Flapjack.Lab` representation; that adapter is
part of the open `stack_to_lab` port.
-/

namespace Flapjack.Compiler.Backend.LabLang

/-- HOL `labLang$lab`. -/
inductive Lab where
  | lab (sectionNumber label : Nat)
  deriving Repr, BEq, DecidableEq

/-- HOL `labLang$asm_with_lab`, with imported carriers explicit. -/
inductive AsmWithLab (Cmp RegImm MlString : Type) where
  | jump (target : Lab)
  | jumpCmp (operator : Cmp) (condition : Nat) (right : RegImm) (target : Lab)
  | call (target : Lab)
  | locValue (register : Nat) (target : Lab)
  | callFFI (function : MlString)
  | install
  | halt
  deriving Repr, BEq, DecidableEq

/-- HOL `labLang$asm_or_cbw`. -/
inductive AsmOrCbw (Inst Memop Addr : Type) where
  | asmi (instruction : Inst)
  | cbw (left right : Nat)
  | shareMem (operator : Memop) (register : Nat) (address : Addr)
  deriving Repr, BEq, DecidableEq

/-- HOL `labLang$line`; bytes are fixed `word8` values and positions retain
the width-polymorphic HOL word carrier. -/
inductive Line (AsmOrCbw AsmWithLab Word : Type) where
  | label (sectionId label length : Nat)
  | asm (instruction : AsmOrCbw) (encoded : List (BitVec 8)) (length : Nat)
  | labAsm (instruction : AsmWithLab) (position : Word)
      (encoded : List (BitVec 8)) (length : Nat)
  deriving Repr, BEq, DecidableEq

/-- HOL `labLang$sec`. -/
structure Section (Line : Type) where
  sectionId : Nat
  lines : List Line
  deriving Repr, BEq, DecidableEq

end Flapjack.Compiler.Backend.LabLang
