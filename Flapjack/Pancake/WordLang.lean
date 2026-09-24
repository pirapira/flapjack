import Flapjack.Pancake.PanLang
import Flapjack.FiniteMap.Basic
import Flapjack.HolRef
import Flapjack.Word

/-!
# Pancake wordLang word operations

The word-level operation evaluator is shared by Pancake's word and Crepe
semantics. Keep its list behavior beside the Lean Pancake syntax rather than
inside a target backend.
-/

namespace Flapjack

/-! Flapjack's generic implementation helper for CakeML `word_op_def`.
This helper is deliberately untagged because HOL's declaration is over
fixed-width word types, not arbitrary Lean types carrying operation classes. -/
def wordOp [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [Complement α] [OfNat α 0] (operator : BinOp) (values : List α) : Option α :=
  match operator, values with
  | .and, values =>
      some (values.foldr (fun left right => AndOp.and left right)
        (Complement.complement (0 : α)))
  | .add, values => some (values.foldr (fun left right => left + right) 0)
  | .or, values => some (values.foldr (fun left right => OrOp.or left right) 0)
  | .xor, values => some (values.foldr (fun left right => HXor.hXor left right) 0)
  | .sub, [left, right] => some (left - right)
  | _, _ => none

/-! Exact source counterpart of CakeML `wordLang$word_op_def`
(`cakeml/compiler/backend/wordLangScript.sml:302-311`). HOL quantifies over
`'a word`; Lean represents that polymorphic word width by `BitVec width`. -/
@[hol "cakeml/compiler/backend/wordLangScript.sml" "word_op_def"]
def wordOpHOL [NeZero width] (operator : BinOp)
    (values : List (BitVec width)) : Option (BitVec width) :=
  wordOp operator values

/-! ## Faithful backend WordLang syntax

`cakeml/compiler/backend/wordLangScript.sml:14-68` defines the register-level
CakeML backend language on top of the assembly instruction carrier of
`cakeml/compiler/encoders/asm/asmScript.sml`.  The datatypes below mirror that
syntax constructor for constructor so HOL results such as
`wordConvs$extract_labels_def` and
`word_to_wordProof$compile_to_word_conventions` can be stated over the same
program shape.

`WordRegImm`, `WordMemOp`, and `WordStore` are reused from `Flapjack.Word`,
where they already model `asm$reg_imm`, `asm$memop`, and
`stackLang$store_name`; `BinOp`, `Cmp`, and `Shift` model `asm$binop`,
`asm$cmp`, and `ast$shift`.

HOL's `num_set` (`num |-> unit`) is represented by the finite map
`FiniteMap Nat Unit`.  As with every finite-map modeling choice in this
repository this fixes the lookup behaviour of `num_set`.  The audit recorded
in `docs/NUM-SET-AUDIT.md` checks what the wordConvs definitions actually
inspect: `every_name_def` and the `Loop` clause of `every_var_def` enumerate
the `sptree$toAList` domain, but only through `EVERY`, so the HOL result is
independent of `sptree` iteration order (verified directly in
`scripts/hol-probes/num_set_audit_probe.out`); `wf_names_def`/`wf_cutsets_def`
use the `sptree$wf` canonicalisation invariant, which the function carrier
cannot express (see the audit).  The bridge lemmas below state the
order-insensitive domain form and its equivalence to an explicit domain list. -/

/-- Lean model of HOL `num_set` (`num |-> unit`). -/
abbrev WordLangNumSet := FiniteMap Nat Unit

/-- HOL `cutsets = num_set # num_set`. -/
abbrev WordLangCutsets := WordLangNumSet × WordLangNumSet

/-- Order-insensitive reading of HOL's `EVERY P (MAP FST (toAList t))` for a
Lean `num_set` model: every key present in the map satisfies `P`.

This is the domain form the wordConvs `every_name`/`every_var` ports use; it
does not mention `sptree` iteration order. -/
def everyNumSetKey (P : Nat → Bool) (t : WordLangNumSet) : Prop :=
  ∀ k, t k = some () → P k = true

/-- An explicit domain witness for a `num_set` model: a nodup key list that
lists exactly the map's keys.  This is the smallest faithful bridge to HOL's
`toAList` enumeration (order irrelevant) without changing the carrier. -/
def numSetDomainList (keys : List Nat) (t : WordLangNumSet) : Prop :=
  keys.Nodup ∧ ∀ k, t k = some () ↔ k ∈ keys

theorem everyNumSetKey_ext {P : Nat → Bool} {t u : WordLangNumSet}
    (h : ∀ k, t k = u k) : everyNumSetKey P t ↔ everyNumSetKey P u := by
  constructor <;> intro hP k hk
  · exact hP k ((h k).trans hk)
  · exact hP k ((h k).symm.trans hk)

theorem everyNumSetKey_iff_list {P : Nat → Bool} {keys : List Nat} {t : WordLangNumSet}
    (h : numSetDomainList keys t) : everyNumSetKey P t ↔ keys.all P = true := by
  rcases h with ⟨_, hmem⟩
  constructor
  · intro hP
    exact List.all_eq_true.mpr (fun k hk => hP k ((hmem k).mpr hk))
  · intro hall k hk
    exact List.all_eq_true.mp hall k ((hmem k).mp hk)

/-- `asm$arith` (`cakeml/compiler/encoders/asm/asmScript.sml:85-95`). -/
inductive WordLangArith (α : Type u) where
  | binop (operator : BinOp) (destination source : Nat) (right : WordRegImm α)
  | shift (operator : Shift) (destination source : Nat) (right : WordRegImm α)
  | div (destination dividend divisor : Nat)
  | longMul (destinationLeft destinationRight sourceLeft sourceRight : Nat)
  | longDiv (destinationLeft destinationRight sourceLeft sourceRight quotient : Nat)
  | addCarry (destination resultCarry sourceLeft sourceRight : Nat)
  | addOverflow (destination resultCarry sourceLeft sourceRight : Nat)
  | subOverflow (destination resultCarry sourceLeft sourceRight : Nat)
  deriving Repr

/-- `asm$fp` (`cakeml/compiler/encoders/asm/asmScript.sml:87-108`). -/
inductive WordLangFp where
  | fpLess (destination left right : Nat)
  | fpLessEqual (destination left right : Nat)
  | fpEqual (destination left right : Nat)
  | fpAbs (destination source : Nat)
  | fpNeg (destination source : Nat)
  | fpSqrt (destination source : Nat)
  | fpAdd (destination left right : Nat)
  | fpSub (destination left right : Nat)
  | fpMul (destination left right : Nat)
  | fpDiv (destination left right : Nat)
  | fpFma (destination left right : Nat)
  | fpMov (destination source : Nat)
  | fpMovToReg (destinationInteger second sourceFloat : Nat)
  | fpMovFromReg (destinationFloat sourceInteger second : Nat)
  | fpToInt (destination source : Nat)
  | fpFromInt (destination source : Nat)
  deriving DecidableEq, Repr

/-- `asm$addr = Addr reg ('a word)`
(`cakeml/compiler/encoders/asm/asmScript.sml:120-122`). -/
inductive WordLangAddr (α : Type u) where
  | addr (base : Nat) (offset : α)
  deriving Repr

/-- `asm$inst = Skip | Const reg ('a word) | Arith ('a arith) |
`Mem memop reg ('a addr) | FP fp`
(`cakeml/compiler/encoders/asm/asmScript.sml:129-134`). -/
inductive WordLangInst (α : Type u) where
  | skip
  | const (destination : Nat) (value : α)
  | arith (operation : WordLangArith α)
  | mem (operator : WordMemOp) (destination : Nat) (address : WordLangAddr α)
  | fp (operation : WordLangFp)
  deriving Repr

/-- `wordLang$exp` (`cakeml/compiler/backend/wordLangScript.sml:14-21`). -/
inductive WordLangExp (α : Type u) where
  | const (value : α)
  | var (name : Nat)
  | lookup (store : WordStore α)
  | load (address : WordLangExp α)
  | op (operator : BinOp) (args : List (WordLangExp α))
  | shift (operator : Shift) (left right : WordLangExp α)
  deriving Repr

/-- `wordLang$prog` (`cakeml/compiler/backend/wordLangScript.sml:35-68`). -/
inductive WordLangProg (α : Type u) where
  | skip
  | move (priority : Nat) (moves : List (Nat × Nat))
  | inst (instruction : WordLangInst α)
  | assign (name : Nat) (value : WordLangExp α)
  | get (destination : Nat) (store : WordStore α)
  | set (store : WordStore α) (value : WordLangExp α)
  | store (address : WordLangExp α) (value : Nat)
  | mustTerminate (body : WordLangProg α)
  /- `Call ret dest args h`: returned registers, normal/exception cut sets,
     return-handler program, and the two handler labels. -/
  | call (returns : Option (List Nat × WordLangCutsets × WordLangProg α × Nat × Nat))
      (target : Option Nat) (arguments : List Nat)
      (handler : Option (Nat × WordLangProg α × Nat × Nat))
  | seq (first second : WordLangProg α)
  | ite (operator : Cmp) (condition : Nat) (right : WordRegImm α)
      (thenBranch elseBranch : WordLangProg α)
  | loop (liveIn : WordLangNumSet) (body : WordLangProg α) (liveOut : WordLangNumSet)
  | alloc (destination : Nat) (cutsets : WordLangCutsets)
  | storeConsts (source bitmap codeLength dataLength : Nat) (constants : List (Bool × α))
  | raise (exception : Nat)
  | return (label : Nat) (values : List Nat)
  | break (label : Nat)
  | continue (label : Nat)
  | tick
  | opCurrHeap (operator : BinOp) (destination source : Nat)
  | locValue (destination source : Nat)
  | install (codeBuffer codeLength dataBuffer dataLength : Nat) (cutsets : WordLangCutsets)
  | codeBufferWrite (address value : Nat)
  | dataBufferWrite (address value : Nat)
  | ffi (function : FunName) (configuration configurationLength array arrayLength : Nat)
      (live : WordLangCutsets)
  | shareInst (operator : WordMemOp) (name : Nat) (address : WordLangExp α)

/-- HOL `wordLang$exp_to_addr` (`wordLangScript.sml:323-326`): recognises a
`Var` or `Op Add [Var; Const]` address expression. -/
@[hol "cakeml/compiler/backend/wordLangScript.sml" "exp_to_addr_def"]
def expToAddr {width : Nat} :
    WordLangExp (BitVec width) -> Option (WordLangAddr (BitVec width))
  | .var name => some (.addr name 0)
  | .op .add [.var name, .const offset] => some (.addr name offset)
  | _ => none

mutual
/-- HOL `wordLang$every_var_exp` (`wordLangScript.sml:85-91`): every register
occurring in an expression satisfies `P`. -/
@[hol "cakeml/compiler/backend/wordLangScript.sml" "every_var_exp_def"]
def everyVarExp {width : Nat} (P : Nat -> Bool) :
    WordLangExp (BitVec width) -> Bool
  | .var num => P num
  | .load exp => everyVarExp P exp
  | .op _ expressions => everyVarExps P expressions
  | .shift _ left right => everyVarExp P left && everyVarExp P right
  | _ => true

/-- Flapjack helper: the `EVERY (every_var_exp P)` list traversal of HOL
`every_var_exp`. -/
def everyVarExps {width : Nat} (P : Nat -> Bool) :
    List (WordLangExp (BitVec width)) -> Bool
  | [] => true
  | expression :: expressions =>
      everyVarExp P expression && everyVarExps P expressions
end

/-- HOL `wordLang$every_var_imm` (`wordLangScript.sml:93-96`). -/
@[hol "cakeml/compiler/backend/wordLangScript.sml" "every_var_imm_def"]
def everyVarImm {width : Nat} (P : Nat -> Bool) :
    WordRegImm (BitVec width) -> Bool
  | .reg num => P num
  | _ => true

/-- HOL `wordLang$every_var_inst` (`wordLangScript.sml:98-133`). -/
@[hol "cakeml/compiler/backend/wordLangScript.sml" "every_var_inst_def"]
def everyVarInst {width : Nat} (P : Nat -> Bool) :
    WordLangInst (BitVec width) -> Bool
  | .const reg _ => P reg
  | .arith (.binop _ r1 r2 right) => P r1 && P r2 && everyVarImm P right
  | .arith (.shift _ r1 r2 right) => P r1 && P r2 && everyVarImm P right
  | .arith (.div r1 r2 r3) => P r1 && P r2 && P r3
  | .arith (.addCarry r1 r2 r3 r4) => P r1 && P r2 && P r3 && P r4
  | .arith (.addOverflow r1 r2 r3 r4) => P r1 && P r2 && P r3 && P r4
  | .arith (.subOverflow r1 r2 r3 r4) => P r1 && P r2 && P r3 && P r4
  | .arith (.longMul r1 r2 r3 r4) => P r1 && P r2 && P r3 && P r4
  | .arith (.longDiv r1 r2 r3 r4 r5) => P r1 && P r2 && P r3 && P r4 && P r5
  | .mem .load reg (.addr base _) => P reg && P base
  | .mem .store reg (.addr base _) => P reg && P base
  | .mem .load32 reg (.addr base _) => P reg && P base
  | .mem .store32 reg (.addr base _) => P reg && P base
  | .mem .load8 reg (.addr base _) => P reg && P base
  | .mem .store8 reg (.addr base _) => P reg && P base
  | .fp (.fpLess reg _ _) => P reg
  | .fp (.fpLessEqual reg _ _) => P reg
  | .fp (.fpEqual reg _ _) => P reg
  | .fp (.fpMovToReg r1 r2 _) => if width = 64 then P r1 else (P r1 && P r2)
  | .fp (.fpMovFromReg _ r1 r2) => if width = 64 then P r1 else (P r1 && P r2)
  | _ => true

end Flapjack
