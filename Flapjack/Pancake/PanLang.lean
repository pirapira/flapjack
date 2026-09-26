import Flapjack.HolRef
import Flapjack.FiniteMap.Basic

/-!
The core Flapjack syntax.

This is the initial Lean counterpart of CakeML's `panLang` theory. Identifiers
are represented by `String`, while expressions remain polymorphic in their
word-value type, matching the polymorphic HOL AST.
-/

namespace Flapjack

abbrev StructName := String
abbrev FieldName := String
abbrev VarName := String
abbrev FunName := String
abbrev ExceptionId := String
abbrev DeclarationName := String

/- FLAPJACK-SPECIFIC (not an exact HOL port): the `Named` field carrier differs.
HOL `panLangScript.sml:21` aliases `stcname = ``:mlstring``` and the datatype is
`shape = One | Comb (shape list) | Named stcname`, whereas Lean aliases
`StructName := String` (PanLang.lean:14). Constructor arities/order match, but
`StructName = String` is not `mlstring`, so no `@[hol]` tag is attached until an
MlString identifier carrier (or a reviewed production bridge) lands; tracked by
bead `flapjack-pxn.18.3.5.8`. The datatype remains the production implementation. -/
inductive Shape where
  | one
  | comb (fields : List Shape)
  | named (name : StructName)
  deriving Repr

namespace Shape

def shapeSize : Shape → Nat
  | .one => 1
  | .comb fields => fields.foldl (fun total field => total + shapeSize field) 0
  | .named _ => 1

/-! Production String rendering follows Pancake's `shape_to_str_def` equations.
    It is not an exact HOL port because this shape carrier's named fields use
    `String` rather than `mlstring`; `Shape.shapeToString_eq_shapeToStrHOL_toStringOfBytes`
    proves the production bridge on byte-ranged shapes. -/
def shapeToString : Shape → String
  | .one => "1"
  | .comb [] => "{}"
  | .comb (head :: tail) =>
      "{" ++ shapeToString head ++
        tail.foldl (fun result field => result ++ "," ++ shapeToString field) "" ++ "}"
  | .named name => name

@[simp] theorem shapeSize_one : shapeSize Shape.one = 1 := by simp [shapeSize]

@[simp] theorem shapeSize_named (name : StructName) : shapeSize (Shape.named name) = 1 := by
  simp [shapeSize]

end Shape

/-- Exact port of Cake's `struct_info` datatype (`cakeml/pancake/panLangScript.sml:121`):
field types `(fldname # shape) list` (`List (FieldName × Shape)`) and `num` (`Nat`) match,
without the production-only `StructInfo.shapedFields` cache. -/
structure StructInfoHOL where
  fields : List (FieldName × Shape)
  size : Nat
  deriving Repr

/-- HOL-shaped struct context: the association list `(stcname # struct_info) list`
(`(StructName × StructInfoHOL) list`) that `is_wf_shape` ranges over via `ALOOKUP`. -/
abbrev StructContextHOL := List (StructName × StructInfoHOL)

/-- Key-polymorphic first-match association-list lookup: the Lean counterpart
    of HOL `alist$ALOOKUP`. The association list may use any key type with
    `BEq`; under `[LawfulBEq κ]` the `==` test reflects HOL's `=`, so this is
    the exact `ALOOKUP` operation (the production `InfoMap` is the
    `κ = String` instance). It is not `@[hol]`-tagged: the HOL source
    (`alistTheory`, cited by HOL `FLOOKUP` users) is HOL stdlib, outside the
    CakeML submodule, and the definition quantifies a `[BEq κ]` instance where
    HOL uses `=`. Direct evidence: the review/audit bead
    `flapjack-pxn.18.3.6.5`, the equality to core `List.lookup`
    (`lookupInfo_eq_lookup`, `Proofs/PanStructs.lean:263`) under `[LawfulBEq
    String]`, and the tagged `ALOOKUP_MAP3`/`ALOOKUP_MAP4` ports. -/
def lookupInfo [BEq κ] (key : κ) : List (κ × α) → Option α
  | [] => none
  | (candidate, value) :: entries =>
      if candidate == key then some value else lookupInfo key entries

/- FLAPJACK-SPECIFIC (not an exact HOL port): executable mirror of HOL
`panLang$is_wf_shape` (`cakeml/pancake/panLangScript.sml:139`). The clauses are
reproduced literally: `One` is `T`; `Comb shs` is `EVERY (is_wf_shape ctxt) shs`;
`Named nm` is `case ALOOKUP ctxt nm of SOME _ => T | NONE => F`, rendered with
the first-match `lookupInfo` (the String-keyed `alist$ALOOKUP` analogue) and
`isSome` as the Bool rendering of `<> NONE`. The tag is WITHDRAWN because the
context carrier does not match: HOL keys the association list by
`stcname = ``:mlstring``` (`panLangScript.sml:21`) while Lean's
`StructContextHOL` keys it by `StructName := String` (PanLang.lean:14).
Likewise, `.named` in the input uses String-backed `Shape`, and the context's
field names are String-backed, unlike HOL's `shape`/`struct_info` carriers.
Matching `ALOOKUP` at the concrete `BEq String` instance is not HOL equality;
the six direct HOL rows and Lean guards exercise the clauses but do not prove
byte-level carrier equivalence. An exact port needs the MlString/ShapeHOL
carriers (bead `flapjack-pxn.18.3.5.8`), so no `@[hol]` tag is attached. -/
mutual
  def isWfShapeHOL (context : StructContextHOL) : Shape → Bool
    | .one => true
    | .comb shapes => isWfShapeListHOL context shapes
    | .named name => (lookupInfo name context).isSome
  termination_by shape => sizeOf shape
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def isWfShapeListHOL (context : StructContextHOL) :
      List Shape → Bool
    | [] => true
    | shape :: shapes => isWfShapeHOL context shape && isWfShapeListHOL context shapes
  termination_by shapes => sizeOf shapes
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

inductive BinOp where
  | add
  | sub
  | and
  | or
  | xor
  deriving DecidableEq, Repr

/-! Exact source counterpart of Pancake's `binop_to_str_def`
    (`panStaticScript.sml:588-596`). -/
def binopToString : BinOp → String
  | .add => "Add"
  | .sub => "Sub"
  | .and => "And"
  | .or => "Or"
  | .xor => "Xor"

/-- Exact port of Cake's `panop` datatype (`cakeml/pancake/panLangScript.sml:41`):
the single nullary constructor `Mul` matches. -/
@[hol "cakeml/pancake/panLangScript.sml" "panop"]
inductive PanOp where
  | mul
  deriving DecidableEq, Repr

/-! Exact source counterpart of Pancake's `panop_to_str_def`
    (`panStaticScript.sml:599-603`). -/
def panopToString : PanOp → String
  | .mul => "Mul"

inductive Cmp where
  | equal
  | lower
  | less
  | test
  | notEqual
  | notLower
  | notLess
  | notTest
  deriving DecidableEq, Repr

/-!
Pancake has two order relations on words: `Lower` is unsigned while `Less`
is signed. Keeping them in a target-supplied interface avoids accidentally
using Lean's single `LT` relation for both source-language operations.
The fallback instance below is useful for abstract scalar models whose only
available order is `LT`; word targets should provide their own instance.
-/

class PanCmp (α : Type u) where
  lower : α → α → Bool
  less : α → α → Bool

instance (priority := 10) panCmpOfLt [LT α]
    [DecidableRel (fun left right : α => left < right)] : PanCmp α where
  lower left right := decide (left < right)
  less left right := decide (left < right)

inductive Shift where
  | lsl
  | lsr
  | asr
  | ror
  deriving DecidableEq, Repr

/-!
The source language distinguishes logical and arithmetic right shifts, and
also exposes rotate-right.  These operations are separate from Lean's
homogeneous `ShiftRight` class because the latter denotes logical shift for
the target words.
-/

class ArithmeticShiftRight (α : Type u) where
  arithmeticShiftRight : α → α → α

class RotateRightOp (α : Type u) where
  rotateRight : α → α → α

/-- Exact port of Cake's `varkind` datatype (`cakeml/pancake/panLangScript.sml:45`):
the two nullary constructors `Local`/`Global` match. -/
@[hol "cakeml/pancake/panLangScript.sml" "varkind"]
inductive VarKind where
  | local
  | global
  deriving DecidableEq, Repr

/-! Exact source counterpart of Pancake's `varkind_to_str_def`
    (`pan_passesScript.sml:124-127`). -/
def varKindToString : VarKind → String
  | .global => "global"
  | .local => "local"

inductive Exp (α : Type u) where
  | const (value : α)
  | var (kind : VarKind) (name : VarName)
  | rStruct (fields : List (Exp α))
  | rField (index : Nat) (value : Exp α)
  | nStruct (name : StructName) (fields : List (FieldName × Exp α))
  | nField (name : FieldName) (value : Exp α)
  | load (shape : Shape) (address : Exp α)
  | load32 (address : Exp α)
  | loadByte (address : Exp α)
  | op (operator : BinOp) (args : List (Exp α))
  | panOp (operator : PanOp) (args : List (Exp α))
  | cmp (operator : Cmp) (left right : Exp α)
  | shift (operator : Shift) (left right : Exp α)
  | baseAddr
  | topAddr
  | bytesInWord
  deriving Repr

/-! ## Width-indexed `Exp` / HOL `exp` constructor audit (option A)

Full constructor/field audit of HOL `panLangScript.sml` `exp` (lines 49-68)
against the production `Exp (α : Type u)` at `α := BitVec width`:

| # | HOL `exp`                         | Lean `Exp (BitVec width)`                 |
|---|-----------------------------------|-------------------------------------------|
| 1 | `Const ('a word)`                 | `const (BitVec width)`                    |
| 2 | `Var varkind varname`             | `var VarKind VarName`                     |
| 3 | `RStruct (exp list)`              | `rStruct (List (Exp ·))`                  |
| 4 | `RField index exp`                | `rField Nat (Exp ·)`                      |
| 5 | `NStruct stcname ((fldname # exp) list)` | `nStruct StructName (List (FieldName × Exp ·))` |
| 6 | `NField fldname exp`              | `nField FieldName (Exp ·)`                |
| 7 | `Load shape exp`                  | `load Shape (Exp ·)`                      |
| 8 | `Load32 exp`                      | `load32 (Exp ·)`                          |
| 9 | `LoadByte exp`                    | `loadByte (Exp ·)`                        |
|10 | `Op binop (exp list)`             | `op BinOp (List (Exp ·))`                 |
|11 | `Panop panop (exp list)`          | `panOp PanOp (List (Exp ·))`              |
|12 | `Cmp cmp exp exp`                 | `cmp Cmp (Exp ·) (Exp ·)`                 |
|13 | `Shift shift exp exp`             | `shift Shift (Exp ·) (Exp ·)`             |
|14 | `BaseAddr`                        | `baseAddr`                                |
|15 | `TopAddr`                         | `topAddr`                                 |
|16 | `BytesInWord`                     | `bytesInWord`                             |

Constructor names, arities and order match, and the word field matches once the
word length is fixed (`α := BitVec width` is exactly HOL `'a word` at
`'a = width`); the executed compiler front already uses this instantiation.

IMPORTANT GAP (review HOLD, 2026-09-24): the *identifier* fields do NOT match.
HOL `panLangScript.sml:21-31` aliases `stcname`/`fldname`/`varname`/`funname`/
`eid` to `mlstring`, while production `PanLang.lean:14-18` aliases
`StructName`/`FieldName`/`VarName`/`FunName`/`ExceptionId` to Lean `String`.
Row 2 (`Var varname`), row 5 (`NStruct stcname`/`fldname`) and row 6
(`NField fldname`) therefore retain a string-carrier mismatch even at
`Exp (BitVec width)`. A faithful `Exp` carrier must use `MlString`
identifiers or a reviewed production bridge (bead `flapjack-pxn.18.3.5.8`).

Consequence for option A (single production datatype): every "correspondence"
statement is definitional reflexivity on the same Lean term, and constructor
freeness/injectivity is generic `Exp` injection — i.e. tautological proof sites.
This slice therefore records the audit as evidence and adds NO theorems and NO
`@[hol]` tag. A substantive representation refinement requires distinct carriers
(option B/C of bead flapjack-pxn.18.3.5.3.1.2), or an explicit reviewer decision
that the audit itself establishes the width-specialized `Const` shape. -/


/-- Exact port of Cake's `opsize` datatype (`cakeml/pancake/panLangScript.sml:49`):
the four nullary constructors `Op8`/`OpW`/`Op32`/`Op16` match in order. -/
@[hol "cakeml/pancake/panLangScript.sml" "opsize"]
inductive OpSize where
  | op8
  | opW
  | op32
  | op16
  deriving DecidableEq, Repr

/-- Exact port of Cake's `primop` datatype (`cakeml/pancake/panLangScript.sml:72`):
the single nullary constructor `AddCarry` matches. -/
@[hol "cakeml/pancake/panLangScript.sml" "primop"]
inductive PrimOp where
  | addCarry
  deriving DecidableEq, Repr

/-! Exact source counterpart of Pancake's `primop_to_str_def`
    (`panStaticScript.sml:606-610`). -/
def primopToString : PrimOp → String
  | .addCarry => "AddCarry"

/-! The source `word_sh` operation receives a natural shift amount extracted
    from a target word.  Targets provide the word width and this extraction so
    the generic source evaluator can preserve CakeML's out-of-range failure
    rule. -/
class PanShiftWidth (α : Type u) where
  width : Nat
  amount : α → Nat

/-! Natural-number pipeline instantiations (used by pass-local fixtures) treat
    the word width as the 64-bit RISC-V target and extract shift amounts
    unchanged. -/
instance natPanShiftWidth : PanShiftWidth Nat where
  width := 64
  amount := id

/-- Lean's executable `Prog` follows the constructor layout of HOL
    `panLang$prog` (`cakeml/pancake/panLangScript.sml:82-100`), including the
    recursive program positions and nested `Call` metadata. It is not an exact
    port: its expression payloads use the generic `Exp α`, whose `Const` case
    contains `α`, while HOL `Const` is indexed by the target word type. Keep
    this useful generic syntax untagged until an exact word-indexed expression
    interface is available. -/
inductive Prog (α : Type u) where
  | skip
  | dec (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
  | assign (kind : VarKind) (name : VarName) (value : Exp α)
  | primitive (name : VarName) (operator : PrimOp) (args : List (Exp α))
  | store (address value : Exp α)
  | store32 (address value : Exp α)
  | storeByte (address value : Exp α)
  | seq (first second : Prog α)
  | ite (condition : Exp α) (thenBranch elseBranch : Prog α)
  | while (condition : Exp α) (body : Prog α)
  | break
  | continue
  | call (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α))) (name : FunName) (args : List (Exp α))
  | decCall (name : VarName) (shape : Shape) (function : FunName)
      (args : List (Exp α)) (body : Prog α)
  | extCall (function : FunName) (configuration configurationLength array arrayLength : Exp α)
  | raise (exception : ExceptionId) (value : Exp α)
  | return (value : Exp α)
  | shMemLoad (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α)
  | shMemStore (size : OpSize) (address value : Exp α)
  | tick
  | annot (tag text : String)
  deriving Repr

/-- Lean's `FunDecl` has the HOL field layout
    (`cakeml/pancake/panLangScript.sml:102-109`), but is not an exact port:
    `body` uses generic `Prog α` and therefore inherits the mismatch between
    generic `Exp α.Const` and HOL's word-indexed `Const`. Keep it untagged. -/
structure FunDecl (α : Type u) where
  name : FunName
  inline : Bool
  exported : Bool
  params : List (VarName × Shape)
  body : Prog α
  returnShape : Shape
  deriving Repr

/-- Lean's `Decl` follows the constructor layout of HOL `panLang$decl`
    (`cakeml/pancake/panLangScript.sml:112-116`), but is not an exact port:
    function bodies use generic `FunDecl α` and value declarations contain
    generic `Exp α`, inheriting the mismatch between generic `Exp α.Const` and
    HOL's word-indexed `Const`. Keep it untagged. -/
inductive Decl (α : Type u) where
  | function (declaration : FunDecl α)
  | decl (shape : Shape) (name : DeclarationName) (value : Exp α)
  | exnDecl (exception : ExceptionId) (shape : Shape)
  | name (struct : StructName) (fields : List (FieldName × Shape))
  deriving Repr

/-! Direct source-shaped counterpart of `panLang$inlinable`: only function
    declarations expose their inline bit. -/
def inlinable : Decl α → Bool
  | .function declaration => declaration.inline
  | _ => false

/- FLAPJACK-SPECIFIC (not an exact HOL port): executable mirror of
    `panLang$exceptions` (`panLangScript.sml:328-337`), preserving exception
    declaration order and dropping all other constructors. HOL takes its
    word-indexed `decl list` and returns `(mlstring # shape) list` (`eid` is
    `mlstring`, `panLangScript.sml:29`). This function instead takes generic
    `Decl α` and returns `(ExceptionId × Shape)` entries with
    `ExceptionId := String`; `Decl α` and monomorphic `Shape` are not the
    reviewed exact HOL carriers either. The direct HOL-EVAL fixture and Lean
    parity guard exercise the five selection clauses, not byte-level carrier
    equivalence. The `@[hol]` tag therefore remains WITHDRAWN; an exact
    counterpart needs the MlString/ShapeHOL declaration carrier (bead
    `flapjack-pxn.18.3.5.8`). -/
def exceptionEntries : List (Decl α) → List (ExceptionId × Shape)
  | [] => []
  | .exnDecl exception shape :: declarations =>
      (exception, shape) :: exceptionEntries declarations
  | _ :: declarations => exceptionEntries declarations
termination_by declarations => sizeOf declarations

/- FLAPJACK-SPECIFIC (not an exact HOL port): clause-structured mirror of HOL
    `panLang$functions` (`panLangScript.sml:319-326`), retaining every
    function's metadata while skipping value, exception, and struct
    declarations; the tuple order matches HOL (name, params, body, return
    shape). The `@[hol]` tag is WITHDRAWN for more than a name representation
    change: HOL's input is a `decl list` whose `Function` payload is
    word-indexed (`'a prog` bodies, `mlstring` names, `shape` params/return) and
    its result is `(mlstring # (mlstring # shape) list # 'a prog # shape)
    list`; this production function instead quantifies over generic `Decl α`
    with String-backed names and monomorphic `Shape`/`Prog α`. The
    `names_as_string` qualifier cannot account for the generic expression and
    program carriers. Direct HOL-EVAL rows are recorded in
    `scripts/hol-probes/pan_lang_functions_probe.out` and reproduced by
    `Flapjack/Test/PanLangFunctionsParity.lean`. Exact-carrier replacement is
    tracked by `flapjack-pxn.18.3.5.8`; this analogue remains useful to the
    executed compiler and is deliberately untagged. -/
def functionEntries : List (Decl α) →
    List (FunName × List (VarName × Shape) × Prog α × Shape)
  | [] => []
  | .function declaration :: declarations =>
      (declaration.name, declaration.params, declaration.body,
        declaration.returnShape) :: functionEntries declarations
  | _ :: declarations => functionEntries declarations

def nestedSeq : List (Prog α) → Prog α
  | [] => .skip
  | statement :: statements => .seq statement (nestedSeq statements)

/-! Source-shaped port of Pancake's `pan_seqs_def`
    (`pan_passesScript.sml:184-190`).  Annotation-led sequences are kept as
    one display item; all other sequences are flattened recursively. -/
def isAnnot : Prog α → Bool
  | .annot _ _ => true
  | _ => false

def panSeqs : Prog α → List (Prog α)
  | .seq first second =>
      if isAnnot first then [.seq first second]
      else panSeqs first ++ panSeqs second
  | program => [program]
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! The exception identifiers syntactically reachable from a Pancake program.
    This follows `panLang$exp_ids_def`; in particular, a call contributes its
    handler identifier and the identifiers reachable in that handler, while
    ordinary calls and all non-handler forms contribute no identifiers. -/
def expIds : Prog α → List ExceptionId
  | .skip => []
  | .dec _ _ _ body => expIds body
  | .assign _ _ _ => []
  | .primitive _ _ _ => []
  | .store _ _ => []
  | .store32 _ _ => []
  | .storeByte _ _ => []
  | .seq first second => expIds first ++ expIds second
  | .ite _ thenBranch elseBranch => expIds thenBranch ++ expIds elseBranch
  | .while _ body => expIds body
  | .break => []
  | .continue => []
  | .call (some (_, some (exception, _, handler))) _ _ =>
      exception :: expIds handler
  | .call _ _ _ => []
  | .decCall _ _ _ _ body => expIds body
  | .extCall _ _ _ _ _ => []
  | .raise exception _ => [exception]
  | .return _ => []
  | .shMemLoad _ _ _ _ => []
  | .shMemStore _ _ _ => []
  | .tick => []
  | .annot _ _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- Cake's `exp_ids_nested_seq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:128`): the exception
    identifiers of a nested sequence are the concatenation of the statements'
    identifiers. -/
theorem expIds_nestedSeq (statements : List (Prog α)) :
    expIds (nestedSeq statements) = (statements.map expIds).flatten := by
  induction statements with
  | nil => simp [nestedSeq, expIds]
  | cons statement statements ih => simp [nestedSeq, expIds, ih]

/-- Source-shaped counterpart of Pancake's `panProps$exps_of`
    (`cakeml/pancake/semantics/panPropsScript.sml:1336`): collect the
    expressions that occur directly in a program. -/
def expsOf : Prog α → List (Exp α)
  | .raise _ e => [e]
  | .dec _ _ e body => e :: expsOf body
  | .seq p q => expsOf p ++ expsOf q
  | .ite e p q => e :: (expsOf p ++ expsOf q)
  | .while e body => e :: expsOf body
  | .call info _ es =>
      es ++ (match info with
             | some (_, some (_, _, handler)) => expsOf handler
             | _ => [])
  | .decCall _ _ _ es body => es ++ expsOf body
  | .store a b => [a, b]
  | .store32 a b => [a, b]
  | .storeByte a b => [a, b]
  | .return e => [e]
  | .extCall _ e1 e2 e3 e4 => [e1, e2, e3, e4]
  | .assign _ _ e => [e]
  | .primitive _ _ es => es
  | .shMemLoad _ _ _ e => [e]
  | .shMemStore _ a b => [a, b]
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- Cake's `pan_exps_of_nested_seq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:1018`): the expressions
    of a nested sequence are the concatenation of the statements' expressions. -/
theorem expsOf_nestedSeq (statements : List (Prog α)) :
    expsOf (nestedSeq statements) = (statements.map expsOf).flatten := by
  induction statements with
  | nil => simp [nestedSeq, expsOf]
  | cons statement statements ih => simp [nestedSeq, expsOf, ih]

/-! Direct source-shaped counterpart of `panLang$fun_ids`: collect the
    statically referenced function names, including call-handler bodies and
    declaration-call bodies. -/
def funIds : Prog α → List FunName
  | .dec _ _ _ body => funIds body
  | .seq first second => funIds first ++ funIds second
  | .ite _ thenBranch elseBranch => funIds thenBranch ++ funIds elseBranch
  | .while _ body => funIds body
  | .call (some (_, some (_, _, handler))) name _ => name :: funIds handler
  | .call _ name _ => [name]
  | .decCall _ _ function _ body => function :: funIds body
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! Split a flat value list according to the source shape sizes.  This is the
    direct Lean counterpart of `panLang$with_shape` (`cakeml/pancake/panLangScript.sml:214-218`):

      `(with_shape [] _ = []) ∧`
      `(with_shape (sh::shs) e = TAKE (size_of_shape sh) e :: with_shape shs (DROP (size_of_shape sh) e))`

    The clause structure matches clause-for-clause (`List.take`/`List.drop` model
    HOL `TAKE`/`DROP`, and drops the leftover tail exactly like HOL).  The
    carrier, however, is the production pair: this definition uses the
    production `Shape` (`Shape.named : String`) and the untagged
    `Shape.shapeSize`, and is polymorphic in the list element type `α`, whereas
    HOL `with_shape` uses the exact `shape` (`named : mlstring`, tagged
    `ShapeHOL`) and the reviewed `size_of_shape` (`sizeOfShapeHOL`,
    `Flapjack/Pancake/PanLang/Shape.lean`).  No supported qualifier authorizes a
    `Shape`/`shapeSize` substitution, so this declaration is deliberately
    untagged with a documented carrier mismatch; the faithful port over
    `ShapeHOL`/`sizeOfShapeHOL` is tracked by `flapjack-pxn.18.3.5.8`.  Values
    left over after the requested shapes are intentionally ignored, and short
    inputs are handled by `List.take`/`List.drop` just like CakeML's
    `TAKE`/`DROP`.  Direct HOL oracle rows are
    `scripts/hol-probes/pan_lang_with_shape_probe.out`
    (`empty_shapes=[]`, `one_comb_named=[[1]; [2; 3]; [4]]`,
    `short_input=[[7]; []]`), replayed by `Flapjack/Test/PanWithShapeParity.lean`. -/
def withShape : List Shape → List α → List (List α)
  | [], _ => []
  | shape :: shapes, values =>
      values.take (Shape.shapeSize shape) ::
        withShape shapes (values.drop (Shape.shapeSize shape))
termination_by shapes => sizeOf shapes
decreasing_by
  all_goals decreasing_trivial

theorem withShape_length (shapes : List Shape) (values : List α) :
    (withShape shapes values).length = shapes.length := by
  induction shapes generalizing values with
  | nil => simp [withShape]
  | cons shape shapes ih => simp [withShape, ih]

/-! Counterpart of Cake's `length_with_shape_eq_shape`
    (`cakeml/pancake/semantics/panPropsScript.sml:265`): the flat-value split
    produces one sub-list per requested shape, so the hypothesis on the flat
    value count is retained only for fidelity with the original statement. -/
theorem length_withShape_eq_shape (shapes : List Shape) (values : List α)
    (hvalues : values.length = Shape.shapeSize (.comb shapes)) :
    shapes.length = (withShape shapes values).length := by
  have _ := hvalues
  rw [withShape_length]

theorem shapeSize_comb_cons (head : Shape) (tail : List Shape) :
    Shape.shapeSize (.comb (head :: tail)) =
      Shape.shapeSize head + Shape.shapeSize (.comb tail) := by
  have hfold : ∀ (shapes : List Shape) (acc : Nat),
      shapes.foldl (fun total field => total + Shape.shapeSize field) acc =
        acc + shapes.foldl (fun total field => total + Shape.shapeSize field) 0 := by
    intro shapes
    induction shapes with
    | nil => intro acc; simp
    | cons shape shapes ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih (acc + Shape.shapeSize shape), ih (0 + Shape.shapeSize shape)]
        omega
  simp only [Shape.shapeSize, List.foldl_cons, Nat.zero_add]
  rw [hfold tail (Shape.shapeSize head)]

/-! Counterpart of Cake's `all_distinct_with_shape`
    (`cakeml/pancake/semantics/panPropsScript.sml:286`): the `n`-th component
    produced by the flat-value split is distinct whenever the flat value list
    is distinct. -/
theorem all_distinct_withShape (shapes : List Shape) (values : List α) (n : Nat)
    (hdistinct : values.Nodup)
    (hn : n < shapes.length)
    (hvalues : values.length = Shape.shapeSize (.comb shapes)) :
    ((withShape shapes values)[n]'(by rw [withShape_length]; exact hn)).Nodup := by
  revert values n
  induction shapes with
  | nil => intro values n hdistinct hn hvalues; exact absurd hn (Nat.not_lt_zero n)
  | cons shape shapes ih =>
      intro values n hdistinct hn hvalues
      cases n with
      | zero =>
          simp only [withShape]
          exact hdistinct.take
      | succ k =>
          simp only [withShape]
          simp only [List.length_cons] at hn
          have hn' : k < shapes.length := by omega
          have hvalues' : (values.drop (Shape.shapeSize shape)).length =
              Shape.shapeSize (.comb shapes) := by
            rw [List.length_drop, hvalues, shapeSize_comb_cons, Nat.add_sub_cancel_left]
          exact ih (values.drop (Shape.shapeSize shape)) k hdistinct.drop hn' hvalues'

/-! Counterpart of Cake's `mem_with_shape_length`
    (`cakeml/pancake/semantics/panPropsScript.sml:328`). -/
theorem mem_withShape_length (shapes : List Shape) (values : List α) (n : Nat)
    (hvalues : values.length = Shape.shapeSize (.comb shapes))
    (hn : n < shapes.length) :
    (withShape shapes values)[n]'(by rw [withShape_length]; exact hn) ∈
      withShape shapes values := by
  have _ := hvalues
  exact List.getElem_mem _

/-! Counterpart of Cake's `el_mem_with_shape`
    (`cakeml/pancake/semantics/panPropsScript.sml:307`). -/
theorem mem_of_withShape_mem (shapes : List Shape) (values : List α) (n : Nat)
    (x : α)
    (hn : n < (withShape shapes values).length)
    (hvalues : values.length = Shape.shapeSize (.comb shapes))
    (hmem : x ∈ (withShape shapes values)[n]'hn) :
    x ∈ values := by
  revert values n x
  induction shapes with
  | nil =>
      intro values n x hn hvalues hmem
      simp [withShape] at hn
  | cons shape shapes ih =>
      intro values n x hn hvalues hmem
      simp only [withShape] at hn hmem
      cases n with
      | zero =>
          exact List.mem_of_mem_take (by simpa using hmem)
      | succ k =>
          apply List.mem_of_mem_drop
          have hk : k < (withShape shapes (values.drop (Shape.shapeSize shape))).length := by
            simp only [List.length_cons] at hn; omega
          have hvalues' : (values.drop (Shape.shapeSize shape)).length =
              Shape.shapeSize (.comb shapes) := by
            rw [List.length_drop, hvalues, shapeSize_comb_cons, Nat.add_sub_cancel_left]
          exact ih (values.drop (Shape.shapeSize shape)) k x hk hvalues' hmem

/-! Counterpart of Cake's `with_shape_el_take_drop_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:341`). -/
theorem withShape_getElem_eq_take_drop (shapes : List Shape) (values : List α)
    (n : Nat)
    (hvalues : values.length = Shape.shapeSize (.comb shapes))
    (hn : n < shapes.length) :
    (withShape shapes values)[n]'(by rw [withShape_length]; exact hn) =
      (values.drop (Shape.shapeSize (.comb (shapes.take n)))).take
        (Shape.shapeSize (shapes[n]'hn)) := by
  revert values n
  induction shapes with
  | nil => intro values n hvalues hn; exact absurd hn (Nat.not_lt_zero n)
  | cons shape shapes ih =>
      intro values n hvalues hn
      cases n with
      | zero => simp [withShape, Shape.shapeSize]
      | succ k =>
          have hn' : k < shapes.length := by
            simp only [List.length_cons] at hn; omega
          have hvalues' : (values.drop (Shape.shapeSize shape)).length =
              Shape.shapeSize (.comb shapes) := by
            rw [List.length_drop, hvalues, shapeSize_comb_cons, Nat.add_sub_cancel_left]
          simp only [withShape, List.getElem_cons_succ, List.take_succ_cons]
          rw [ih (values.drop (Shape.shapeSize shape)) k hvalues' hn']
          rw [shapeSize_comb_cons]
          rw [← List.drop_drop]

/-! Counterpart of Cake's `comp_field`
    (`cakeml/pancake/pan_to_crepScript.sml:28`).  Cake returns the pair
    `(TAKE (size_of_shape sh) es, sh)` for the selected field and recurses on
    `DROP (size_of_shape sh) es`; here we keep only the expression-list
    component (the shape component is `shapes[index]`).  Cake's empty-list
    fallback `[Const 0w]` is represented by `[]` because every use below
    assumes `index < shapes.length`, so that branch is unreachable. -/
def compField (index : Nat) (shapes : List Shape) (values : List α) : List α :=
  match shapes with
  | [] => []
  | shape :: shapes =>
      if index = 0 then values.take (Shape.shapeSize shape)
      else compField (index - 1) shapes (values.drop (Shape.shapeSize shape))

/-- Counterpart of Cake's `mem_comp_field`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:666`): an expression of
    a selected field is an expression of the flattened record. -/
theorem mem_compField_imp_mem (index : Nat) (shapes : List Shape)
    (values : List α) (candidate : α)
    (hindex : index < shapes.length)
    (hvalues : values.length = Shape.shapeSize (.comb shapes))
    (hmem : candidate ∈ compField index shapes values) :
    candidate ∈ values := by
  revert values index
  induction shapes with
  | nil => intro index values hindex; exact absurd hindex (Nat.not_lt_zero index)
  | cons shape shapes ih =>
      intro index values hindex hvalues hmem
      simp only [List.length_cons] at hindex
      cases index with
      | zero =>
          simp only [compField] at hmem
          exact List.mem_of_mem_take hmem
      | succ k =>
          have hk : k < shapes.length := by omega
          have hvalues' : (values.drop (Shape.shapeSize shape)).length =
              Shape.shapeSize (.comb shapes) := by
            rw [List.length_drop, hvalues, shapeSize_comb_cons, Nat.add_sub_cancel_left]
          simp only [compField, Nat.succ_ne_zero, if_false] at hmem
          exact List.mem_of_mem_drop
            (ih k (values.drop (Shape.shapeSize shape)) hk hvalues' hmem)

/-- Counterpart of Cake's `mem_comp_field_lem`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:397`): with no index
    bound the selected field is still a sublist of the flattened record (Cake's
    `Const 0w` fallback is represented by the empty list here). -/
theorem mem_compField_imp_mem_of_any (index : Nat) (shapes : List Shape)
    (values : List α) (candidate : α)
    (hmem : candidate ∈ compField index shapes values) :
    candidate ∈ values := by
  revert values index
  induction shapes with
  | nil =>
      intro index values hmem
      exact absurd hmem (by simp [compField])
  | cons shape shapes ih =>
      intro index values hmem
      cases index with
      | zero =>
          simp only [compField] at hmem
          exact List.mem_of_mem_take hmem
      | succ k =>
          simp only [compField, Nat.succ_ne_zero, if_false] at hmem
          exact List.mem_of_mem_drop
            (ih k (values.drop (Shape.shapeSize shape)) hmem)

/-! Counterpart of Cake's `all_distinct_take`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:384`). -/
theorem nodup_take (values : List α) (n : Nat) (h : values.Nodup) :
    (values.take n).Nodup := h.take

/-! Counterpart of Cake's `all_distinct_drop`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:392`). -/
theorem nodup_drop (values : List α) (n : Nat) (h : values.Nodup) :
    (values.drop n).Nodup := h.drop

/-! Counterpart of Cake's `disjoint_take_drop_sum`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:399`): a prefix and a
    suffix separated by `m` elements of a duplicate-free list cannot share an
    element. -/
theorem listDisjoint_take_drop_sum (values : List α) (n m p : Nat)
    (h : values.Nodup) :
    ListDisjoint (values.take n) ((values.drop (n + m)).take p) := by
  intro value hleft hright
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hleft
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hright
  rw [List.getElem_take] at hix
  rw [List.getElem_take] at hjx
  rw [List.getElem_drop] at hjx
  have hiLen : i < values.length := by
    have := hi; rw [List.length_take] at this; omega
  have hjLen : (n + m) + j < values.length := by
    have := hj; rw [List.length_take, List.length_drop] at this; omega
  have hinj : i = (n + m) + j := (List.getElem_inj h).mp (hix.trans hjx.symm)
  have hiN : i < n := by
    have := hi; rw [List.length_take] at this; omega
  omega

/-! Counterpart of Cake's `disjoint_drop_take_sum`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:413`). -/
theorem listDisjoint_drop_take_sum (values : List α) (n m p : Nat)
    (h : values.Nodup) :
    ListDisjoint ((values.drop (n + m)).take p) (values.take n) :=
  fun value hright hleft =>
    listDisjoint_take_drop_sum values n m p h value hleft hright

/-! Counterpart of Cake's `distinct_lists_eq_disjoint`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:102`): Cake defines
    `distinct_lists xs ys` as `EVERY (\x. ~MEM x ys) xs`, which is exactly the
    `ListDisjoint` predicate below. -/
theorem forall_not_mem_iff_listDisjoint (xs ys : List α) :
    (∀ x, x ∈ xs → x ∉ ys) ↔ ListDisjoint xs ys :=
  Iff.rfl

/-! Counterpart of Cake's `distinct_lists_append`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:108`). -/
theorem listDisjoint_append (xs ys : List α) (h : (xs ++ ys).Nodup) :
    ListDisjoint xs ys := by
  have hdisj := (List.nodup_append.mp h).2.2
  intro value hx hy
  exact absurd rfl (hdisj value hx value hy)

/-! Counterpart of Cake's `distinct_lists_commutes`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:116`). -/
theorem listDisjoint_comm (xs ys : List α) (h : ListDisjoint xs ys) :
    ListDisjoint ys xs :=
  fun value hy hx => h value hx hy

/-! Counterpart of Cake's `genlist_distinct_max`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:208`): the
    `GENLIST (λx. SUC x + m) n` slot enumeration is disjoint from any list
    whose elements are bounded by `m`. -/
theorem listDisjoint_range_add (n m : Nat) (ys : List Nat)
    (h : ∀ y, y ∈ ys → y ≤ m) :
    ListDisjoint ((List.range n).map (fun x => x + 1 + m)) ys := by
  intro x hx hy
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hx
  have hlt : m < i + 1 + m := by omega
  have hle := h (i + 1 + m) hy
  omega

/-! Counterpart of Cake's `genlist_distinct_max'`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:221`): the shifted
    `GENLIST (λx. SUC x + (m + p)) n` slot enumeration is disjoint from any
    list whose elements are bounded by `m`. -/
theorem listDisjoint_range_add_shift (n m p : Nat) (ys : List Nat)
    (h : ∀ y, y ∈ ys → y ≤ m) :
    ListDisjoint ((List.range n).map (fun x => x + 1 + (m + p))) ys := by
  intro x hx hy
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hx
  have hlt : m < i + 1 + (m + p) := by omega
  have hle := h (i + 1 + (m + p)) hy
  omega

/-! Counterpart of Cake's `distinct_lists_cons`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:125`). -/
theorem listDisjoint_of_append_left (ns xs ys zs : List α)
    (h : ListDisjoint (ns ++ xs) (ys ++ zs)) :
    ListDisjoint xs zs :=
  fun value hx hz =>
    h value (List.mem_append_right ns hx) (List.mem_append_right ys hz)

/-! Counterpart of Cake's `distinct_lists_simp_cons`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:133`). -/
theorem listDisjoint_of_cons_right (xs : List α) (y : α) (ys : List α)
    (h : ListDisjoint xs (y :: ys)) :
    ListDisjoint xs ys :=
  fun value hx hy => h value hx (List.mem_cons.mpr (Or.inr hy))

/-! Counterpart of Cake's `distinct_lists_append_intro`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:141`). -/
theorem listDisjoint_append_right (xs ys zs : List α)
    (hys : ListDisjoint xs ys) (hzs : ListDisjoint xs zs) :
    ListDisjoint xs (ys ++ zs) :=
  fun value hx hmem => by
    rcases List.mem_append.mp hmem with h | h
    · exact hys value hx h
    · exact hzs value hx h

/-! Counterpart of Cake's `distinct_lists_append_right_elim`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:150`). -/
theorem listDisjoint_append_right_elim (xs ys zs : List α)
    (h : ListDisjoint xs (ys ++ zs)) :
    ListDisjoint xs ys ∧ ListDisjoint xs zs :=
  ⟨fun value hx hy => h value hx (List.mem_append_left zs hy),
   fun value hx hz => h value hx (List.mem_append_right ys hz)⟩

/-! Counterpart of Cake's `all_distinct_take_frop_disjoint`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:534`). -/
theorem listDisjoint_take_drop (xs : List α) (n : Nat) (h : xs.Nodup) :
    ListDisjoint (xs.take n) (xs.drop n) := by
  intro value htake hdrop
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem htake
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hdrop
  rw [List.getElem_take] at hix
  rw [List.getElem_drop] at hjx
  have hiLen : i < xs.length := by
    have := hi; rw [List.length_take] at this; omega
  have hjLen : n + j < xs.length := by
    have := hj; rw [List.length_drop] at this; omega
  have hinj : i = n + j := (List.getElem_inj h).mp (hix.trans hjx.symm)
  have hiN : i < n := by
    have := hi; rw [List.length_take] at this; omega
  omega

/-! Counterpart of Cake's `disjoint_not_mem_el`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:606`). -/
theorem not_mem_of_listDisjoint_getElem (xs ys : List α) (n : Nat)
    (h : ListDisjoint xs ys) (hn : n < xs.length) :
    xs[n] ∉ ys :=
  fun hmem => h xs[n] (List.getElem_mem hn) hmem

/-! Shifted-window form of Cake's `disjoint_take_drop_sum`: a suffix window and
    a later suffix window of the same distinct list are disjoint whenever the
    first window ends before the second window starts. -/
theorem listDisjoint_drop_take_drop_take (values : List α) (a b c d : Nat)
    (hbound : b ≤ c) (h : values.Nodup) :
    ListDisjoint ((values.drop a).take b) ((values.drop (a + c)).take d) := by
  intro value hleft hright
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hleft
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hright
  rw [List.getElem_take] at hix
  rw [List.getElem_drop] at hix
  rw [List.getElem_take] at hjx
  rw [List.getElem_drop] at hjx
  have hiN : i < b := by
    have := hi; rw [List.length_take] at this; omega
  have hinj : a + i = (a + c) + j := (List.getElem_inj h).mp (hix.trans hjx.symm)
  omega

/-! Additivity of the flat size over an appended shape list (used to relate the
    offsets of the two `withShape` windows). -/
theorem shapeSize_comb_append (left right : List Shape) :
    Shape.shapeSize (.comb (left ++ right)) =
      Shape.shapeSize (.comb left) + Shape.shapeSize (.comb right) := by
  have hfold : ∀ (shapes : List Shape) (acc : Nat),
      shapes.foldl (fun total field => total + Shape.shapeSize field) acc =
        acc + shapes.foldl (fun total field => total + Shape.shapeSize field) 0 := by
    intro shapes
    induction shapes with
    | nil => intro acc; simp
    | cons shape shapes ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih (acc + Shape.shapeSize shape), ih (0 + Shape.shapeSize shape)]
        omega
  simp only [Shape.shapeSize, List.foldl_append]
  rw [hfold right (left.foldl (fun total field => total + Shape.shapeSize field) 0)]

/-! Counterpart of Cake's `all_distinct_disjoint_with_shape`
    (`cakeml/pancake/semantics/panPropsScript.sml:409`), in the strictly
    increasing index case. -/
theorem listDisjoint_withShape_getElem_lt (shapes : List Shape) (values : List α)
    (n n' : Nat) (hdistinct : values.Nodup)
    (hn : n < shapes.length) (hn' : n' < shapes.length) (hlt : n < n')
    (hvalues : values.length = Shape.shapeSize (.comb shapes)) :
    ListDisjoint
      ((withShape shapes values)[n]'(by rw [withShape_length]; exact hn))
      ((withShape shapes values)[n']'(by rw [withShape_length]; exact hn')) := by
  rw [withShape_getElem_eq_take_drop shapes values n hvalues hn,
    withShape_getElem_eq_take_drop shapes values n' hvalues hn']
  have htake : shapes.take n' = shapes.take n ++ (shapes.drop n).take (n' - n) := by
    have h := List.take_add (l := shapes) (i := n) (j := n' - n)
    have hsum : n + (n' - n) = n' := by omega
    rwa [hsum] at h
  have hsize : Shape.shapeSize (.comb (shapes.take n')) =
      Shape.shapeSize (.comb (shapes.take n)) +
        Shape.shapeSize (.comb ((shapes.drop n).take (n' - n))) := by
    rw [htake, shapeSize_comb_append]
  rw [hsize]
  have hle : Shape.shapeSize (shapes[n]'hn) ≤
      Shape.shapeSize (.comb ((shapes.drop n).take (n' - n))) := by
    obtain ⟨k, hk⟩ : ∃ k, n' - n = k + 1 := ⟨n' - n - 1, by omega⟩
    rw [hk, List.drop_eq_getElem_cons (l := shapes) hn, List.take_succ_cons,
      shapeSize_comb_cons]
    omega
  exact listDisjoint_drop_take_drop_take values
    (Shape.shapeSize (.comb (shapes.take n)))
    (Shape.shapeSize (shapes[n]'hn))
    (Shape.shapeSize (.comb ((shapes.drop n).take (n' - n))))
    (Shape.shapeSize (shapes[n']'hn')) hle hdistinct

/-! Counterpart of Cake's `all_distinct_disjoint_with_shape`
    (`cakeml/pancake/semantics/panPropsScript.sml:409`): two distinct components
    of the flat-value split are disjoint whenever the flat value list is
    distinct. -/
theorem listDisjoint_withShape_getElem (shapes : List Shape) (values : List α)
    (n n' : Nat) (hdistinct : values.Nodup)
    (hn : n < shapes.length) (hn' : n' < shapes.length) (hne : n ≠ n')
    (hvalues : values.length = Shape.shapeSize (.comb shapes)) :
    ListDisjoint
      ((withShape shapes values)[n]'(by rw [withShape_length]; exact hn))
      ((withShape shapes values)[n']'(by rw [withShape_length]; exact hn')) := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact listDisjoint_withShape_getElem_lt shapes values n n' hdistinct hn hn'
      hlt hvalues
  · intro value hleft hright
    exact listDisjoint_withShape_getElem_lt shapes values n' n hdistinct hn' hn
      hlt hvalues value hright hleft

/-! Membership in a `zip` exposes the common index and both components.  Lean
    core has no `List.mem_zip`, so this is the helper used to read Cake's
    `MEM ... (ZIP ...)` hypotheses. -/
theorem mem_zip_getElem (left : List α) (right : List β) (pair : α × β)
    (hmem : pair ∈ left.zip right) :
    ∃ (i : Nat) (hi : i < left.length) (hj : i < right.length),
      left[i]'hi = pair.1 ∧ right[i]'hj = pair.2 := by
  obtain ⟨i, hbound, hpi⟩ := List.mem_iff_getElem.mp hmem
  rw [List.length_zip] at hbound
  rw [List.getElem_zip] at hpi
  refine ⟨i, Nat.lt_of_lt_of_le hbound (Nat.min_le_left ..),
    Nat.lt_of_lt_of_le hbound (Nat.min_le_right ..), ?_, ?_⟩
  · exact congrArg Prod.fst hpi
  · exact congrArg Prod.snd hpi

/-! Counterpart of Cake's `all_distinct_mem_zip_disjoint_with_shape`
    (`cakeml/pancake/semantics/panPropsScript.sml:452`): two triples of the
    aligned `(label, shape, component)` view whose labels differ have disjoint
    components. -/
theorem listDisjoint_of_mem_zip_withShape (labels : List α) (shapes : List Shape)
    (values : List β) (left right : α × (Shape × List β))
    (hlabels : labels.length = shapes.length)
    (hshapes : shapes.length = (withShape shapes values).length)
    (hdistinct : values.Nodup)
    (hvalues : values.length = Shape.shapeSize (.comb shapes))
    (hleft : left ∈ labels.zip (shapes.zip (withShape shapes values)))
    (hright : right ∈ labels.zip (shapes.zip (withShape shapes values)))
    (hne : left.1 ≠ right.1) :
    ListDisjoint left.2.2 right.2.2 := by
  obtain ⟨i, hi, _hiInner, hleftFirst, hleftSecond⟩ :=
    mem_zip_getElem labels (shapes.zip (withShape shapes values)) left hleft
  obtain ⟨j, hj, _hjInner, hrightFirst, hrightSecond⟩ :=
    mem_zip_getElem labels (shapes.zip (withShape shapes values)) right hright
  rw [List.getElem_zip] at hleftSecond
  rw [List.getElem_zip] at hrightSecond
  have hiShapes : i < shapes.length := by rw [hlabels] at hi; exact hi
  have hjShapes : j < shapes.length := by rw [hlabels] at hj; exact hj
  have hiValues : i < (withShape shapes values).length := by
    rw [hshapes] at hiShapes; exact hiShapes
  have hjValues : j < (withShape shapes values).length := by
    rw [hshapes] at hjShapes; exact hjShapes
  have hleftComponent : left.2.2 = (withShape shapes values)[i]'hiValues := by
    simpa using (congrArg Prod.snd hleftSecond).symm
  have hrightComponent : right.2.2 = (withShape shapes values)[j]'hjValues := by
    simpa using (congrArg Prod.snd hrightSecond).symm
  have hneIndex : i ≠ j := by
    intro heq
    subst heq
    exact hne (by rw [← hleftFirst, ← hrightFirst])
  rw [hleftComponent, hrightComponent]
  exact listDisjoint_withShape_getElem shapes values i j hdistinct hiShapes hjShapes
    hneIndex hvalues

/-! Counterpart of Cake's `el_reduc_tl`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:360`): an index of the
    tail is an index of the original list, shifted by one. -/
theorem getElem_tail_eq (values : List α) (n : Nat) (hn : 0 < n)
    (hbound : n < values.length) :
    values[n]'hbound = (values.tail)[n - 1]'(by rw [List.length_tail]; omega) := by
  rw [List.getElem_tail]
  congr 1
  omega

/-! Counterpart of Cake's `el_pair_map_fst_el`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:722`): the first
    component of an indexed triple is the indexed first projection. -/
theorem getElem_map_fst (values : List (α × β × γ)) (n : Nat)
    (hbound : n < values.length) {x : α} {y : β} {z : γ}
    (heq : values[n]'hbound = (x, y, z)) :
    x = (values.map Prod.fst)[n]'(by rwa [List.length_map]) := by
  rw [List.getElem_map]
  rw [heq]

/-! Counterpart of Cake's `all_distinct_el_fst_same_eq`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:732`): in a list whose
    first projections are distinct, equal first components force equal indices. -/
theorem getElem_fst_inj (values : List (α × β)) (n n' : Nat)
    (hnodup : (values.map Prod.fst).Nodup)
    (hn : n < values.length) (hn' : n' < values.length)
    {x : α} {y y' : β}
    (heq : values[n]'hn = (x, y)) (heq' : values[n']'hn' = (x, y')) :
    n = n' := by
  have hmapped : (values.map Prod.fst)[n]'(by rwa [List.length_map]) =
      (values.map Prod.fst)[n']'(by rwa [List.length_map]) := by
    rw [List.getElem_map, List.getElem_map, heq, heq']
  exact (List.getElem_inj hnodup).mp hmapped

/-! Counterpart of Cake's `max_foldr_lt`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:768`): a member of a
    list is strictly below the fold with `max` plus any positive slack. -/
theorem mem_lt_foldr_max_add (values : List Nat) (x n m : Nat)
    (hmem : x ∈ values) (hle : n ≤ x) (hm : 0 < m) :
    x < values.foldr max n + m := by
  have _ := hle
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · have hmax : x ≤ max x (tail.foldr max n) := Nat.le_max_left x _
        omega
      · have hrec := ih hmem
        have hmax : tail.foldr max n ≤ max head (tail.foldr max n) := Nat.le_max_right _ _
        omega

/-- A fold of `max` never drops below its accumulator. -/
theorem le_foldr_max (values : List Nat) (bound : Nat) :
    bound ≤ values.foldr max bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldr_cons]
      exact Nat.le_trans ih (Nat.le_max_right head (List.foldr max bound tail))

/-- A fold of `max` with accumulator `bound` returns `bound` when every element
    is at most `bound`. -/
theorem foldr_max_eq_of_le (values : List Nat) (bound : Nat)
    (h : ∀ x ∈ values, x ≤ bound) :
    values.foldr max bound = bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldr_cons]
      rw [Nat.max_eq_right
        (Nat.le_trans (h head (by simp)) (le_foldr_max tail bound))]
      exact ih (fun x hx => h x (by simp [hx]))

/-- `MAX_LIST` of the first `n` naturals is `n - 1`. -/
theorem range_foldr_max_self (n : Nat) :
    (List.range n).foldr max n = n :=
  foldr_max_eq_of_le (List.range n) n (fun x hx => by
    rw [List.mem_range] at hx
    omega)

/-- Cake's `MAX_LIST_i_genlist` (`pan_commonPropsScript.sml:712`):
    `MAX_LIST (GENLIST I n) = n - 1`, with `List.range` as the Flapjack
    counterpart of `GENLIST I n` and `foldr max 0` as `MAX_LIST`. -/
theorem range_foldr_max (n : Nat) :
    (List.range n).foldr max 0 = n - 1 := by
  induction n with
  | zero => simp [List.range_zero]
  | succ n _ih =>
      rw [List.range_succ, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      rw [Nat.max_eq_left (Nat.zero_le n)]
      rw [range_foldr_max_self]
      omega

/-- Cake's `mem_genlist_add_suc_val` (`pan_commonPropsScript.sml:234`):
    every value in `GENLIST (SUC · + k) n` lies in the interval `(k, n + k]`. -/
theorem mem_genlist_add_suc_val (n x k : Nat) :
    x ∈ (List.range n).map (fun i => i + 1 + k) → k < x ∧ x ≤ n + k := by
  intro hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hi
  omega

/-- Cake's `genlist_distinct_max` (`pan_commonPropsScript.sml:208`): a
    `GENLIST` starting just above `m` is disjoint from any list bounded by
    `m`. -/
theorem genlist_distinct_max (n m : Nat) (ys : List Nat)
    (hys : ∀ y, y ∈ ys → y ≤ m) :
    ListDisjoint ((List.range n).map (fun i => i + 1 + m)) ys := by
  intro value hx hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hi
  have := hys _ hy
  omega

/-- Cake's `genlist_distinct_max'` (`pan_commonPropsScript.sml:221`): the
    `m + p` variant of `genlist_distinct_max`. -/
theorem genlist_distinct_max' (n m p : Nat) (ys : List Nat)
    (hys : ∀ y, y ∈ ys → y ≤ m) :
    ListDisjoint ((List.range n).map (fun i => i + 1 + (m + p))) ys := by
  intro value hx hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hi
  have := hys _ hy
  omega

/-- Cake's `zero_not_mem_genlist_offset` (`pan_commonPropsScript.sml:367`): for
    a list of at most 31 elements, the `GENLIST` of one-based successors has no
    zero when read as 5-bit words. -/
theorem zero_not_mem_genlist_offset {α : Type} (t : List α) (h : t.length ≤ 31) :
    (0 : BitVec 5) ∉
      (List.range t.length).map (fun i => BitVec.ofNat 5 (i + 1)) := by
  intro hmem
  obtain ⟨i, hi, hzero⟩ := List.mem_map.mp hmem
  rw [List.mem_range] at hi
  have htoNat : (BitVec.ofNat 5 (i + 1)).toNat = i + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hzero] at htoNat
  simp at htoNat

/-- Cake's `MAP2` (`pan_commonScript.sml`): pointwise combination of two lists,
    truncating at the shorter one. -/
def panMap2 (f : α → β → γ) : List α → List β → List γ
  | x :: xs, y :: ys => f x y :: panMap2 f xs ys
  | _, _ => []

/-- Cake's `MAP3` (`pan_commonScript.sml`): pointwise combination of three
    lists, truncating at the shortest one. -/
def panMap3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: panMap3 f xs ys zs
  | _, _, _ => []

/-- Counterpart of Cake's `MAP3_MAP2`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml:827`): a three-way
    pointwise map is a two-way pointwise map over the zipped first two lists
    when the lengths agree. -/
theorem panMap3_eq_map2_zip (f : α → β → γ → δ) (l1 : List α) (l2 : List β)
    (l3 : List γ) (h1 : l1.length = l3.length) (h2 : l2.length = l3.length) :
    panMap3 f l1 l2 l3 =
      panMap2 (fun (pair : α × β) (z : γ) => f pair.1 pair.2 z)
        (l1.zip l2) l3 := by
  induction l3 generalizing l1 l2 with
  | nil =>
      obtain rfl := List.eq_nil_of_length_eq_zero h1
      obtain rfl := List.eq_nil_of_length_eq_zero h2
      rfl
  | cons z zs ih =>
      rw [List.length_cons] at h1 h2
      cases l1 with
      | nil => simp at h1
      | cons x xs =>
          cases l2 with
          | nil => simp at h2
          | cons y ys =>
              have h1' : xs.length = zs.length := by simp at h1; omega
              have h2' : ys.length = zs.length := by simp at h2; omega
              simp only [panMap3, panMap2, List.zip_cons_cons, ih xs ys h1' h2']

/-- Counterpart of Cake's `map_map2_fst`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3799`): when two lists
    have equal length, projecting the first component of a pointwise map that
    keeps its first argument recovers the first list.  CakeML states this for
    the concrete `MAP2` used by `make_funcs`; here the second component is
    arbitrary, since only `FST` is observed. -/
theorem panMap2_fst_eq {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (panMap2 (fun x y => (x, f x y)) xs ys).map Prod.fst = xs := by
  intro xs
  induction xs with
  | nil => intro ys _; rfl
  | cons x xs ih =>
      intro ys hlen
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons] at hlen
          simp only [panMap2, List.map_cons]
          rw [ih ys (by omega)]

/-- Counterpart of Cake's `mem_lookup_fromalist_some`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3813`): looking up a
    key in an association list with distinct keys returns the value paired with
    it.  CakeML states this for `lookup`/`fromAList`; the list-backed Flapjack
    analogue is `List.lookup` on the association list itself. -/
theorem list_lookup_of_mem_of_nodup [BEq α] [LawfulBEq α] {entries : List (α × β)}
    {key : α} {value : β}
    (hnodup : (entries.map Prod.fst).Nodup) (hmem : (key, value) ∈ entries) :
    entries.lookup key = some value := by
  induction entries with
  | nil => simp at hmem
  | cons entry entries ih =>
      obtain ⟨headKey, headValue⟩ := entry
      simp only [List.map_cons, List.nodup_cons] at hnodup
      obtain ⟨hhead, htail⟩ := hnodup
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rw [List.lookup_cons]
      split
      · rename_i hk
        rcases hmem with hpair | hmem
        · obtain ⟨_, hvalue⟩ := hpair
          subst hvalue
          rfl
        · exfalso
          have hkey : key = headKey := beq_iff_eq.mp hk
          have hmemKey : key ∈ entries.map Prod.fst :=
            List.mem_map.mpr ⟨(key, value), hmem, rfl⟩
          rw [← hkey] at hhead
          exact hhead hmemKey
      · rename_i hk
        rcases hmem with hpair | hmem
        · exfalso
          obtain ⟨hkey, _⟩ := hpair
          have htrue : (key == headKey) = true := by rw [hkey]; exact beq_iff_eq.mpr rfl
          rw [htrue] at hk
          exact Bool.false_ne_true hk.symm
        · exact ih htail hmem

/-- Counterpart of Cake's `alookup_el_pair_eq_el`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3921`): in an
    association list with distinct keys, the entry at an index whose key is
    `key` is exactly the pair recorded by `lookup key`. -/
theorem getElem_eq_of_lookup_eq [BEq α] [LawfulBEq α] {entries : List (α × β)}
    {key : α} {value : β} {n : Nat}
    (hdistinct : (entries.map Prod.fst).Nodup) (hn : n < entries.length)
    (hhead : (entries[n]'hn).1 = key)
    (hlookup : entries.lookup key = some value) :
    entries[n]'hn = (key, value) := by
  obtain ⟨l₁, l₂, hentries, _⟩ := (List.lookup_eq_some_iff).mp hlookup
  have hmem : (key, value) ∈ entries := by
    rw [hentries]
    exact List.mem_append_right l₁ (by simp)
  obtain ⟨m, hm, hmval⟩ := List.getElem_of_mem hmem
  have hnx : entries[n]'hn = (key, (entries[n]'hn).2) := by
    rw [← hhead]
  have hnm : n = m := getElem_fst_inj entries n m hdistinct hn hm hnx hmval
  subst hnm
  exact hmval

/-- Cake's `map_map2_fst_lemma`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:118`): the first
    components of a pointwise pairing are the prefix of the first list cut at
    the shorter length. -/
theorem zipWith_pair_fst {α β : Type} (xs : List α) (ys : List β) :
    (List.zipWith (fun x y => (x, y)) xs ys).map Prod.fst =
      xs.take (min xs.length ys.length) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys =>
          simp only [List.zipWith_cons_cons, List.map_cons, List.length_cons]
          rw [ih]
          have hk : min (xs.length + 1) (ys.length + 1) =
              min xs.length ys.length + 1 := by omega
          rw [hk, List.take_succ_cons]

/-! Counterpart of Cake's `all_distinct_with_shape_distinct`
    (`cakeml/pancake/semantics/panPropsScript.sml:357`): two distinct members of
    the flat-value split are disjoint.  Cake's extra hypotheses `x <> []` and
    `y <> []` are implied here, because membership of a list in
    `withShape shapes values` already forces the component to be nonempty. -/
theorem listDisjoint_of_withShape_mem (shapes : List Shape) (values : List α)
    (x y : List α) (hdistinct : values.Nodup)
    (hvalues : values.length = Shape.shapeSize (.comb shapes))
    (hx : x ∈ withShape shapes values) (hy : y ∈ withShape shapes values)
    (hne : x ≠ y) :
    ListDisjoint x y := by
  obtain ⟨n, hn, hnx⟩ := List.getElem_of_mem hx
  obtain ⟨n', hn', hn'y⟩ := List.getElem_of_mem hy
  have hnlen : n < shapes.length := by rw [withShape_length] at hn; exact hn
  have hn'len : n' < shapes.length := by rw [withShape_length] at hn'; exact hn'
  by_cases heq : n = n'
  · subst n'
    exact absurd (hnx.symm.trans hn'y) hne
  · rcases Nat.lt_or_gt_of_ne heq with hlt | hlt
    · rw [← hnx, ← hn'y]
      exact listDisjoint_withShape_getElem shapes values n n' hdistinct hnlen hn'len
        heq hvalues
    · rw [← hnx, ← hn'y]
      intro value hleft hright
      exact listDisjoint_withShape_getElem shapes values n' n hdistinct hn'len hnlen
        (Ne.symm heq) hvalues value hright hleft

theorem shapeSize_drop_head_le (shapes : List Shape) (n : Nat)
    (hn : n < shapes.length) :
    Shape.shapeSize (shapes[n]'hn) ≤
      Shape.shapeSize (.comb (shapes.drop n)) := by
  rw [List.drop_eq_getElem_cons (l := shapes) hn, shapeSize_comb_cons]
  omega

/-! Counterpart of Cake's `el_el_with_shape`
    (`cakeml/pancake/semantics/panPropsScript.sml:568`): the `n'`-th element of
    the `n`-th group produced by `with_shape` is the
    `n' + size_of_shape (Comb (TAKE n shs))`-th element of the flat list.  Cake's
    `EVERY is_wf_shape_nil shs` hypothesis is not needed here because
    `Shape.shapeSize` is total. -/
theorem withShape_getElem_getElem (shapes : List Shape) (values : List α)
    (n n' : Nat)
    (hvalues : values.length = Shape.shapeSize (.comb shapes))
    (hn : n < shapes.length)
    (hn' : n' < Shape.shapeSize (shapes[n]'hn))
    (hbound : n' <
      ((withShape shapes values)[n]'(by rw [withShape_length]; exact hn)).length) :
    ((withShape shapes values)[n]'(by rw [withShape_length]; exact hn))[n']'hbound =
      values[(Shape.shapeSize (.comb (shapes.take n))) + n']'(by
        have hdrop : Shape.shapeSize (.comb (shapes.take n)) +
              Shape.shapeSize (.comb (shapes.drop n)) =
            Shape.shapeSize (.comb shapes) := by
          rw [← shapeSize_comb_append, List.take_append_drop n shapes]
        rw [hvalues, ← hdrop]
        have hle := shapeSize_drop_head_le shapes n hn
        omega) := by
  simp only [withShape_getElem_eq_take_drop shapes values n hvalues hn,
    List.getElem_take, List.getElem_drop]

/-! Counterpart of the length obligation inside Cake's
    `list_rel_flatten_with_shape_length`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:549`): the `n`-th group
    produced by `with_shape` has exactly `size_of_shape (EL n sh)` elements. -/
theorem withShape_getElem_length (shapes : List Shape) (values : List α) (n : Nat)
    (hvalues : values.length = Shape.shapeSize (.comb shapes))
    (hn : n < shapes.length) :
    ((withShape shapes values)[n]'(by rw [withShape_length]; exact hn)).length =
      Shape.shapeSize (shapes[n]'hn) := by
  rw [withShape_getElem_eq_take_drop shapes values n hvalues hn, List.length_take]
  have hdrop : (values.drop (Shape.shapeSize (.comb (shapes.take n)))).length =
      Shape.shapeSize (.comb (shapes.drop n)) := by
    have h : Shape.shapeSize (.comb shapes) =
        Shape.shapeSize (.comb (shapes.take n)) +
          Shape.shapeSize (.comb (shapes.drop n)) := by
      simpa [List.take_append_drop] using
        shapeSize_comb_append (shapes.take n) (shapes.drop n)
    rw [List.length_drop, hvalues, h, Nat.add_sub_cancel_left]
  rw [hdrop]
  exact Nat.min_eq_left (shapeSize_drop_head_le shapes n hn)

/-- Executable mirror of HOL `panLang$var_exp` (`panLangScript.sml:253-270`):
    collect local-variable occurrences in left-to-right order, retaining
    duplicates. FLAPJACK-SPECIFIC (not an exact HOL port): HOL takes its
    word-indexed `exp` (including `mlstring` names and HOL `shape`) and returns
    `mlstring list`; this function takes generic `Exp α` with String-backed
    names/fields and monomorphic `Shape`, and returns `List VarName` with
    `VarName := String`. The 17 constructor clauses agree structurally, and the
    kernel bridge `Flapjack.Pancake.PanLang.varExpHOL_expToHOL` in `PanLang/Exp.lean`
    proves this helper is the reviewed HOL `var_exp` under the checked
    `expToHOL` name codec: `varExpHOL (expToHOL e) = (expLocalVars e).map ofString`
    for width-indexed expressions. This declaration stays untagged because its
    carrier is the broader generic `Exp α`; the exact-port declaration is the
    tagged `varExpHOL` over `ExpHOL width`. The executable compiler's call sites
    (`globalCompileExp`/`globalCompileProg`) are generic in `α` with no `width`,
    so the width-indexed `expToHOL` codec is not threaded through them;
    production routing is tracked on bead `flapjack-4ac.1.38.1`. The faithful
    MlString/ShapeHOL carrier work is tracked by `flapjack-pxn.18.3.5.8`. -/
def expLocalVars : Exp α → List VarName
  | .const _ => []
  | .var .local name => [name]
  | .var .global _ => []
  | .rStruct fields => expLocalVarsList fields
  | .rField _ value => expLocalVars value
  | .nStruct _ fields => expLocalVarsFieldList fields
  | .nField _ value => expLocalVars value
  | .load _ address => expLocalVars address
  | .load32 address => expLocalVars address
  | .loadByte address => expLocalVars address
  | .op _ args => expLocalVarsList args
  | .panOp _ args => expLocalVarsList args
  | .cmp _ left right => expLocalVars left ++ expLocalVars right
  | .shift _ left right => expLocalVars left ++ expLocalVars right
  | .baseAddr => []
  | .topAddr => []
  | .bytesInWord => []

termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  expLocalVarsList (expressions : List (Exp α)) : List VarName :=
    match expressions with
    | [] => []
    | expression :: expressions => expLocalVars expression ++ expLocalVarsList expressions
  termination_by sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  expLocalVarsFieldList (fields : List (FieldName × Exp α)) : List VarName :=
    match fields with
    | [] => []
    | (_, expression) :: fields => expLocalVars expression ++ expLocalVarsFieldList fields
  termination_by sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

/- FLAPJACK-SPECIFIC (not an exact HOL port): clause-structured mirror of HOL
    `panLang$free_var_ids` (`panLangScript.sml:347`). The expression helper
    mirrors HOL `var_exp`, and the `Dec` filter uses lawful String equality.
    The `@[hol]` tag is WITHDRAWN for more than a name representation change:
    HOL's input is a word-indexed `prog` with `mlstring` identifiers and its
    result is `mlstring list`; this production function instead quantifies over
    generic `Prog α`/`Exp α` with String-backed names and returns `List String`.
    The `names_as_string` qualifier cannot account for the generic expression
    and program carriers. Exact-carrier replacement is tracked by
    `flapjack-pxn.18.3.5.8`; this analogue remains useful to the executed
    compiler and is deliberately untagged. -/
def freeVarIds : Prog α → List VarName
  | .dec name _ value body =>
      expLocalVars value ++ (freeVarIds body).filter (fun vname => vname != name)
  | .seq first second => freeVarIds first ++ freeVarIds second
  | .ite condition thenBranch elseBranch =>
      expLocalVars condition ++ freeVarIds thenBranch ++ freeVarIds elseBranch
  | .while condition body => expLocalVars condition ++ freeVarIds body
  | .assign kind name value =>
      (if kind == .local then [name] else []) ++ expLocalVars value
  | .primitive name _ arguments => name :: arguments.flatMap expLocalVars
  | .store address value => expLocalVars address ++ expLocalVars value
  | .store32 address value => expLocalVars address ++ expLocalVars value
  | .storeByte address value => expLocalVars address ++ expLocalVars value
  | .raise _ value => expLocalVars value
  | .return value => expLocalVars value
  | .extCall _ configuration configurationLength array arrayLength =>
      expLocalVars configuration ++ expLocalVars configurationLength ++
        expLocalVars array ++ expLocalVars arrayLength
  | .shMemLoad _ kind name address =>
      (if kind == .local then [name] else []) ++ expLocalVars address
  | .shMemStore _ address value => expLocalVars address ++ expLocalVars value
  | .call (some (none, some (_, exceptionName, handler))) _ arguments =>
      exceptionName :: freeVarIds handler ++ arguments.flatMap expLocalVars
  | .call (some (some (kind, name), some (_, exceptionName, handler))) _ arguments =>
      (if kind == .local then [name] else []) ++
        exceptionName :: freeVarIds handler ++ arguments.flatMap expLocalVars
  | .call (some (some (kind, name), none)) _ arguments =>
      (if kind == .local then [name] else []) ++ arguments.flatMap expLocalVars
  | .call (some (none, none)) _ arguments => arguments.flatMap expLocalVars
  | .call none _ arguments => arguments.flatMap expLocalVars
  | .decCall name _ _ arguments body =>
      name :: freeVarIds body ++ arguments.flatMap expLocalVars
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def expGlobalVars : Exp α → List VarName
  | .const _ => []
  | .var .local _ => []
  | .var .global name => [name]
  | .rStruct fields => expGlobalVarsList fields
  | .rField _ value => expGlobalVars value
  | .nStruct _ fields => expGlobalVarsFieldList fields
  | .nField _ value => expGlobalVars value
  | .load _ address => expGlobalVars address
  | .load32 address => expGlobalVars address
  | .loadByte address => expGlobalVars address
  | .op _ args => expGlobalVarsList args
  | .panOp _ args => expGlobalVarsList args
  | .cmp _ left right => expGlobalVars left ++ expGlobalVars right
  | .shift _ left right => expGlobalVars left ++ expGlobalVars right
  | .baseAddr => []
  | .topAddr => []
  | .bytesInWord => []

termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  expGlobalVarsList (expressions : List (Exp α)) : List VarName :=
    match expressions with
    | [] => []
    | expression :: expressions => expGlobalVars expression ++ expGlobalVarsList expressions
  termination_by sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  expGlobalVarsFieldList (fields : List (FieldName × Exp α)) : List VarName :=
    match fields with
    | [] => []
    | (_, expression) :: fields => expGlobalVars expression ++ expGlobalVarsFieldList fields
  termination_by sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

end Flapjack
