import Flapjack.Pancake.PanLang
import Flapjack.Pancake.PanLang.Shape
import Flapjack.Basis.Pure.MlString

/-!
# Exact `panLang$exp` over the faithful `mlstring` carrier

HOL `panLang$exp` (`cakeml/pancake/panLangScript.sml:53-69`) is indexed by the
target word type in its `Const` case:

```
exp = Const ('a word) | Var varkind varname | RStruct (exp list) |
      RField index exp | NStruct stcname ((fldname # exp) list) |
      NField fldname exp | Load shape exp | Load32 exp | LoadByte exp |
      Op binop (exp list) | Panop panop (exp list) | Cmp cmp exp exp |
      Shift shift exp exp | BaseAddr | TopAddr | BytesInWord
```

with `varname`/`stcname`/`fldname = mlstring` (lines 23-31) and `index = num`.
The executable `Flapjack.Exp α` (`Flapjack/Pancake/PanLang.lean`) is generic in
the word type and uses Lean `String` identifiers, so it is not the exact HOL
datatype and stays untagged.

`ExpHOL width` below is the exact counterpart: `const : BitVec width`, the
`mlstring`-named identifier fields, and `load : ShapeHOL` (the exact shape
carrier of `Flapjack/Pancake/PanLang/Shape.lean`).

`expToHOL`/`expOfHOL` are the kernel-checked codec to production
`Flapjack.Exp (BitVec width)`.  `expToHOL_expOfHOL` round trips `ExpHOL` exactly;
the reverse `expOfHOL_expToHOL` needs the byte-range predicate `ExpByteRanged`
on production identifiers, the range HOL `char` represents.  Direct HOL oracle
rows are recorded in `scripts/hol-probes/pan_lang_exp_probe.out` and reproduced
by `Flapjack/Test/PanLangExpHOLParity.lean`.
-/

namespace Flapjack.Pancake.PanLang

open Flapjack.Basis.Pure.MlString

/-- Exact port of HOL `panLang$exp` (`cakeml/pancake/panLangScript.sml:53-69`).

    The `const` field is the width-indexed `BitVec width` (HOL `'a word`), the
    identifier fields are the faithful `mlstring` carrier `MlS`, and `load`
    carries the exact `ShapeHOL`.  Constructor arities, fields, and ordering
    match the HOL datatype. -/
@[hol "cakeml/pancake/panLangScript.sml" "exp"]
inductive ExpHOL (width : Nat) [NeZero width] where
  | const (value : BitVec width)
  | var (kind : VarKind) (name : MlS)
  | rstruct (fields : List (ExpHOL width))
  | rfield (index : Nat) (value : ExpHOL width)
  | nstruct (name : MlS) (fields : List (MlS × ExpHOL width))
  | nfield (name : MlS) (value : ExpHOL width)
  | load (shape : ShapeHOL) (address : ExpHOL width)
  | load32 (address : ExpHOL width)
  | loadByte (address : ExpHOL width)
  | op (operator : BinOp) (args : List (ExpHOL width))
  | panop (operator : PanOp) (args : List (ExpHOL width))
  | cmp (operator : Cmp) (left right : ExpHOL width)
  | shift (operator : Shift) (left right : ExpHOL width)
  | baseAddr
  | topAddr
  | bytesInWord
  deriving Repr

mutual
  /-- Production expressions all of whose identifiers are byte-ranged (every
      character code `< 256`), hence exactly representable as `mlstring`.  The
      `load` case also requires its shape to be byte-ranged. -/
  def ExpByteRanged {width : Nat} : Flapjack.Exp (BitVec width) → Prop
    | .const _ => True
    | .var _ name => ∀ c ∈ name.toList, c.toNat < 256
    | .rStruct fields => ListExpByteRanged fields
    | .rField _ value => ExpByteRanged value
    | .nStruct name fields =>
        (∀ c ∈ name.toList, c.toNat < 256) ∧ ListFieldByteRanged fields
    | .nField name value =>
        (∀ c ∈ name.toList, c.toNat < 256) ∧ ExpByteRanged value
    | .load shape address => ShapeByteRanged shape ∧ ExpByteRanged address
    | .load32 address => ExpByteRanged address
    | .loadByte address => ExpByteRanged address
    | .op _ args => ListExpByteRanged args
    | .panOp _ args => ListExpByteRanged args
    | .cmp _ left right => ExpByteRanged left ∧ ExpByteRanged right
    | .shift _ left right => ExpByteRanged left ∧ ExpByteRanged right
    | .baseAddr => True
    | .topAddr => True
    | .bytesInWord => True
  def ListExpByteRanged {width : Nat} :
      List (Flapjack.Exp (BitVec width)) → Prop
    | [] => True
    | e :: es => ExpByteRanged e ∧ ListExpByteRanged es
  def ListFieldByteRanged {width : Nat} :
      List (String × Flapjack.Exp (BitVec width)) → Prop
    | [] => True
    | p :: ps =>
        (∀ c ∈ p.1.toList, c.toNat < 256) ∧ ExpByteRanged p.2 ∧ ListFieldByteRanged ps
end

/-- Encode a production expression into the exact HOL-shaped carrier.  Names
    use the total `ofString` and shapes use `shapeToHOL`. -/
def expToHOL {width : Nat} [NeZero width] :
    Flapjack.Exp (BitVec width) → ExpHOL width
  | .const value => .const value
  | .var kind name => .var kind (ofString name)
  | .rStruct fields => .rstruct (fields.map expToHOL)
  | .rField index value => .rfield index (expToHOL value)
  | .nStruct name fields =>
      .nstruct (ofString name) (fields.map (fun p => (ofString p.1, expToHOL p.2)))
  | .nField name value => .nfield (ofString name) (expToHOL value)
  | .load shape address => .load (shapeToHOL shape) (expToHOL address)
  | .load32 address => .load32 (expToHOL address)
  | .loadByte address => .loadByte (expToHOL address)
  | .op operator args => .op operator (args.map expToHOL)
  | .panOp operator args => .panop operator (args.map expToHOL)
  | .cmp operator left right => .cmp operator (expToHOL left) (expToHOL right)
  | .shift operator left right => .shift operator (expToHOL left) (expToHOL right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr
  | .bytesInWord => .bytesInWord
termination_by e => sizeOf e
decreasing_by
  simp_wf
  all_goals
    first
      | decreasing_trivial
      | (rename_i _name h
         simp only [Exp.nStruct.sizeOf_spec]
         have hmem := List.sizeOf_lt_of_mem h
         have hps : sizeOf p.snd < sizeOf p := by cases p; simp +arith
         omega)

/-- Decode the exact carrier back to a production expression. -/
def expOfHOL {width : Nat} [NeZero width] :
    ExpHOL width → Flapjack.Exp (BitVec width)
  | .const value => .const value
  | .var kind name => .var kind (toStringOfBytes name)
  | .rstruct fields => .rStruct (fields.map expOfHOL)
  | .rfield index value => .rField index (expOfHOL value)
  | .nstruct name fields =>
      .nStruct (toStringOfBytes name)
        (fields.map (fun p => (toStringOfBytes p.1, expOfHOL p.2)))
  | .nfield name value => .nField (toStringOfBytes name) (expOfHOL value)
  | .load shape address => .load (shapeOfHOL shape) (expOfHOL address)
  | .load32 address => .load32 (expOfHOL address)
  | .loadByte address => .loadByte (expOfHOL address)
  | .op operator args => .op operator (args.map expOfHOL)
  | .panop operator args => .panOp operator (args.map expOfHOL)
  | .cmp operator left right => .cmp operator (expOfHOL left) (expOfHOL right)
  | .shift operator left right => .shift operator (expOfHOL left) (expOfHOL right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr
  | .bytesInWord => .bytesInWord
termination_by e => sizeOf e
decreasing_by
  simp_wf
  all_goals
    first
      | decreasing_trivial
      | (rename_i _name h
         simp only [ExpHOL.nstruct.sizeOf_spec]
         have hmem := List.sizeOf_lt_of_mem h
         have hps : sizeOf p.snd < sizeOf p := by cases p; simp +arith
         omega)

/-- `ExpHOL -> Exp -> ExpHOL` round trips exactly. -/
@[simp] theorem expToHOL_expOfHOL {width : Nat} [NeZero width] :
    (e : ExpHOL width) → expToHOL (expOfHOL e) = e :=
  ExpHOL.rec
    (motive_1 := fun e => expToHOL (expOfHOL e) = e)
    (motive_2 := fun l => (l.map expOfHOL).map expToHOL = l)
    (motive_3 := fun l =>
      (l.map (fun p => (toStringOfBytes p.1, expOfHOL p.2))).map
        (fun p => (ofString p.1, expToHOL p.2)) = l)
    (motive_4 := fun p => (ofString (toStringOfBytes p.1), expToHOL (expOfHOL p.2)) = p)
    (fun _value => by simp only [expToHOL, expOfHOL])
    (fun _kind name => by
      simp only [expToHOL, expOfHOL,
        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes])
    (fun fields ih => by
      simp only [expToHOL, expOfHOL]
      rw [ih])
    (fun _index _value ih => by
      simp only [expToHOL, expOfHOL]
      rw [ih])
    (fun name fields ih => by
      simp only [expToHOL, expOfHOL,
        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
      rw [ih])
    (fun name _value ih => by
      simp only [expToHOL, expOfHOL,
        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
      rw [ih])
    (fun shape address ih => by
      simp only [expToHOL, expOfHOL, shapeToHOL_shapeOfHOL]
      rw [ih])
    (fun _address ih => by
      simp only [expToHOL, expOfHOL]
      rw [ih])
    (fun _address ih => by
      simp only [expToHOL, expOfHOL]
      rw [ih])
    (fun operator args ih => by
      simp only [expToHOL, expOfHOL]
      rw [ih])
    (fun operator args ih => by
      simp only [expToHOL, expOfHOL]
      rw [ih])
    (fun operator left right ihl ihr => by
      simp only [expToHOL, expOfHOL]
      rw [ihl, ihr])
    (fun operator left right ihl ihr => by
      simp only [expToHOL, expOfHOL]
      rw [ihl, ihr])
    (by simp only [expToHOL, expOfHOL])
    (by simp only [expToHOL, expOfHOL])
    (by simp only [expToHOL, expOfHOL])
    rfl
    (fun _head _tail ih1 ih2 => by simp [ih1, ih2])
    rfl
    (fun head _tail ih4 ih3 => by simp [ih4, ih3])
    (fun fst snd ih => by
      simp [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes, ih])
/-- `Exp -> ExpHOL -> Exp` round trips exactly on byte-ranged expressions. -/
@[simp] theorem expOfHOL_expToHOL {width : Nat} [NeZero width] :
    (e : Flapjack.Exp (BitVec width)) → ExpByteRanged e →
      expOfHOL (expToHOL e) = e :=
  Flapjack.Exp.rec
    (motive_1 := fun e => ExpByteRanged e → expOfHOL (expToHOL e) = e)
    (motive_2 := fun l =>
      ListExpByteRanged l → (l.map (expOfHOL ∘ expToHOL)) = l)
    (motive_3 := fun l =>
      ListFieldByteRanged l →
        (l.map ((fun p => (toStringOfBytes p.1, expOfHOL p.2)) ∘
          fun p => (ofString p.1, expToHOL p.2))) = l)
    (motive_4 := fun p =>
      ((∀ c ∈ p.1.toList, c.toNat < 256) ∧ ExpByteRanged p.2) →
        (toStringOfBytes (ofString p.1), expOfHOL (expToHOL p.2)) = p)
    (fun _value => by intro _; simp only [expToHOL, expOfHOL])
    (fun _kind name => by
      intro h
      simp only [expToHOL, expOfHOL,
        Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name h])
    (fun fields ih => by
      intro h
      simp only [expToHOL, expOfHOL, List.map_map]
      rw [ih h])
    (fun _index _value ih => by
      intro h
      simp only [expToHOL, expOfHOL]
      rw [ih h])
    (fun name fields ih => by
      intro h
      obtain ⟨hname, hfields⟩ := h
      simp only [expToHOL, expOfHOL, List.map_map,
        Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname]
      rw [ih hfields])
    (fun name _value ih => by
      intro h
      obtain ⟨hname, hvalue⟩ := h
      simp only [expToHOL, expOfHOL,
        Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname]
      rw [ih hvalue])
    (fun shape address ih => by
      intro h
      obtain ⟨hshape, haddress⟩ := h
      simp only [expToHOL, expOfHOL, shapeOfHOL_shapeToHOL shape hshape]
      rw [ih haddress])
    (fun address ih => by
      intro h
      simp only [expToHOL, expOfHOL]
      rw [ih h])
    (fun address ih => by
      intro h
      simp only [expToHOL, expOfHOL]
      rw [ih h])
    (fun _operator args ih => by
      intro h
      simp only [expToHOL, expOfHOL, List.map_map]
      rw [ih h])
    (fun _operator args ih => by
      intro h
      simp only [expToHOL, expOfHOL, List.map_map]
      rw [ih h])
    (fun _operator left right ihl ihr => by
      intro h
      obtain ⟨hl, hr⟩ := h
      simp only [expToHOL, expOfHOL]
      rw [ihl hl, ihr hr])
    (fun _operator left right ihl ihr => by
      intro h
      obtain ⟨hl, hr⟩ := h
      simp only [expToHOL, expOfHOL]
      rw [ihl hl, ihr hr])
    (by intro _; simp only [expToHOL, expOfHOL])
    (by intro _; simp only [expToHOL, expOfHOL])
    (by intro _; simp only [expToHOL, expOfHOL])
    (by intro _; rfl)
    (fun head _tail ih1 ih2 => by
      intro h
      obtain ⟨hh, ht⟩ := h
      simp only [List.map_cons, Function.comp_apply]
      rw [ih1 hh, ih2 ht])
    (by intro _; rfl)
    (fun head _tail ih4 ih3 => by
      intro h
      obtain ⟨hA, hB, hC⟩ := h
      simp only [List.map_cons, Function.comp_apply]
      rw [ih4 ⟨hA, hB⟩, ih3 hC])
    (fun fst snd ih => by
      intro h
      obtain ⟨hf, hs⟩ := h
      simp only [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes fst hf,
        ih hs])

/-! ### Exact `panLang$var_exp` -/

/-- Exact port of HOL `panLang$var_exp` (`cakeml/pancake/panLangScript.sml:253-276`):
collects the local variable names of an expression in source order, returning
`mlstring` names.  `Var Local v` contributes `[v]`, `Var Global` nothing, and
aggregating constructs concatenate the results of their sub-expressions
(`FLAT (MAP var_exp …)` for `RStruct`/`NStruct`/`Op`/`Panop`, `++` for
`Cmp`/`Shift`).  The production `expLocalVars` uses Lean `String` and is
untagged. -/
@[hol "cakeml/pancake/panLangScript.sml" "var_exp_def"]
def varExpHOL {width : Nat} [NeZero width] : ExpHOL width → List MlS
  | .const _ => []
  | .var .local name => [name]
  | .var .global _ => []
  | .rstruct fields => (fields.map varExpHOL).flatten
  | .rfield _ value => varExpHOL value
  | .nstruct _ fields => (fields.map (fun pair => varExpHOL pair.2)).flatten
  | .nfield _ value => varExpHOL value
  | .load _ address => varExpHOL address
  | .load32 address => varExpHOL address
  | .loadByte address => varExpHOL address
  | .op _ args => (args.map varExpHOL).flatten
  | .panop _ args => (args.map varExpHOL).flatten
  | .cmp _ left right => varExpHOL left ++ varExpHOL right
  | .shift _ left right => varExpHOL left ++ varExpHOL right
  | .baseAddr => []
  | .topAddr => []
  | .bytesInWord => []
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (rename_i mem
       have hlt := List.sizeOf_lt_of_mem mem
       have hsnd : sizeOf pair.snd < sizeOf pair := by cases pair; simp +arith
       omega)
    | (rename_i elem mem
       have hlt := List.sizeOf_lt_of_mem mem
       omega)

end Flapjack.Pancake.PanLang
