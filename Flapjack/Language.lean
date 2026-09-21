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

/-! Exact source counterpart of Pancake's `shape_to_str_def`. -/
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

inductive OpSize where
  | op8
  | opW
  | op32
  | op16
  deriving DecidableEq, Repr

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

structure FunDecl (α : Type u) where
  name : FunName
  inline : Bool
  exported : Bool
  params : List (VarName × Shape)
  body : Prog α
  returnShape : Shape
  deriving Repr

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
    direct Lean counterpart of `panLang$with_shape`; values left over after
    the requested shapes are intentionally ignored, and short inputs are
    handled by `List.take`/`List.drop` just like CakeML's `TAKE`/`DROP`. -/
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

/-- Cake's `DISJOINT (set left) (set right)` predicate, stated directly on
    lists because `List` membership already expresses the element relation. -/
def ListDisjoint (left right : List α) : Prop :=
  ∀ value, value ∈ left → value ∈ right → False

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

/-! Direct source-shaped counterpart of `panLang$free_var_ids`.  The
    expression helper is the existing `expLocalVars`, which mirrors the
    source `var_exp` distinction between local and global variables. -/
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
