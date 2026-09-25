import Flapjack.HolRef
import Flapjack.Pancake.PanLang

/-!
The Crepe intermediate language.

Crepe is Flapjack after structured locals have been flattened into word-sized
locals. This mirrors `cakeml/pancake/crepLangScript.sml`; target-specific word
operations remain abstract in the polymorphic value type.
-/

namespace Flapjack

universe u

inductive CrepOp where
  | mul
  deriving DecidableEq, Repr

inductive CrepExp (α : Type u) where
  | const (value : α)
  | var (name : Nat)
  | load (address : CrepExp α)
  | load32 (address : CrepExp α)
  | loadByte (address : CrepExp α)
  | loadGlob (address : BitVec 5)
  | op (operator : BinOp) (args : List (CrepExp α))
  | crepOp (operator : CrepOp) (args : List (CrepExp α))
  | cmp (operator : Cmp) (left right : CrepExp α)
  | shift (operator : Shift) (left right : CrepExp α)
  | baseAddr
  | topAddr
  deriving BEq, Repr

inductive CrepMemOp where
  | load
  | load8
  | load16
  | load32
  | store
  | store8
  | store16
  | store32
  deriving DecidableEq, Repr

inductive CrepProg (α : Type u) where
  | skip
  | dec (name : Nat) (value : CrepExp α) (body : CrepProg α)
  | assign (name : Nat) (value : CrepExp α)
  | primitive (names : List Nat) (operator : PrimOp) (args : List Nat)
  | store (address value : CrepExp α)
  | store32 (address value : CrepExp α)
  | storeByte (address value : CrepExp α)
  | storeGlob (address : BitVec 5) (value : CrepExp α)
  | seq (first second : CrepProg α)
  | ite (condition : CrepExp α) (thenBranch elseBranch : CrepProg α)
  | while (condition : CrepExp α) (body : CrepProg α)
  | break (label : Nat)
  | continue (label : Nat)
  | call (returnInfo : Option (List Nat × Option (α × CrepProg α)))
      (name : FunName) (args : List (CrepExp α))
  | extCall (function : FunName) (configuration configurationLength array arrayLength : Nat)
  | raise (exception : α)
  | return (values : List (CrepExp α))
  | shMem (operator : CrepMemOp) (name : Nat) (address : CrepExp α)
  | tick
  deriving Repr

/-! Faithful port of `crepLang$assigned_free_vars` from
    `cakeml/pancake/crepLangScript.sml:149-162`. -/
/- FLAPJACK-SPECIFIC (not an exact HOL port): this helper is generic over
    `CrepProg α`/`CrepExp α`, while HOL `crepLang$prog`/`exp` are indexed by
    the word length (`'a word`). The exact width-indexed tag is on the
    `...W` wrapper below (over `BitVec width`). -/
def crepAssignedFreeVars : CrepProg α → List Nat
  | .skip => []
  | .dec name _ body =>
      (crepAssignedFreeVars body).filter (fun candidate => candidate != name)
  | .assign name _ => [name]
  | .primitive names _ _ => names
  | .seq first second => crepAssignedFreeVars first ++ crepAssignedFreeVars second
  | .ite _ thenBranch elseBranch =>
      crepAssignedFreeVars thenBranch ++ crepAssignedFreeVars elseBranch
  | .while _ body => crepAssignedFreeVars body
  | .call (some (returns, some (_, handler))) _ _ =>
      returns ++ crepAssignedFreeVars handler
  | .call (some (returns, none)) _ _ => returns
  | .shMem _ name _ => [name]
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! Faithful port of `crepLang$assigned_vars` from
    `cakeml/pancake/crepLangScript.sml:164-176`. -/
/- FLAPJACK-SPECIFIC (not an exact HOL port): this helper is generic over
    `CrepProg α`/`CrepExp α`, while HOL `crepLang$prog`/`exp` are indexed by
    the word length (`'a word`). The exact width-indexed tag is on the
    `...W` wrapper below (over `BitVec width`). -/
def crepAssignedVars : CrepProg α → List Nat
  | .skip => []
  | .dec name _ body => name :: crepAssignedVars body
  | .assign name _ => [name]
  | .primitive names _ _ => names
  | .seq first second => crepAssignedVars first ++ crepAssignedVars second
  | .ite _ thenBranch elseBranch =>
      crepAssignedVars thenBranch ++ crepAssignedVars elseBranch
  | .while _ body => crepAssignedVars body
  | .call (some (returns, some (_, handler))) _ _ =>
      returns ++ crepAssignedVars handler
  | .call (some (returns, none)) _ _ => returns
  | .shMem _ name _ => [name]
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/- FLAPJACK-SPECIFIC (not an exact HOL port): this helper is generic over
    `CrepProg α`/`CrepExp α`, while HOL `crepLang$prog`/`exp` are indexed by
    the word length (`'a word`). The exact width-indexed tag is on the
    `...W` wrapper below (over `BitVec width`). -/
def crepExpVars : CrepExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .load address | .load32 address | .loadByte address => crepExpVars address
  | .loadGlob _ => []
  | .op _ expressions | .crepOp _ expressions => crepExpVarsList expressions
  | .cmp _ left right | .shift _ left right => crepExpVars left ++ crepExpVars right
  | .baseAddr | .topAddr => []
termination_by expression => sizeOf expression
where
  crepExpVarsList : List (CrepExp α) → List Nat
    | [] => []
    | expression :: expressions => crepExpVars expression ++ crepExpVarsList expressions
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

/-! Faithful port of `crepLang$exps` from
    `cakeml/pancake/crepLangScript.sml:193-207`.

    The result preserves expression nodes while recursively flattening the
    expression lists of `Op` and `Crepop`, matching HOL's `FLAT (MAP exps)`. -/
/- FLAPJACK-SPECIFIC (not an exact HOL port): this helper is generic over
    `CrepProg α`/`CrepExp α`, while HOL `crepLang$prog`/`exp` are indexed by
    the word length (`'a word`). The exact width-indexed tag is on the
    `...W` wrapper below (over `BitVec width`). -/
def crepExps : CrepExp α → List (CrepExp α)
  | expression@(.const _) => [expression]
  | expression@(.var _) => [expression]
  | .load address | .load32 address | .loadByte address => crepExps address
  | expression@(.loadGlob _) => [expression]
  | .op _ expressions | .crepOp _ expressions => crepExpsList expressions
  | .cmp _ left right | .shift _ left right => crepExps left ++ crepExps right
  | expression@(.baseAddr) | expression@(.topAddr) => [expression]
termination_by expression => sizeOf expression
where
  crepExpsList : List (CrepExp α) → List (CrepExp α)
    | [] => []
    | expression :: expressions => crepExps expression ++ crepExpsList expressions
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def distinctLists (left right : List Nat) : Bool :=
  left.all (fun name => !right.contains name)

@[simp] theorem crepExpVars_const (value : α) :
    crepExpVars (.const value) = [] := by
  simp [crepExpVars]

theorem crepExpVars_var {α : Type} (name : Nat) :
    crepExpVars (α := α) (.var name) = [name] := by
  simp [crepExpVars]

/-- The fixed machine byte width `byte$bytes_in_word` that Cake's
    `crepLang$load_shape` uses for its stride
    (`cakeml/pancake/crepLangScript.sml:82-86`).  Cake derives it from the word
    type as `n2w (dimindex (:'a) DIV 8)`; Flapjack's value type is abstract, so a
    target supplies the same fixed constant through an instance, exactly as
    `[OfNat α 1]` supplies the fixed increment of `load_globals`. -/
class CrepBytesInWord (α : Type u) where
  bytesInWord : α

/-! `Nat` is used by source-parity fixtures as an unbounded stand-in for the
    64-bit target word; its fixed target stride is eight bytes. -/
instance natCrepBytesInWord : CrepBytesInWord Nat where
  bytesInWord := 8

/-- The RISC-V style instance: a `BitVec w` word has `w / 8` bytes. -/
instance bitVecCrepBytesInWord (w : Nat) : CrepBytesInWord (BitVec w) where
  bytesInWord := BitVec.ofNat w (w / 8)

/-- General-stride loading used by the Flapjack pipeline.  Cake's
    `crepLang$load_shape` fixes the stride to `byte$bytes_in_word`; the pipeline
    passes the stride from its compile context, so this remains Flapjack-specific
    infrastructure.  The faithful fixed-width port is `loadShapeBytes`. -/
def loadShape [BEq α] [OfNat α 0] [Add α]
    (address stride : α) (count : Nat) (value : CrepExp α) : List (CrepExp α) :=
  match count with
  | 0 => []
  | count + 1 =>
      let loaded := if address == 0 then .load value else .load (.op .add [value, .const address])
      loaded :: loadShape (address + stride) stride count value

/-- Faithful fixed-stride loading: load `count` consecutive words starting at
    `address`, stepping by the fixed machine byte width supplied by the
    `CrepBytesInWord` instance.

    FLAPJACK-SPECIFIC (not an exact HOL port): this helper is generic over the
    word element type, while HOL `crepLang$load_shape_def`
    (`cakeml/pancake/crepLangScript.sml:82-86`) is indexed by the word length
    (`address : 'a word`, `0w`, `byte$bytes_in_word`).  The exact width-indexed
    tag is on `loadShapeBytesW` below. -/
def loadShapeBytes [BEq α] [OfNat α 0] [Add α] [CrepBytesInWord α]
    (address : α) (count : Nat) (value : CrepExp α) : List (CrepExp α) :=
  match count with
  | 0 => []
  | count + 1 =>
      let loaded := if address == 0 then .load value else .load (.op .add [value, .const address])
      loaded :: loadShapeBytes (address + CrepBytesInWord.bytesInWord) count value

/-- Width-indexed production adapter for `loadShapeBytes`. HOL's exact
    `load_shape_def` is tagged on `loadShapeBytesHOLW`, which uses
    `CrepExpHOL`; this adapter still uses production `CrepExp` and is
    Flapjack-specific. -/
def loadShapeBytesW {width : Nat} [NeZero width]
    (address : BitVec width) (count : Nat) (value : CrepExp (BitVec width)) :
    List (CrepExp (BitVec width)) :=
  loadShapeBytes address count value

/-- Checked invariant connecting the pipeline's parameterized `loadShape` to the
    faithful fixed-width `loadShapeBytes`: when the explicit stride is the
    machine byte width, the two agree.  The production `.load` lowering passes
    `context.bytesInWord` as that stride, so the bridge
    `compileExp_load_eq_loadShapeBytes` below certifies its fixed-width
    behavior.  This is Flapjack infrastructure; HOL has no parameterized
    `load_shape`. -/
theorem loadShape_eq_loadShapeBytes_of_stride_eq [BEq α] [OfNat α 0] [Add α]
    [CrepBytesInWord α] (address stride : α) (count : Nat) (value : CrepExp α)
    (hstride : stride = CrepBytesInWord.bytesInWord) :
    loadShape address stride count value = loadShapeBytes address count value := by
  subst hstride
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadShape, loadShapeBytes, ih]

/-- The machine byte width the executable RV64 entry point (`Flapjack.compileMain`)
    passes to the pipeline.  This is the concrete fixed stride on the executed
    path; `riscv64BytesInWord_eq` certifies it is Cake's `byte$bytes_in_word`. -/
def riscv64BytesInWord : BitVec 64 := BitVec.ofNat 64 8

/-- The RISC-V compile context byte width is the fixed machine byte width: the
    pipeline entry points supply `riscv64BytesInWord` for the 64-bit word, which
    is exactly `byte$bytes_in_word` (`n2w (dimindex (:'a) DIV 8)`). -/
theorem riscv64BytesInWord_eq : riscv64BytesInWord = CrepBytesInWord.bytesInWord := rfl

/-- The RISC-V compile context byte width is the fixed machine byte width: the
    pipeline entry points supply `8` for the 64-bit word, which is exactly
    `byte$bytes_in_word` (`n2w (dimindex (:'a) DIV 8)`). -/
theorem riscvBytesInWord_eq : (8 : BitVec 64) = CrepBytesInWord.bytesInWord := rfl

/-- The 32-bit oracle probe width is the fixed machine byte width: the checked-in
    `crep_load_shape_probe.out` was produced with `32 word` values, for which
    `byte$bytes_in_word = 4`. -/
theorem probeBytesInWord_eq : (4 : BitVec 32) = CrepBytesInWord.bytesInWord := rfl

/-- Flapjack-specific Nat/variable-stride indexing helper. The exact HOL
    `load_shape_el_rel` port uses word arithmetic and fixed machine-byte
    stride in `Proofs/PanToCrep.lean`. -/
theorem loadShape_getElem (address stride count n : Nat) (value : CrepExp Nat)
    (h : n < count) :
    (loadShape address stride count value)[n]? =
      some (if address + n * stride == 0 then .load value
            else .load (.op .add [value, .const (address + n * stride)])) := by
  induction count generalizing address n with
  | zero => simp at h
  | succ count ih =>
      cases n with
      | zero => simp [loadShape]
      | succ k =>
          have hk : k < count := by omega
          rw [loadShape]
          simp only [List.getElem?_cons_succ]
          rw [ih (address + stride) k hk]
          have haddr : (address + stride) + k * stride = address + (k + 1) * stride := by
            rw [Nat.add_mul, Nat.one_mul]
            ac_rfl
          simp only [haddr]

/-- Original-domain counterpart of Cake's `load_glob_not_mem_load`
    (`cakeml/pancake/semantics/crepPropsScript.sml:688`): a global load absent
    from an expression's expression list stays absent from every expression
    produced by `loadShape`. -/
theorem crepExps_loadShape_not_mem_loadGlob [BEq α] [OfNat α 0] [Add α]
    (address stride : α) (count : Nat) (value : CrepExp α) (target : BitVec 5)
    (h : CrepExp.loadGlob target ∉ crepExps value) :
    CrepExp.loadGlob target ∉ (loadShape address stride count value).flatMap crepExps := by
  induction count generalizing address with
  | zero => simp [loadShape]
  | succ count ih =>
      rw [loadShape]
      simp only [List.flatMap_cons, List.mem_append, not_or]
      refine ⟨?_, ih (address + stride)⟩
      by_cases hz : address == 0
      · simp only [hz, if_true]
        simpa [crepExps] using h
      · simp only [hz]
        simp [crepExps, crepExps.crepExpsList, h]

/-- Original-domain counterpart of Cake's `var_exp_load_shape`
    (`cakeml/pancake/semantics/crepPropsScript.sml:215`): every expression
    produced by `loadShape` has the same free variables as its source. -/
theorem crepExpVars_of_mem_loadShape [BEq α] [OfNat α 0] [Add α]
    (address stride : α) (count : Nat) (value n : CrepExp α)
    (h : n ∈ loadShape address stride count value) :
    crepExpVars n = crepExpVars value := by
  induction count generalizing address with
  | zero => simp [loadShape] at h
  | succ count ih =>
      rw [loadShape] at h
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · by_cases hzero : address == 0
        · simp [hzero, crepExpVars]
        · simp [hzero, crepExpVars, crepExpVars.crepExpVarsList]
      · exact ih (address + stride) h

/- FLAPJACK-SPECIFIC (not an exact HOL port): this helper is generic over
    `CrepProg α`/`CrepExp α`, while HOL `crepLang$prog`/`exp` are indexed by
    the word length (`'a word`). The exact width-indexed tag is on the
    `...W` wrapper below (over `BitVec width`). -/
def crepNestedSeq : List (CrepProg α) → CrepProg α
  | [] => .skip
  | statement :: statements => .seq statement (crepNestedSeq statements)


/-- Faithful port of Cake `crepProps$exps_of` from
    `cakeml/pancake/semantics/crepPropsScript.sml:1282`: collect the
    expressions that occur directly in a Crepe program. -/
def crepExpsOf : CrepProg α → List (CrepExp α)
  | .dec _ value body => value :: crepExpsOf body
  | .seq first second => crepExpsOf first ++ crepExpsOf second
  | .ite condition thenBranch elseBranch =>
      condition :: (crepExpsOf thenBranch ++ crepExpsOf elseBranch)
  | .while condition body => condition :: crepExpsOf body
  | .call info _ args =>
      args ++ (match info with
               | some (_, some (_, handler)) => crepExpsOf handler
               | _ => [])
  | .store address value => [address, value]
  | .store32 address value => [address, value]
  | .storeByte address value => [address, value]
  | .storeGlob _ value => [value]
  | .return values => values
  | .assign _ value => [value]
  | .shMem _ _ address => [address]
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- Cake's `crepProps$exps_of_nested_seq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:1010`). -/
theorem crepExpsOf_nestedSeq (statements : List (CrepProg α)) :
    crepExpsOf (crepNestedSeq statements) =
      (statements.map crepExpsOf).flatten := by
  induction statements with
  | nil => simp [crepNestedSeq, crepExpsOf]
  | cons statement statements ih => simp [crepNestedSeq, crepExpsOf, ih]

/-! Faithful port of Cake `crep_seqs_def` from
    `cakeml/pancake/pan_passesScript.sml:377`: flatten only `Seq` nodes,
    preserving the left-to-right order of all other Crepe statements. -/
def crepSeqs : CrepProg α → List (CrepProg α)
  | .seq first second => crepSeqs first ++ crepSeqs second
  | program => [program]
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! UNTAGGED (documented mismatch with `crepLang$stores_def`,
    `cakeml/pancake/crepLangScript.sml:95-100`): HOL fixes the stride to
    `byte$bytes_in_word` (derived from the word length), whereas this helper
    takes `stride` as an explicit argument so it can serve several callers
    (`crepAssigned*_nestedSeq_stores`).  A width-indexed `stores` with the fixed
    stride is the exact counterpart once the stride is tied to the word type. -/
def stores [BEq α] [OfNat α 0] [Add α]
    (address : CrepExp α) : List (CrepExp α) → α → α → List (CrepProg α)
  | [], _, _ => []
  | value :: values, offset, stride =>
      let destination := if offset == 0 then address else .op .add [address, .const offset]
      .store destination value :: stores address values (offset + stride) stride

/-- Exact width-indexed port of HOL `crepLang$stores_def`
     (`cakeml/pancake/crepLangScript.sml:95-100`): HOL's address/offset are
    `'a word` and the stride is the fixed `byte$bytes_in_word`
    (`BitVec.ofNat width (width / 8)`).  Clause-for-clause identical to the
    generic `stores` once the stride is fixed.  The carrier is
    `BitVec width` with `[NeZero width]` because every HOL word type has
    positive `dimindex` (`BitVec 0` has no HOL counterpart), even though the
    body never inspects word bits. -/
@[hol "cakeml/pancake/crepLangScript.sml" "stores_def"]
def storesW {width : Nat} [NeZero width] (address : CrepExp (BitVec width))
    (values : List (CrepExp (BitVec width))) (offset : BitVec width) :
    List (CrepProg (BitVec width)) :=
  match values with
  | [] => []
  | value :: values =>
      let destination := if offset == 0 then address else .op .add [address, .const offset]
      .store destination value ::
        storesW address values (offset + BitVec.ofNat width (width / 8))

/-- Untagged bridge showing the generic stride-parametric `stores` (the
    executed helper; production passes `CrepBytesInWord.bytesInWord`) is the
    exact width-indexed `storesW` when the stride is the machine byte width. -/
theorem storesW_eq_stores {width : Nat} [NeZero width] (address : CrepExp (BitVec width))
    (values : List (CrepExp (BitVec width))) (offset : BitVec width) :
    storesW address values offset =
      stores address values offset (BitVec.ofNat width (width / 8)) := by
  induction values generalizing offset with
  | nil => rfl
  | cons value values ih => simp [storesW, stores, ih]


/- FLAPJACK-SPECIFIC (not an exact HOL port): this helper is generic over
    `CrepProg α`/`CrepExp α`, while HOL `crepLang$prog`/`exp` are indexed by
    the word length (`'a word`). The exact width-indexed tag is on the
    `...W` wrapper below (over `BitVec width`). -/
def nestedDecs : List Nat → List (CrepExp α) → CrepProg α → CrepProg α
  | [], [], body => body
  | name :: names, value :: values, body => .dec name value (nestedDecs names values body)
  | _, _, _ => .skip

/-! ## Width-indexed exact wrappers for the crepLang core definitions

HOL `crepLangScript.sml` indexes `prog`/`exp` by the word length (`Const ('a
word)`), so the exact tagged declarations are stated over `BitVec width`
(`= RiscV.Word width`); the generic helpers above remain untagged Flapjack
infrastructure.  Every HOL `word` type has a positive `dimindex`, so the exact
wrappers carry `[NeZero width]` (as the WordLang/CrepArith tagged ports do),
even though their bodies never inspect the word bits.

The executed compiler path calls the generic helpers, whose carriers stay
generic over the word element type (`compileProgHOL`/`compileProg` in
`Flapjack/Pancake/PanToCrep/Compile.lean`, `crepInlineTmpNames`/
`crepInlineCallBody`/`crepInlineProgFmap` in
`Flapjack/Pancake/CrepInline/Pass.lean`, `crepVarProg`/`crepArgLoad` in
`Flapjack/Pancake/CrepInline.lean`, and `maxCrepExpVarHOL`/`expHdlFiniteMap`).
Each `...W` wrapper below is a definitional delegation (`def W ... := generic`),
so those call sites compute the identical function; routing them literally
through the `...W` names is blocked only by their generic carriers (the
deferred width-indexing migration `flapjack-pxn.18.3.5.3.1`) and is tracked by
`flapjack-pxn.18.4.3.82`. -/
/-- Exact width-indexed port of HOL `crepLang$nested_seq_def`
    (`cakeml/pancake/crepLangScript.sml:89`). -/
@[hol "cakeml/pancake/crepLangScript.sml" "nested_seq_def"]
def crepNestedSeqW {width : Nat} [NeZero width] (statements : List (CrepProg (BitVec width))) :
    CrepProg (BitVec width) :=
  crepNestedSeq statements

/-- Exact width-indexed port of HOL `crepLang$nested_decs_def`
    (`cakeml/pancake/crepLangScript.sml:102`). -/
@[hol "cakeml/pancake/crepLangScript.sml" "nested_decs_def"]
def nestedDecsW {width : Nat} [NeZero width] (names : List Nat)
    (values : List (CrepExp (BitVec width))) (body : CrepProg (BitVec width)) :
    CrepProg (BitVec width) :=
  nestedDecs names values body

/-- Exact width-indexed port of HOL `crepLang$assigned_free_vars_def`
    (`cakeml/pancake/crepLangScript.sml:149`). -/
@[hol "cakeml/pancake/crepLangScript.sml" "assigned_free_vars_def"]
def crepAssignedFreeVarsW {width : Nat} [NeZero width] (program : CrepProg (BitVec width)) : List Nat :=
  crepAssignedFreeVars program

/-- Exact width-indexed port of HOL `crepLang$assigned_vars_def`
    (`cakeml/pancake/crepLangScript.sml:164`). -/
@[hol "cakeml/pancake/crepLangScript.sml" "assigned_vars_def"]
def crepAssignedVarsW {width : Nat} [NeZero width] (program : CrepProg (BitVec width)) : List Nat :=
  crepAssignedVars program

/-- Exact width-indexed port of HOL `crepLang$var_cexp_def`
    (`cakeml/pancake/crepLangScript.sml:128`).  Note: the source file spells the
    last equation `var_cexp TopAddrl = []`, but `TopAddrl` is the
    overload-disambiguated *printing* of the `crepLang$exp` constructor
    `TopAddr` (fetched `crepLangTheory` `var_cexp_def` reads
    `var_cexp BaseAddr = [] \/\ var_cexp TopAddr = []`), so the Lean `.topAddr`
    clause is the exact counterpart; oracle
    `scripts/hol-probes/crep_var_cexp_probe.out` row `base_top=([],[])`
    confirms. -/
@[hol "cakeml/pancake/crepLangScript.sml" "var_cexp_def"]
def crepExpVarsW {width : Nat} [NeZero width] (expression : CrepExp (BitVec width)) : List Nat :=
  crepExpVars expression

/-- Exact width-indexed port of HOL `crepLang$exps_def`
    (`cakeml/pancake/crepLangScript.sml:193`). -/
@[hol "cakeml/pancake/crepLangScript.sml" "exps_def"]
def crepExpsW {width : Nat} [NeZero width] (expression : CrepExp (BitVec width)) :
    List (CrepExp (BitVec width)) :=
  crepExps expression

theorem crepExpsOf_nestedDecs (names : List Nat) :
    ∀ (values : List (CrepExp α)) (body : CrepProg α) {e : CrepExp α},
      e ∈ crepExpsOf (nestedDecs names values body) →
        e ∈ values ∨ e ∈ crepExpsOf body := by
  induction names with
  | nil =>
      intro values body e hmem
      cases values with
      | nil => exact Or.inr (by simpa [nestedDecs] using hmem)
      | cons value values => simp [nestedDecs, crepExpsOf] at hmem
  | cons name names ih =>
      intro values body e hmem
      cases values with
      | nil => simp [nestedDecs, crepExpsOf] at hmem
      | cons value values =>
          simp only [nestedDecs, crepExpsOf, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact Or.inl (by simp)
          · rcases ih values body hmem with hv | hb
            · exact Or.inl (by simp [hv])
            · exact Or.inr hb

theorem crepExpsOf_nestedSeq_assign (names : List Nat) :
    ∀ (values : List (CrepExp α)) {e : CrepExp α},
      e ∈ crepExpsOf
          (crepNestedSeq (panMap2 (fun name value => .assign name value)
            names values)) →
        e ∈ values := by
  induction names with
  | nil =>
      intro values e hmem
      cases values with
      | nil => simp [panMap2, crepNestedSeq, crepExpsOf] at hmem
      | cons value values => simp [panMap2, crepNestedSeq, crepExpsOf] at hmem
  | cons name names ih =>
      intro values e hmem
      cases values with
      | nil => simp [panMap2, crepNestedSeq, crepExpsOf] at hmem
      | cons value values =>
          simp only [panMap2, crepNestedSeq, crepExpsOf, List.mem_cons,
            List.singleton_append] at hmem
          rcases hmem with heq | hmem
          · subst heq; exact by simp
          · exact List.mem_cons.mpr (Or.inr (ih values hmem))

/-- Faithful port of Cake `arg_load_def` from
    `cakeml/pancake/crep_inlineScript.sml:59`: simulate the argument loading
    of a function call as a pair of nested declaration blocks. -/
def argLoad (tmpVars : List Nat) (args : List (CrepExp α))
    (argsVName : List Nat) (body : CrepProg α) : CrepProg α :=
  nestedDecs tmpVars args (nestedDecs argsVName (tmpVars.map CrepExp.var) body)

/-- Cake's `exps_of_arg_load` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:3057`):
    an expression occurring in an argument load is either one of the loaded
    argument expressions, a temporary variable, or an expression of the body. -/
theorem crepExpsOf_argLoad (tmpVars : List Nat) (args : List (CrepExp α))
    (argsVName : List Nat) (body : CrepProg α) {e : CrepExp α}
    (hmem : e ∈ crepExpsOf (argLoad tmpVars args argsVName body)) :
    e ∈ args ∨ (∃ c, c ∈ tmpVars ∧ e = .var c) ∨ e ∈ crepExpsOf body := by
  unfold argLoad at hmem
  rcases crepExpsOf_nestedDecs tmpVars args
      (nestedDecs argsVName (tmpVars.map CrepExp.var) body) hmem with hargs | hinner
  · exact Or.inl hargs
  · rcases crepExpsOf_nestedDecs argsVName (tmpVars.map CrepExp.var) body hinner with
      hvars | hbody
    · rcases List.mem_map.mp hvars with ⟨c, hc, heq⟩
      exact Or.inr (Or.inl ⟨c, hc, heq.symm⟩)
    · exact Or.inr (Or.inr hbody)

/- FLAPJACK-SPECIFIC (not an exact HOL port): generic over `CrepProg α`/
   `CrepExp α`, while HOL `prog`/`exp` are indexed by the word length. The exact
   width-indexed tag is on `storeGlobalsW` below. -/
def storeGlobals {α : Type u}
    (address : BitVec 5) : List (CrepExp α) → List (CrepProg α)
  | [] => []
  | value :: values => .storeGlob address value :: storeGlobals (address + 1) values

/- FLAPJACK-SPECIFIC (not an exact HOL port): generic over `CrepExp α`; the
   exact width-indexed tag is on `loadGlobalsW` below. -/
def loadGlobals {α : Type u}
    (address : BitVec 5) (count : Nat) : List (CrepExp α) :=
  match count with
  | 0 => []
  | count + 1 => .loadGlob address :: loadGlobals (address + 1) count

/-- Exact width-indexed port of HOL `store_globals_def`
    (`cakeml/pancake/crepLangScript.sml:109-113`).  Carrier `BitVec width` with
    `[NeZero width]` because HOL word types have positive `dimindex`. -/
@[hol "cakeml/pancake/crepLangScript.sml" "store_globals_def"]
def storeGlobalsW {width : Nat} [NeZero width]
    (address : BitVec 5) (values : List (CrepExp (BitVec width))) :
    List (CrepProg (BitVec width)) :=
  storeGlobals address values

/-- Exact width-indexed port of HOL `load_globals_def`
    (`cakeml/pancake/crepLangScript.sml:116-119`).  Carrier `BitVec width` with
    `[NeZero width]` because HOL word types have positive `dimindex`. -/
@[hol "cakeml/pancake/crepLangScript.sml" "load_globals_def"]
def loadGlobalsW {width : Nat} [NeZero width]
    (address : BitVec 5) (count : Nat) : List (CrepExp (BitVec width)) :=
  loadGlobals address count

/-- Faithful port of Cake `crepProps$assigned_free_vars_seq_store_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:439`). -/
theorem crepAssignedFreeVars_nestedSeq_stores [BEq α] [OfNat α 0] [Add α]
    (address : CrepExp α) (values : List (CrepExp α)) (offset stride : α) :
    crepAssignedFreeVars (crepNestedSeq (stores address values offset stride)) = [] := by
  induction values generalizing offset with
  | nil => simp [stores, crepNestedSeq, crepAssignedFreeVars]
  | cons value values ih =>
      simp [stores, crepNestedSeq, crepAssignedFreeVars, ih]

/-- Faithful port of Cake `crepProps$assigned_vars_nested_decs_append`
    (`cakeml/pancake/semantics/crepPropsScript.sml:390`). -/
theorem crepAssignedVars_nestedDecs_append (names : List Nat)
    (values : List (CrepExp α)) (body : CrepProg α)
    (h : names.length = values.length) :
    crepAssignedVars (nestedDecs names values body) = names ++ crepAssignedVars body := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => simp [nestedDecs]
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons] at h
          simp [nestedDecs, crepAssignedVars, ih values (by omega)]

/-- Faithful port of Cake `crepProps$assigned_free_vars_nested_decs_append`
    (`cakeml/pancake/semantics/crepPropsScript.sml:400`). -/
theorem crepAssignedFreeVars_nestedDecs_append (names : List Nat)
    (values : List (CrepExp α)) (body : CrepProg α)
    (h : names.length = values.length) :
    crepAssignedFreeVars (nestedDecs names values body) =
      (crepAssignedFreeVars body).filter
        (fun candidate => decide (candidate ∉ names)) := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil =>
          simp only [nestedDecs, List.not_mem_nil]
          symm
          exact List.filter_eq_self.mpr (fun _ _ => rfl)
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons] at h
          rw [nestedDecs, crepAssignedFreeVars, ih values (by omega), List.filter_filter]
          congr 1
          funext candidate
          by_cases hc : candidate = name
          · subst hc
            simp
          · simp [hc, List.mem_cons, bne_iff_ne]

/-- A variable absent from both the declared slots and the body's assigned
    free variables is absent from the `nestedDecs` body.  This is the
    `not_mem_context_assigned_mem_gt` transport step for the declarations
    introduced by `compileProg`. -/
theorem not_mem_crepAssignedFreeVars_nestedDecs (names : List Nat)
    (values : List (CrepExp α)) (body : CrepProg α)
    (h : names.length = values.length) {x : Nat}
    (hbody : x ∉ crepAssignedFreeVars body) :
    x ∉ crepAssignedFreeVars (nestedDecs names values body) := by
  rw [crepAssignedFreeVars_nestedDecs_append names values body h]
  intro hmem
  exact hbody (List.mem_filter.mp hmem).1

/-! The membership form used by Cake's
`not_mem_context_assigned_mem_gt` induction.  A declaration nest removes
exactly its bound names from the body's assigned-free-variable list; exposing
the converse as an iff keeps the recursive proof from having to unfold the
filter representation at every `compileProg` branch. -/
theorem crepAssignedFreeVars_nestedDecs_mem_iff (names : List Nat)
    (values : List (CrepExp α)) (body : CrepProg α)
    (h : names.length = values.length) (x : Nat) :
    x ∈ crepAssignedFreeVars (nestedDecs names values body) ↔
      x ∈ crepAssignedFreeVars body ∧ x ∉ names := by
  rw [crepAssignedFreeVars_nestedDecs_append names values body h]
  simp

/-- Faithful port of Cake `crepProps$assigned_vars_seq_store_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:429`). -/
theorem crepAssignedVars_nestedSeq_stores [BEq α] [OfNat α 0] [Add α]
    (address : CrepExp α) (values : List (CrepExp α)) (offset stride : α) :
    crepAssignedVars (crepNestedSeq (stores address values offset stride)) = [] := by
  induction values generalizing offset with
  | nil => simp [stores, crepNestedSeq, crepAssignedVars]
  | cons value values ih =>
      simp [stores, crepNestedSeq, crepAssignedVars, ih]

/- FLAPJACK-SPECIFIC (not an exact HOL port): generic over `CrepProg α`; the
   exact width-indexed tag is on `assignRetW` below. -/
def assignRet {α : Type u} [OfNat α 0] [OfNat α 1] [Add α]
    (names : List Nat) : CrepProg α :=
  crepNestedSeq (names.zipWith (fun name value => .assign name value)
    (loadGlobals (0 : BitVec 5) names.length))

/-- Exact width-indexed port of HOL `assign_ret_def`
    (`cakeml/pancake/crepLangScript.sml:122-125`).  Carrier `BitVec width` with
    `[NeZero width]` because HOL word types have positive `dimindex`. -/
@[hol "cakeml/pancake/crepLangScript.sml" "assign_ret_def"]
def assignRetW {width : Nat} [NeZero width] (names : List Nat) :
    CrepProg (BitVec width) :=
  assignRet names

/-- The assignments emitted by `assignRet` assign exactly `names`, so their
    free-variable set is `names`.  Used by the call-handler branch of Cake's
    `not_mem_context_assigned_mem_gt` (`pan_to_crepProofScript.sml:1252`). -/
theorem crepAssignedFreeVars_assignRet {α : Type u}
    [OfNat α 0] [OfNat α 1] [Add α]
    (names : List Nat) :
    crepAssignedFreeVars (assignRet (α := α) names) = names := by
  unfold assignRet
  have aux : ∀ (names : List Nat) (address : BitVec 5),
      crepAssignedFreeVars
          (crepNestedSeq (names.zipWith (fun name value => .assign name value)
            (loadGlobals (α := α) address names.length))) = names := by
    intro names
    induction names with
    | nil => intro address; simp [loadGlobals, crepNestedSeq, crepAssignedFreeVars]
    | cons name names ih =>
        intro address
        simp [loadGlobals, crepNestedSeq, crepAssignedFreeVars, ih]
  exact aux names 0

end Flapjack
