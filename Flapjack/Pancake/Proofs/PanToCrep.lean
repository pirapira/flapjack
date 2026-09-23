import Flapjack.FiniteMap
import Flapjack.HolRef
import Flapjack.PanBst
import Flapjack.PanEmptyLocals
import Flapjack.PanLocalised
import Flapjack.PanValueFlatten
import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpVmax
import Flapjack.CrepeCompileExpVariables
import Flapjack.PanToCrepMaxList

/-!
Faithful HOL-facing relations and contexts for the Pancake `pan_to_crep`
correctness proof.  The definitions here use the extensional finite-map model
from `Flapjack.FiniteMap`, rather than the list-backed executable compiler
context.
-/

namespace Flapjack

/-! Exact Lean port of HOL `globals_lookup_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:435`). The production
    globals field has HOL's `5 word` keys and `word_lab` cells; `panSemShapeOf`
    is the exact `shape_of` port constructor by constructor, with no premises.
    `Shape.shapeSize` matches HOL `size_of_shape_def` on `One`, `Comb` (sum of
    child sizes), and `Named`, also without side conditions. `List.range` with
    `BitVec.ofNat` represents `GENLIST n2w` including 5-bit truncation, and
    `List.mapM` represents `OPT_MMAP`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "globals_lookup_def"]
def globalsLookup (state : CrepRuntimeState α σ) (value : PanValue α) :
    Option (List (PanWordLab α)) :=
  (List.range (Shape.shapeSize (panSemShapeOf value))).mapM
    (fun index => state.globals (BitVec.ofNat 5 index))

/-! Exact utility theorem ports used by the `pan_to_crep` proof development. -/

/-- Exact port of the duplicate Cake `EL_load_globals` theorem
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4102`). The finite
    word offset and bounded total index have the same shape as HOL's `n2w` and
    `EL`; the proof reuses the primary semantics counterpart. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "EL_load_globals"]
theorem elLoadGlobals {α : Type u}
    (n count : Nat) (address : BitVec 5) (h : n < count) :
    (loadGlobals (α := α) address count)[n]'(by
      simpa only [loadGlobals_length] using h) =
        .loadGlob (address + BitVec.ofNat 5 n) := by
  exact loadGlobals_getElem (α := α) address count n h

/-- Flapjack-specific bridge: the source-semantics shape function agrees with
    the pre-existing value shape function at the empty structure context.
    HOL has one `shape_of` function, so this bridge has no HOL original. -/
private theorem panSemShapeOf_eq_panValueShape_nil (value : PanValue α) :
    panSemShapeOf value = panValueShape [] value := by
  induction value using panSemShapeOf.induct with
  | case1 _ => simp [panSemShapeOf, panValueShape]
  | case2 values ih =>
      simpa [panSemShapeOf, panValueShape] using ih
  | case3 _ _ => simp [panSemShapeOf, panValueShape]

/-- HOL `flatten_nil_no_size[local]`: flattening a value of well-formed
    empty-structure shape is empty exactly when its shape has size zero. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "flatten_nil_no_size"]
theorem flattenNilNoSize (value : PanValue α)
    (hwf : isWfShape [] (panSemShapeOf value) = true) :
    panValueFlatten value = [] ↔ Shape.shapeSize (panSemShapeOf value) = 0 := by
  rw [panSemShapeOf_eq_panValueShape_nil] at hwf ⊢
  exact panValueFlatten_eq_nil_iff_shapeSize_eq_zero value hwf

/-- HOL `res_var_commutes'`: restoring two distinct finite-map locals
    commutes. `LawfulBEq` identifies the map implementation's Boolean key
    comparison with HOL equality. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "res_var_commutes'"]
theorem resVarCommutesPrime [BEq α] [LawfulBEq α]
    (locals : FiniteMap α β) (h n : α) (v v' : Option β)
    (hne : n ≠ h) :
    resVar (resVar locals (h, v)) (n, v') =
      resVar (resVar locals (n, v')) (h, v) := by
  funext key
  change FLOOKUP (resVar (resVar locals (h, v)) (n, v')) key =
    FLOOKUP (resVar (resVar locals (n, v')) (h, v)) key
  simp only [FLOOKUP_resVar]
  by_cases hh : key = h <;> by_cases hn : key = n <;>
    simp_all [beq_iff_eq]

/-- Flapjack-only optional-indexing support for HOL `load_shape_el_rel`.
    HOL's `EL` is stated without an Option because its index premise gives
    the required bound; the exact tagged statement follows below. -/
private theorem loadShapeBytes_getElemOpt_rel {width : Nat}
    (address : BitVec width) (count index : Nat)
    (value : CrepExp (BitVec width)) (hindex : index < count) :
    (loadShapeBytes address count value)[index]? =
      some (if address + CrepBytesInWord.bytesInWord *
            BitVec.ofNat width index == 0 then .load value
        else .load (.op .add [value, .const
          (address + CrepBytesInWord.bytesInWord * BitVec.ofNat width index)])) := by
  induction count generalizing address index with
  | zero => omega
  | succ count ih =>
      cases index with
      | zero => simp [loadShapeBytes]
      | succ index =>
          have htail : index < count := by omega
          rw [loadShapeBytes]
          simp only [List.getElem?_cons_succ]
          rw [ih (address + CrepBytesInWord.bytesInWord) index htail]
          have haddr :
              (address + CrepBytesInWord.bytesInWord) +
                  CrepBytesInWord.bytesInWord * BitVec.ofNat width index =
                address + CrepBytesInWord.bytesInWord *
                  BitVec.ofNat width (index + 1) := by
            rw [BitVec.ofNat_add]
            simp [BitVec.mul_add]
            ac_rfl
          simp [haddr]

/-- The fixed-stride loader emits exactly one expression per requested word.
    This is Flapjack-only support for converting optional indexing to HOL `EL`. -/
private theorem loadShapeBytes_length {width : Nat}
    (address : BitVec width) (count : Nat)
    (value : CrepExp (BitVec width)) :
    (loadShapeBytes address count value).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadShapeBytes, ih]

/-- HOL `load_shape_el_rel`: the bounded `EL` of the fixed-stride loader uses
    word offset `address + bytes_in_word * n2w index`. The dependent Lean index
    carries the HOL premise `index < count` without an Option result. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "load_shape_el_rel"]
theorem loadShapeBytes_getElem_rel {width : Nat}
    (address : BitVec width) (count index : Nat)
    (value : CrepExp (BitVec width)) (hindex : index < count) :
    (loadShapeBytes address count value)[index]'(by
      simpa [loadShapeBytes_length] using hindex) =
      if address + CrepBytesInWord.bytesInWord * BitVec.ofNat width index == 0
      then .load value
      else .load (.op .add [value, .const
        (address + CrepBytesInWord.bytesInWord * BitVec.ofNat width index)]) := by
  have hopt := loadShapeBytes_getElemOpt_rel address count index value hindex
  have hvalid : index < (loadShapeBytes address count value).length := by
    simpa [loadShapeBytes_length] using hindex
  rw [List.getElem?_eq_getElem hvalid] at hopt
  exact Option.some.inj hopt

/-- HOL `is_wf_shape_nil_length_flatten`: a word list chosen by the zero-size
    or positive-size branch has the size prescribed by the source value shape. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "is_wf_shape_nil_length_flatten"]
theorem isWfShapeNil_length_flatten (value : PanValue α) (words : List α)
    (hwf : isWfShape [] (panSemShapeOf value) = true)
    (hzero : Shape.shapeSize (panSemShapeOf value) = 0 → words = [])
    (hpositive : 0 < Shape.shapeSize (panSemShapeOf value) →
      words = panValueFlatten value) :
    words.length = Shape.shapeSize (panSemShapeOf value) := by
  rw [panSemShapeOf_eq_panValueShape_nil] at hwf hzero hpositive ⊢
  by_cases hz : Shape.shapeSize (panValueShape [] value) = 0
  · simp [hzero hz, hz]
  · have hpos : 0 < Shape.shapeSize (panValueShape [] value) := Nat.pos_of_ne_zero hz
    rw [hpositive hpos]
    exact panValueFlatten_length_eq_shapeSize value hwf

/-! Local support for `MAP_SOME_MEM_lemma`, kept in its HOL counterpart
    module. This drops the source theorem's unused Nat witness; the exact
    tagged theorem below restores that witness in its original position. -/
theorem mapFlattenMemSomeSupport {α β : Type} (f : α → Option β)
    (xs : List (List α)) (ys : List (List β)) (zs : List α) (z : α)
    (h : xs.flatten.map f = ys.flatten.map some)
    (hzs : zs ∈ xs) (hz : z ∈ zs) :
    ∃ y, f z = some y ∧ y ∈ ys.flatten := by
  have hzflat : z ∈ xs.flatten := List.mem_flatten.mpr ⟨zs, hzs, hz⟩
  have hzmap : f z ∈ xs.flatten.map f := List.mem_map.mpr ⟨z, hzflat, rfl⟩
  rw [h] at hzmap
  obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hzmap
  exact ⟨y, hfy.symm, hy⟩

/-- Faithful port of Cake `pan_to_crepProof$MAP_SOME_MEM_lemma`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4060`). The unused HOL
    existential `r` has type `num`: the source proof instantiates it with the
    flattened-list index `m` (or `LENGTH h + _`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAP_SOME_MEM_lemma"]
theorem mapSomeMemLemma {α β : Type} (f : α → Option β)
    (xs : List (List α)) (ys : List (List β)) (zs : List α) (z : α)
    (h : xs.flatten.map f = ys.flatten.map some)
    (hzs : zs ∈ xs) (hz : z ∈ zs) :
    ∃ (_r : Nat) (y : β), f z = some y ∧ y ∈ ys.flatten := by
  obtain ⟨y, hfy, hy⟩ := mapFlattenMemSomeSupport f xs ys zs z h hzs hz
  exact ⟨0, y, hfy, hy⟩

/-- Faithful port of Cake `pan_to_crepProof$shape_of_alt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1906`). HOL's
    `Val (Word w)` is represented by `PanValue.word w`, and the context-free
    `panSemShapeOf` counterpart retains the exact conclusion shape. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "shape_of_alt"]
theorem panSemShapeOf_word (value : α) :
    panSemShapeOf (.word value) = .one := by
  simp [panSemShapeOf]

/-- Faithful port of Cake `pan_to_crepProof$cexp_heads_eq`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:104`). The simplified
    head collector is imported from the `crepProps` counterpart. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "cexp_heads_eq"]
theorem cexpHeads_eq_cexpHeadsSimp (expressions : List (List (CrepExp α))) :
    cexpHeads expressions = cexpHeadsSimp expressions := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      cases expression with
      | nil => simp [cexpHeads, cexpHeadsSimp]
      | cons head tail =>
          simp only [cexpHeads, ih, cexpHeadsSimp]
          cases h : expressions.any List.isEmpty <;> simp [h]

/-- HOL `MAX_LIST_APPEND`: the maximum of an appended list is the maximum
    of the two constituent maxima. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAX_LIST_APPEND"]
theorem maxListAppendHol (first second : List Nat) :
    maxList (first ++ second) = max (maxList first) (maxList second) :=
  maxList_append first second

/-- HOL `MAX_LIST_NOT_MEM`: a natural number above the list maximum is not
    present in that list. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAX_LIST_NOT_MEM"]
theorem maxListNotMemHol (x : Nat) (values : List Nat)
    (h : x > maxList values) : x ∉ values :=
  maxList_not_mem x values h

section
attribute [local instance] Classical.propDecidable

/-- HOL `flookup_res_var_thm_quant`: restoring one key changes only that
    key's lookup. Lawful Boolean equality represents HOL key equality. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "flookup_res_var_thm_quant"]
theorem flookupResVarQuant [BEq κ] [LawfulBEq κ]
    (locals : FiniteMap κ α)
    (name query : κ) (value : Option α) :
    FLOOKUP (resVar locals (name, value)) query =
      if query = name then value else FLOOKUP locals query := by
  simpa [beq_iff_eq] using FLOOKUP_resVar locals name query value

end

/-- HOL `no_overlap_wrap_rt_some_all_distinct`: a successful wrapped return
    lookup retains the duplicate-free slot list supplied by `no_overlap`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "no_overlap_wrap_rt_some_all_distinct"]
theorem noOverlapWrapRtNodup
    (fm : FiniteMap String (Shape × List Nat)) (name : String)
    (shape : Shape) (slots : List Nat)
    (hno : noOverlap fm)
    (hwrap : wrapRt (FLOOKUP fm name) = some (shape, slots)) :
    slots.Nodup := by
  cases hlookup : FLOOKUP fm name with
  | none => simp [wrapRt, hlookup] at hwrap
  | some entry =>
      rcases entry with ⟨entryShape, entrySlots⟩
      have hnodup : entrySlots.Nodup :=
        hno.1 name entryShape entrySlots hlookup
      cases entryShape <;> cases entrySlots <;>
        simp [wrapRt, hlookup] at hwrap <;>
        rcases hwrap with ⟨_, hslots⟩ <;>
        simpa [← hslots] using hnodup

/-- HOL `mem_comp_field_lem`: selecting a compiled record field retains an
    input expression or produces the zero fallback. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mem_comp_field_lem"]
theorem compileField_mem_or_zero
    [OfNat α 0]
    (index : Nat) (shapes : List Shape) (expressions : List (CrepExp α))
    (expression : CrepExp α)
    (hmem : expression ∈ (compileField index shapes expressions).1) :
    expression ∈ expressions ∨ expression = .const 0 := by
  induction shapes generalizing index expressions with
  | nil =>
      simp [compileField] at hmem
      exact Or.inr hmem
  | cons shape shapes ih =>
      cases index with
      | zero =>
          left
          exact List.mem_of_mem_take hmem
      | succ index =>
          have hdrop : expression ∈
              (compileField index shapes
                (expressions.drop (Shape.shapeSize shape))).1 := by
            simpa [compileField] using hmem
          rcases ih index (expressions.drop (Shape.shapeSize shape)) hdrop with
            hinput | hzero
          · exact Or.inl (List.mem_of_mem_drop hinput)
          · exact Or.inr hzero

/-- Flapjack-only support for the exact HOL `mem_comp_field` statement below:
    a valid field index excludes the source definition's zero fallback. -/
private theorem compileField_mem_of_index_lt
    [OfNat α 0] (index : Nat) (shapes : List Shape)
    (expressions : List (CrepExp α)) (candidate : CrepExp α)
    (hindex : index < shapes.length)
    (hmem : candidate ∈ (compileField index shapes expressions).1) :
    candidate ∈ expressions := by
  induction shapes generalizing index expressions with
  | nil => simp at hindex
  | cons shape shapes ih =>
      cases index with
      | zero =>
          exact List.mem_of_mem_take (by simpa [compileField] using hmem)
      | succ index =>
          have hindex' : index < shapes.length := by simpa using hindex
          have hmem' : candidate ∈
              (compileField index shapes
                (expressions.drop (Shape.shapeSize shape))).1 := by
            simpa [compileField] using hmem
          exact List.mem_of_mem_drop
            (ih index (expressions.drop (Shape.shapeSize shape)) hindex' hmem')

/-- HOL `mem_comp_field`: with a valid record-field index and matching
    source record shape, every expression selected by the pair-valued
    `compileField` is from the flattened record input. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mem_comp_field"]
theorem compileField_mem_of_record_shape
    [OfNat α 0] (shapes : List Shape) (index : Nat)
    (expressions : List (CrepExp α)) (selectedShape : Shape)
    (candidate : CrepExp α) (selected : List (CrepExp α))
    (values : List (PanValue α))
    (hindex : index < values.length)
    (_hlength : expressions.length =
      Shape.shapeSize (panSemShapeOf (.rStruct values)))
    (hcompiled : compileField index shapes expressions =
      (selected, selectedShape))
    (hshape : Shape.comb shapes = panSemShapeOf (.rStruct values))
    (hmem : candidate ∈ selected) :
    candidate ∈ expressions := by
  have hshapes : shapes = values.map panSemShapeOf :=
    Shape.comb.inj (by simpa [panSemShapeOf] using hshape)
  have hindex' : index < shapes.length := by
    simpa [hshapes] using hindex
  have hmem' : candidate ∈ (compileField index shapes expressions).1 := by
    simpa [hcompiled] using hmem
  exact compileField_mem_of_index_lt index shapes expressions candidate hindex' hmem'

/-- HOL `filter_not_mem_self`: filtering a list by non-membership in that
    same list removes every element. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "filter_not_mem_self"]
theorem filter_not_mem_self {α : Type} [DecidableEq α] (l : List α) :
    l.filter (fun x => decide (x ∉ l)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp [hx]

/-! Cake `not_none_then_some` (`pan_to_crepProofScript.sml:3593`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "not_none_then_some"]
theorem option_ne_none_iff_exists {α : Type} (x : Option α) :
    x ≠ none ↔ ∃ a, x = some a := by
  constructor
  · intro h
    cases x with
    | none => exact absurd rfl h
    | some a => exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact Option.some_ne_none a

/-! Cake `mod_eq_lt_eq` (`pan_to_crepProofScript.sml:4621`): below the
modulus, reduction is the identity. The HOL conjunction of three premises is
represented by Lean's curried theorem arguments. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mod_eq_lt_eq"]
theorem mod_eq_of_lt_eq {n x m : Nat} (hn : n < x) (hm : m < x)
    (h : n % x = m % x) : n = m := by
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at h
  exact h

/-! Cake `pair_map_I` (`pan_to_crepProofScript.sml:4630`): the uncurried pair
constructor is the identity on pairs. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pair_map_I"]
theorem prod_mk_pair_eq_id {α β : Type} :
    (fun p : α × β => (p.1, p.2)) = id := by
  funext p
  cases p
  rfl

/-! The HOL proof context record used by `ctxt_fc_def`. -/
structure PanToCrepProofContext (α : Type) where
  vars : FiniteMap String (Shape × List Nat)
  funcs : FiniteMap String (List (String × Shape) × Shape)
  eids : FiniteMap String α
  vmax : Nat

/-! HOL `excp_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:16`).
    This states equality of exception-code map domains and injectivity of the
    compiler's code map on its defined entries; the source exception map's
    values need not equal the compiler's values. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "excp_rel_def"]
def excpRel
    (compilerCodes : FiniteMap String α)
    (sourceShapes : FiniteMap String β) : Prop :=
  FDOM sourceShapes = FDOM compilerCodes ∧
    ∀ exception exception' code code',
      FLOOKUP compilerCodes exception = some code →
      FLOOKUP compilerCodes exception' = some code' →
      code = code' → exception = exception'

/-! HOL `ctxt_fc_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:25`).
    `FUPDATE_LIST` and `withShape` preserve the source definition's ZIP
    truncation and TAKE/DROP slicing, and `maxList` is Cake's `MAX_LIST`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_def"]
def ctxtFc
    (compilerFunctions : FiniteMap String (List (String × Shape) × Shape))
    (exceptionCodes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) : PanToCrepProofContext α :=
  { vars := FUPDATE_LIST FEMPTY
      (variables.zip (shapes.zip (withShape shapes names)))
    funcs := compilerFunctions
    eids := exceptionCodes
    vmax := maxList names }

/-- HOL `ctxt_fc_funcs_eq`: constructing a function context preserves the
    supplied function map. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_funcs_eq"]
theorem ctxtFcFuncsEq
    (functions : FiniteMap String (List (String × Shape) × Shape))
    (codes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) :
    (ctxtFc functions codes variables shapes names).funcs = functions := rfl

/-- HOL `ctxt_fc_eids_eq`: constructing a function context preserves the
    supplied exception-code map. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_eids_eq"]
theorem ctxtFcEidsEq
    (functions : FiniteMap String (List (String × Shape) × Shape))
    (codes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) :
    (ctxtFc functions codes variables shapes names).eids = codes := rfl

/-- HOL `ctxt_fc_vmax`: the constructed context's maximum slot is the
    maximum of the supplied slot list. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_vmax"]
theorem ctxtFcVmax
    (context : PanToCrepProofContext α) (codes : FiniteMap String α)
    (variables : List String) (shapes : List Shape) (names : List Nat) :
    (ctxtFc context.funcs codes variables shapes names).vmax = maxList names := rfl

/-- HOL `ctxt_max_el_leq`: a slot selected from a variable's flattened name
    list does not exceed the context's maximum slot. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_max_el_leq"]
theorem ctxtMaxGetElemLe
    (context : PanToCrepProofContext α) (varName : String)
    (shape : Shape) (names : List Nat) (index : Nat)
    (hmax : ctxtMax context.vmax context.vars)
    (hlookup : FLOOKUP context.vars varName = some (shape, names))
    (hindex : index < names.length) :
    names[index] ≤ context.vmax := by
  exact hmax.2 varName shape names hlookup names[index] (List.getElem_mem hindex)

/-- HOL `slc_def`: pair each source parameter name with its argument value,
    with `ZIP` truncation represented by Lean's `List.zip`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "slc_def"]
def slc (parameters : List (String × Shape))
    (arguments : List (PanValue α)) : FiniteMap String (PanValue α) :=
  FUPDATE_LIST FEMPTY ((parameters.map Prod.fst).zip arguments)

/-- HOL `tlc_def`: pair target slots with the flattened argument words. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "tlc_def"]
def tlc (slots : List Nat) (arguments : List (PanValue α)) :
    FiniteMap Nat α :=
  FUPDATE_LIST FEMPTY (slots.zip (arguments.flatMap panValueFlatten))

/-- HOL `slc_tlc_rw`: both local-map constructor names unfold to their
    original finite-map updates. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "slc_tlc_rw"]
theorem slcTlcRw
    (parameters : List (String × Shape)) (slots : List Nat)
    (arguments : List (PanValue α)) :
    (FUPDATE_LIST FEMPTY ((parameters.map Prod.fst).zip arguments) =
      slc parameters arguments) ∧
    (FUPDATE_LIST FEMPTY (slots.zip (arguments.flatMap panValueFlatten)) =
      tlc slots arguments) := ⟨rfl, rfl⟩

/-! HOL `state_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:45`).
    The source Pancake state and target Crepe state agree on their memory
    domains, clock, endianness, FFI state, and address bounds; the source has
    no struct context (`s.structs = []`) and no globals (`s.globals = FEMPTY`).
    `word_lab` is a single-constructor type, so the target's raw word cells
    reconstruct the source `PanValue` cells with `PanValue.word`; a source cell
    that stored a structure could not be recovered from the target memory and
    therefore does not satisfy the relation. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_def"]
def stateRel (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ) : Prop :=
  s.memory = (fun address => some (PanValue.word (panTheWord (t.memory address)))) ∧
    s.memaddrs = t.memaddrs ∧
    s.sharedMemaddrs = t.shMemaddrs ∧ s.structs = [] ∧
    s.globals = (FEMPTY : FiniteMap VarName (PanValue α)) ∧
    s.clock = t.clock ∧ s.be = t.bigEndian ∧ s.ffi = t.ffi ∧
    s.baseAddress = t.baseAddress ∧ s.topAddress = t.topAddress

/-- HOL `state_rel_structs[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:59`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_structs"]
theorem stateRel_structs (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ)
    (hrel : stateRel s t) : s.structs = [] := by
  rcases hrel with ⟨_, _, _, hstructs, _, _, _, _, _, _⟩
  exact hstructs

/-- HOL `state_rel_globals[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:65`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_globals"]
theorem stateRel_globals (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ)
    (hrel : stateRel s t) : s.globals = (FEMPTY : FiniteMap VarName (PanValue α)) := by
  rcases hrel with ⟨_, _, _, _, hglobals, _, _, _, _, _⟩
  exact hglobals

/-- Flapjack-specific bridge for the target memory representation.  HOL
    `crepSem$state.memory` is a *total* `word -> word_lab` function
    (`cakeml/pancake/semantics/crepSemScript.sml:24-26`) guarded by the separate
    `memaddrs` set; the executable `CrepRuntimeState.memory` stores absence in an
    `Option`.  The relation records the HOL view on every address the guard
    accepts, so no `word_lab` cell is silently dropped.  It is the target-side
    hypothesis of the `mem_load_def` correspondence below. -/
def crepMemoryRel (state : CrepRuntimeState α σ) (total : α → PanWordLab α) : Prop :=
  state.memory = total

/-- First branch of HOL `mem_load_def`
    (`cakeml/pancake/semantics/crepSemScript.sml:48-51`): a load at an address in
    `memaddrs` returns the total memory cell, reconstructed as a `word_lab`. -/
theorem crepRuntimeLoad_eq_some_of_crepMemoryRel {state : CrepRuntimeState α σ}
    {total : α → PanWordLab α} (hrel : crepMemoryRel state total) {address : α}
    (hvalid : state.memaddrs address = true) :
    crepRuntimeLoad state address = some (panTheWord (total address)) := by
  change state.memory = total at hrel
  rw [crepRuntimeLoad]
  simp [hvalid, hrel]

/-- Second branch of HOL `mem_load_def`: an address outside `memaddrs` has no
    loadable cell. -/
theorem crepRuntimeLoad_eq_none_of_memaddrs_false {state : CrepRuntimeState α σ}
    {address : α} (hinvalid : state.memaddrs address = false) :
    crepRuntimeLoad state address = none := by
  rw [crepRuntimeLoad]
  simp [hinvalid]

/-- First branch of HOL `panSem$mem_store`
    (`cakeml/pancake/semantics/panSemScript.sml:373-378`) as used by
    `crepSem$evaluate`'s store case: a store at an address in `memaddrs`
    succeeds and updates exactly that address, keeping the rest of the memory
    function. -/
theorem crepRuntimeStore_eq_some_of_memaddrs_true [BEq α]
    {state : CrepRuntimeState α σ} {address value : α}
    (hvalid : state.memaddrs address = true) :
    crepRuntimeStore state address value =
      some { state with memory := updateCrepRuntimeMemory state.memory address (.word value) } := by
  rw [crepRuntimeStore]
  simp [hvalid]

/-- Second branch of HOL `panSem$mem_store`: a store outside `memaddrs` fails. -/
theorem crepRuntimeStore_eq_none_of_memaddrs_false [BEq α]
    {state : CrepRuntimeState α σ} {address value : α}
    (hinvalid : state.memaddrs address = false) :
    crepRuntimeStore state address value = none := by
  rw [crepRuntimeStore]
  simp [hinvalid]

/-- Storing a value preserves `crepMemoryRel` when the total memory function is
    updated at the same address: the stored cell becomes the `word_lab` of the
    value, and every other guarded address is untouched. -/
theorem crepMemoryRel_store [BEq α] {state : CrepRuntimeState α σ}
    {total : α → PanWordLab α} (hrel : crepMemoryRel state total) {address : α}
    (_hvalid : state.memaddrs address = true) (value : α) :
    crepMemoryRel
      { state with memory := updateCrepRuntimeMemory state.memory address (.word value) }
      (fun current => if current == address then .word value else total current) := by
  unfold crepMemoryRel at hrel ⊢
  rw [hrel]
  funext current
  by_cases hsame : current == address
  · simp [updateCrepRuntimeMemory, hsame]
  · simp [updateCrepRuntimeMemory, hsame]

/-- HOL `locals_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:71`):
    the proof context's variable map is well formed, and every live source
    variable is recovered in the target locals by mapping its slot list through
    the target map, with the flattened value equal to the produced word list and
    the variable's shape well formed against the empty struct context. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_def"]
def localsRel (context : PanToCrepProofContext α)
    (sLocals : FiniteMap String (PanValue α))
    (tLocals : FiniteMap Nat (PanWordLab α)) : Prop :=
  noOverlap context.vars ∧ ctxtMax context.vmax context.vars ∧
    ∀ vname v, FLOOKUP sLocals vname = some v →
      ∃ ns vs, FLOOKUP context.vars vname = some (panValueShape [] v, ns) ∧
        ns.mapM (FLOOKUP tLocals) = some vs ∧
        (panValueFlatten v).map PanWordLab.word = vs ∧
        isWfShape [] (panValueShape [] v) = true

/-- HOL `locals_rel_wf_shape`: every source local covered by the local-state
    relation is a well-formed value in the empty struct context. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_wf_shape" 2345]
theorem localsRelWfShape
    (context : PanToCrepProofContext α)
    (sourceLocals : FiniteMap String (PanValue α))
    (targetLocals : FiniteMap Nat (PanWordLab α)) (name : String) (value : PanValue α)
    (hrel : localsRel context sourceLocals targetLocals)
    (hlookup : FLOOKUP sourceLocals name = some value) :
    panValueIsWf [] value = true := by
  obtain ⟨_, _, hmembers⟩ := hrel
  obtain ⟨_, _, _, _, _, hshape⟩ := hmembers name value hlookup
  rw [← panValueIsWf_eq_isWfShape_panValueShape_of_nil [] value rfl]
  exact hshape

/-- The state-based 64-bit specialization of Cake
    `opt_mmap_eval_is_wf_shape_v`; its evaluator premise is derived solely
    from `PanSemState`, including its
    word-memory domain, shared-memory domain, and endianness. This remains
    untagged because the HOL theorem is polymorphic over word widths while
    this evaluator uses the RISC-V `BitVec 64` model. -/
theorem evalPanSemStateExpsWfShapeOfStateRel
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0]
    [OfNat (RiscV.Word 64) 1] [OfNat (RiscV.Word 64) 2]
    [OfNat (RiscV.Word 64) 3] [Add (RiscV.Word 64)]
    [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (context : PanToCrepProofContext (RiscV.Word 64))
    (targetLocals : FiniteMap Nat (PanWordLab (RiscV.Word 64)))
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (heval : evalPanSemStateExps source expressions = some values)
    (hstate : stateRel source target)
    (hlocals : localsRel context source.locals targetLocals) :
    panValueIsWfValues ([] : StructContext) values = true := by
  obtain ⟨_, _, _, hstructs, hglobalsEq, _, _, _, _, _⟩ := hstate
  have hlocalsWf : ∀ name value, source.locals name = some value →
      panValueIsWf ([] : StructContext) value = true := by
    intro name value hlookup
    exact localsRelWfShape context source.locals targetLocals name value
      hlocals hlookup
  have hglobalsWf : ∀ name value, source.globals name = some value →
      panValueIsWf ([] : StructContext) value = true := by
    intro name value hlookup
    rw [hglobalsEq, FEMPTY] at hlookup
    simp at hlookup
  have heval' : evalPanValueExps ([] : StructContext) source.locals
      source.globals source.memory source.baseAddress source.topAddress
      panSemBitVec64BytesInWord expressions
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some values := by
    simpa [evalPanSemStateExps, evalPanSemStateExp, evalPanValueExps,
      panSemBitVec64BytesInWord, hstructs] using heval
  exact evalPanValueExps_isWfShape ([] : StructContext) source.locals
    source.globals source.memory source.baseAddress source.topAddress
    panSemBitVec64BytesInWord hlocalsWf hglobalsWf expressions
    (some (panSemBitVec64MemoryAccess source)) values heval'

/-- Faithful port of Cake `locals_rel_lookup_ctxt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:527`). The HOL
    `OPT_MMAP (FLOOKUP t_locals) ns = SOME (flatten v)` is Lean's `List.mapM`
    result, and `is_wf_shape_nil` is `isWfShape []` at the translated value
    shape. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_lookup_ctxt"]
theorem localsRelLookupCtxt
    (context : PanToCrepProofContext α)
    (sourceLocals : FiniteMap String (PanValue α))
    (targetLocals : FiniteMap Nat (PanWordLab α)) (name : String) (value : PanValue α)
    (hrel : localsRel context sourceLocals targetLocals)
    (hlookup : FLOOKUP sourceLocals name = some value) :
    ∃ slots,
      FLOOKUP context.vars name = some (panValueShape [] value, slots) ∧
      slots.length = (panValueFlatten value).length ∧
      slots.mapM (FLOOKUP targetLocals) =
        some ((panValueFlatten value).map PanWordLab.word) ∧
      isWfShape [] (panValueShape [] value) = true := by
  obtain ⟨slots, values, hcontext, hmap, hflatten, hwf⟩ :=
    hrel.2.2 name value hlookup
  refine ⟨slots, hcontext, ?_, ?_, hwf⟩
  · calc slots.length = values.length :=
        list_mapM_length (FLOOKUP targetLocals) slots values hmap
      _ = ((panValueFlatten value).map PanWordLab.word).length :=
        congrArg List.length hflatten.symm
      _ = (panValueFlatten value).length := List.length_map PanWordLab.word
  · rw [hmap, ← hflatten]

/-- HOL `local_rel_gt_vmax_preserved`: a target local slot strictly above the
    proof context's maximum cannot occur in any source variable's slot list. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "local_rel_gt_vmax_preserved"]
theorem localRelGtVmaxPreserved
    (context : PanToCrepProofContext α)
    (sourceLocals : FiniteMap String (PanValue α))
    (targetLocals : FiniteMap Nat (PanWordLab α)) (slot : Nat)
    (newValue : PanWordLab α)
    (hrel : localsRel context sourceLocals targetLocals)
    (habove : context.vmax < slot) :
    localsRel context sourceLocals (FUPDATE targetLocals (slot, newValue)) := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  intro name value hlookup
  obtain ⟨names, values, hcontext, hvalues, hflatten, hwf⟩ :=
    hrel.2.2 name value hlookup
  refine ⟨names, values, hcontext, ?_, hflatten, hwf⟩
  rw [← hvalues]
  apply list_mapM_congr
  intro key hkey
  rw [FLOOKUP_update]
  have hle : key ≤ context.vmax :=
    hrel.2.1.2 name (panValueShape [] value) names hcontext key hkey
  have hne : slot ≠ key := by
    intro he
    subst key
    exact (Nat.not_lt_of_ge hle) habove
  simp [beq_eq_false_iff_ne.mpr hne]

/-- HOL `local_rel_le_zip_update_preserved`: replacing a source local by a
    shape-compatible value and writing its flattened words to the associated
    distinct slots preserves the finite-map locals relation. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "local_rel_le_zip_update_preserved"]
theorem localRelLeZipUpdatePreserved
    (context : PanToCrepProofContext α)
    (sourceLocals : FiniteMap String (PanValue α))
    (targetLocals : FiniteMap Nat (PanWordLab α))
    (name : String) (oldValue newValue : PanValue α)
    (shape : Shape) (slots : List Nat)
    (hrel : localsRel context sourceLocals targetLocals)
    (hsource : FLOOKUP sourceLocals name = some oldValue)
    (hcontext : FLOOKUP context.vars name = some (shape, slots))
    (hshape : panValueShape [] oldValue = panValueShape [] newValue)
    (hdistinct : slots.Nodup) :
    localsRel context (FUPDATE sourceLocals (name, newValue))
      (FUPDATE_LIST targetLocals
        (slots.zip ((panValueFlatten newValue).map PanWordLab.word))) := by
  obtain ⟨oldSlots, hlookup, hlen, _, hwf⟩ :=
    localsRelLookupCtxt context sourceLocals targetLocals name oldValue hrel hsource
  have hpair : (panValueShape [] oldValue, oldSlots) = (shape, slots) := by
    apply Option.some.inj
    rw [← hlookup, hcontext]
  have hslots : oldSlots = slots := congrArg Prod.snd hpair
  have hcontextOld : FLOOKUP context.vars name =
      some (panValueShape [] oldValue, slots) := by
    rw [← hslots]
    exact hlookup
  have hwfNew : isWfShape [] (panValueShape [] newValue) = true := by
    rw [← hshape]
    exact hwf
  have hlenNew : slots.length =
      ((panValueFlatten newValue).map PanWordLab.word).length := by
    rw [List.length_map]
    rw [← hslots, hlen, panValueFlatten_length_eq_shapeSize oldValue hwf,
      panValueFlatten_length_eq_shapeSize newValue hwfNew, hshape]
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  intro other value hsourceOther
  rw [FLOOKUP_update] at hsourceOther
  by_cases hsame : name = other
  · subst other
    simp at hsourceOther
    cases hsourceOther
    refine ⟨slots, (panValueFlatten newValue).map PanWordLab.word, ?_, ?_, rfl, hwfNew⟩
    · rw [← hshape]
      exact hcontextOld
    · exact opt_mmap_some_eq_zip_flookup slots targetLocals
        ((panValueFlatten newValue).map PanWordLab.word) hdistinct hlenNew
  · have hneq : (name == other) = false := beq_eq_false_iff_ne.mpr hsame
    simp [hneq] at hsourceOther
    obtain ⟨otherSlots, words, hother, hmap, hflat, hotherWf⟩ :=
      hrel.2.2 other value hsourceOther
    refine ⟨otherSlots, words, hother, ?_, hflat, hotherWf⟩
    have hdisjoint : ListDisjoint slots otherSlots := by
      intro slot hin hotherIn
      apply hsame
      exact hrel.1.2 name other (panValueShape [] oldValue)
        (panValueShape [] value) slots otherSlots hcontextOld hother
        ⟨slot, hin, hotherIn⟩
    rw [opt_mmap_disj_zip_flookup slots targetLocals otherSlots
      ((panValueFlatten newValue).map PanWordLab.word) hdisjoint hlenNew]
    exact hmap

/-- HOL `locals_rel_extend_new_var`: a fresh, well-shaped source local can be
    allocated in distinct target slots above the old context maximum. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_extend_new_var"]
theorem localsRelExtendNewVar
    (context : PanToCrepProofContext α)
    (sourceLocals : FiniteMap String (PanValue α))
    (targetLocals : FiniteMap Nat (PanWordLab α))
    (value : PanValue α) (name : String) (slots : List Nat)
    (hrel : localsRel context sourceLocals targetLocals)
    (hwf : isWfShape [] (panValueShape [] value) = true)
    (hdistinct : slots.Nodup)
    (hbounds : ∀ slot ∈ slots,
      context.vmax < slot ∧
        slot ≤ context.vmax + Shape.shapeSize (panValueShape [] value))
    (hlen : slots.length = Shape.shapeSize (panValueShape [] value)) :
    localsRel
      { context with
        vars := FUPDATE context.vars (name, (panValueShape [] value, slots))
        vmax := context.vmax + Shape.shapeSize (panValueShape [] value) }
      (FUPDATE sourceLocals (name, value))
      (FUPDATE_LIST targetLocals
        (slots.zip ((panValueFlatten value).map PanWordLab.word))) := by
  have hlenFlat : slots.length =
      ((panValueFlatten value).map PanWordLab.word).length := by
    rw [List.length_map, hlen, panValueFlatten_length_eq_shapeSize value hwf]
  have hdisjointOld : ∀ other shape otherSlots,
      FLOOKUP context.vars other = some (shape, otherSlots) →
      ListDisjoint slots otherSlots := by
    intro other shape otherSlots hlookup slot hin hother
    have hle : slot ≤ context.vmax :=
      hrel.2.1.2 other shape otherSlots hlookup slot hother
    exact (Nat.not_lt_of_ge hle) (hbounds slot hin).1
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro other shape otherSlots hlookup
      rw [FLOOKUP_update] at hlookup
      by_cases hsame : name = other
      · simp [beq_iff_eq.mpr hsame] at hlookup
        have hslots : slots = otherSlots := hlookup.2
        rw [← hslots]
        exact hdistinct
      · have hbeq : (name == other) = false := beq_eq_false_iff_ne.mpr hsame
        simp [hbeq] at hlookup
        exact hrel.1.1 other shape otherSlots hlookup
    · intro left right leftShape rightShape leftSlots rightSlots
        hleft hright hinter
      rw [FLOOKUP_update] at hleft hright
      by_cases hl : name = left
      · by_cases hr : name = right
        · exact hl.symm.trans hr
        · have hleq : (name == left) = true := beq_iff_eq.mpr hl
          have hreq : (name == right) = false := beq_eq_false_iff_ne.mpr hr
          simp [hleq] at hleft
          simp [hreq] at hright
          have hslots : slots = leftSlots := hleft.2
          obtain ⟨slot, hin, hother⟩ := hinter
          exact False.elim ((hdisjointOld right rightShape rightSlots hright)
            slot (hslots.symm ▸ hin) hother)
      · by_cases hr : name = right
        · have hleq : (name == left) = false := beq_eq_false_iff_ne.mpr hl
          have hreq : (name == right) = true := beq_iff_eq.mpr hr
          simp [hleq] at hleft
          simp [hreq] at hright
          have hslots : slots = rightSlots := hright.2
          obtain ⟨slot, hin, hother⟩ := hinter
          exact False.elim ((hdisjointOld left leftShape leftSlots hleft)
            slot (hslots.symm ▸ hother) hin)
        · have hleq : (name == left) = false := beq_eq_false_iff_ne.mpr hl
          have hreq : (name == right) = false := beq_eq_false_iff_ne.mpr hr
          simp [hleq] at hleft
          simp [hreq] at hright
          exact hrel.1.2 left right leftShape rightShape leftSlots rightSlots
            hleft hright hinter
  · refine ⟨Nat.zero_le _, ?_⟩
    intro other shape otherSlots hlookup slot hin
    rw [FLOOKUP_update] at hlookup
    by_cases hsame : name = other
    · simp [beq_iff_eq.mpr hsame] at hlookup
      have hslots : slots = otherSlots := hlookup.2
      exact (hbounds slot (hslots.symm ▸ hin)).2
    · have hbeq : (name == other) = false := beq_eq_false_iff_ne.mpr hsame
      simp [hbeq] at hlookup
      exact Nat.le_trans (hrel.2.1.2 other shape otherSlots hlookup slot hin)
        (Nat.le_add_right _ _)
  · intro other otherValue hlookupSource
    rw [FLOOKUP_update] at hlookupSource
    by_cases hsame : name = other
    · simp [beq_iff_eq.mpr hsame] at hlookupSource
      cases hlookupSource
      refine ⟨slots, (panValueFlatten value).map PanWordLab.word, ?_, ?_, rfl, hwf⟩
      · simp [FLOOKUP_update, beq_iff_eq.mpr hsame]
      · exact opt_mmap_some_eq_zip_flookup slots targetLocals
          ((panValueFlatten value).map PanWordLab.word) hdistinct hlenFlat
    · have hbeq : (name == other) = false := beq_eq_false_iff_ne.mpr hsame
      simp [hbeq] at hlookupSource
      obtain ⟨otherSlots, words, hcontext, hmap, hflat, hotherWf⟩ :=
        hrel.2.2 other otherValue hlookupSource
      refine ⟨otherSlots, words, ?_, ?_, hflat, hotherWf⟩
      · simpa [FLOOKUP_update, hbeq] using hcontext
      · rw [opt_mmap_disj_zip_flookup slots targetLocals otherSlots
          ((panValueFlatten value).map PanWordLab.word)
          (hdisjointOld other (panValueShape [] otherValue) otherSlots hcontext)
          hlenFlat]
        exact hmap

/-! Execute the finite-map compiler with the HOL proof context. Every map is
    passed directly to `compileProgHOL`; no queried-name projection to an
    `InfoMap` is performed. -/
def compileCodeRelProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α] (context : PanToCrepProofContext α) (program : Prog α) :
    CrepProg α :=
  compileProgHOL
    { vars := context.vars, funcs := context.funcs, eids := context.eids,
      vmax := context.vmax }
    program

/-! HOL-shaped `code_rel_def` relation (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:32`).
    It quantifies over every source code entry, requires localisation and the
    exact parameter/return-shape lookup in `ctxt.funcs`, derives parameter
    slots from `GENLIST I (size_of_shape (Comb shs))`, constructs the target
    context with `ctxt_fc`, and relates that entry to its compiled body.

    Its compiler conclusion routes to `compileProgHOL`, whose context is the
    original finite-map record. The `compile_def` tag is on the production
    wrapper `compileProgRiscV`, not on this helper. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_def"]
def codeRel [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α)) : Prop :=
  ∀ function variableShapes program returnShape,
    FLOOKUP sourceCode function = some (variableShapes, program, returnShape) →
      localisedProg program ∧
      FLOOKUP context.funcs function = some (variableShapes, returnShape) ∧
      let variables := variableShapes.map Prod.fst
      let shapes := variableShapes.map Prod.snd
      let names := List.range (Shape.shapeSize (.comb shapes))
      let nextContext := ctxtFc context.funcs context.eids variables shapes names
      FLOOKUP targetCode function = some
        (names, compileCodeRelProg nextContext program)

/-- Exact port of HOL `compile_exp_not_mem_load_glob`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2013`). The finite-map
    context fields are passed unchanged to `compileExpHOL`; the source code
    map is bridged from Pancake's executable association list as in the
    surrounding `codeRel` interface. The state, code, and locals relations
    remain explicit HOL premises, and the conclusion traverses the nested
    Crepe expressions with `crepExps`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_exp_not_mem_load_glob"]
theorem compileExpNotMemLoadGlob [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α) (expression : Exp α)
    (source : PanSemState α (FfiState σ)) (target : CrepRuntimeState α σ)
    (expressions : List (CrepExp α)) (shape : Shape) (address : BitVec 5)
    (hcompile : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax } expression = (expressions, shape))
    (_hstate : stateRel source target)
    (_hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (_hlocals : localsRel context source.locals target.locals) :
    CrepExp.loadGlob address ∉ expressions.flatMap crepExps := by
  have hsafe := compileExpHOL_not_mem_loadGlob
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
    expression address
  simpa only [hcompile] using hsafe

/-- HOL `code_rel_imp`: an entry in related source code is localised and
    has the corresponding function metadata and compiled target entry. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_imp"]
theorem codeRelImp [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (hrel : codeRel context sourceCode targetCode)
    (function : FunName) (variableShapes : List (VarName × Shape))
    (program : Prog α) (returnShape : Shape)
    (hlookup : FLOOKUP sourceCode function =
      some (variableShapes, program, returnShape)) :
    localisedProg program ∧
      FLOOKUP context.funcs function = some (variableShapes, returnShape) ∧
      let variables := variableShapes.map Prod.fst
      let shapes := variableShapes.map Prod.snd
      let names := List.range (Shape.shapeSize (.comb shapes))
      let nextContext := ctxtFc context.funcs context.eids variables shapes names
      FLOOKUP targetCode function = some
        (names, compileCodeRelProg nextContext program) :=
  hrel function variableShapes program returnShape hlookup

/-! Faithful port of HOL `code_rel_empty_locals` (`pan_to_crepProofScript.sml:96`).
Both code fields belong to their production semantic states. The HOL source
and target `empty_locals` definitions update only locals, leaving each code
map unchanged. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_empty_locals"]
theorem codeRelEmptyLocals [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α)
    (source : PanSemState α (FfiState σ))
    (target : CrepRuntimeState α σ)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code) :
    codeRel context (panSemCodeAsLookup (panEmptyLocals source).code)
      (clearCrepRuntimeLocals target).code := by
  simpa [panEmptyLocals, clearCrepRuntimeLocals] using hcode

/-- HOL `locals_id_update[local]`: writing the existing locals map into the
    production Crep state leaves that entire state unchanged. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_id_update"]
theorem crepLocalsIdUpdate (target : CrepRuntimeState α σ) :
    { target with locals := target.locals } = target := by
  cases target
  rfl

/-- HOL `first_compile_to_crep_all_distinct`: lowering function declarations
    changes bodies and parameter slots but preserves every function name in
    source order, so distinct source names stay distinct. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "first_compile_to_crep_all_distinct"]
theorem firstCompileToCrepAllDistinct
    (declarations : List (Decl (BitVec width)))
    (hdistinct : ((functionEntries declarations).map
      fun (name, _, _, _) => name).Nodup) :
    ((compileToCrepHOL declarations).map
      fun (name, _, _) => name).Nodup := by
  simpa [compileToCrepHOL, List.map_map, Function.comp_def] using hdistinct

/-- Exact port of HOL `first_compile_prog_all_distinct`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4556`). The original
    premise is distinct names from `functions prog`; `compile_prog` preserves
    those names while compiling each body and applying `compile_inl_top`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "first_compile_prog_all_distinct"]
theorem firstCompileProgAllDistinct {width : Nat}
    (declarations : List (Decl (BitVec width)))
    (hdistinct : ((functionEntries declarations).map
      fun (name, _, _, _) => name).Nodup) :
    ((compileProgTopHOL declarations).map
      fun (name, _, _) => name).Nodup := by
  have hnames :
      ((compileProgTopHOL declarations).map fun (name, _, _) => name) =
        ((compileToCrepHOL declarations).map fun (name, _, _) => name) := by
    simp [compileProgTopHOL, compileInlTopHOL, List.map_map,
      Function.comp_def]
  rw [hnames]
  exact firstCompileToCrepAllDistinct declarations hdistinct

end Flapjack
