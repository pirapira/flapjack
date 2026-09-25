import Flapjack.FiniteMap
import Flapjack.HolRef
import Flapjack.PanBst
import Flapjack.PanEmptyLocals
import Flapjack.PanLocalised
import Flapjack.PanValueFlatten
import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.DeclContextExact
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.ValueHOL
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

/-! Flapjack analogue of HOL `globals_lookup_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:435-438`). The lookup
    algorithm uses the same 5-bit indices, shape-size count, and optional-map
    traversal. It is deliberately untagged: HOL's input is a `panSem$value`
    and a `crepSem$state` (the direct probe instantiates an
    `((8),unit) crepSem$state` with `ValWord`/`RStruct` values), whereas this
    uses the production `PanValue α` with String-backed struct/field names,
    the untagged production `panSemShapeOf`/`Shape.shapeSize` in place of HOL
    `shape_of`/`size_of_shape`, and `CrepRuntimeState α σ`, which is only a
    production projection of the HOL state. The `names_as_string` qualifier
    cannot authorize the value/shape/state carriers, and its required
    same-module `NameRanged` witness cannot be stated for an
    `Option (List (PanWordLab α))` output. Direct HOL-EVAL rows
    (`lookup_success`, `lookup_missing`, `lookup_struct`) are recorded in
    `scripts/hol-probes/globals_lookup_probe.out` and reproduced by
    `Flapjack/Test/PanToCrepGlobalsLookupParity.lean`. Exact-carrier
    replacement is tracked by `flapjack-pxn.18.3.5.8.8`. -/
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
theorem panSemShapeOf_eq_panValueShape_nil (value : PanValue α) :
    panSemShapeOf value = panValueShape [] value := by
  induction value using panSemShapeOf.induct with
  | case1 _ => simp [panSemShapeOf, panValueShape]
  | case2 values ih =>
      simpa [panSemShapeOf, panValueShape] using ih
  | case3 _ _ => simp [panSemShapeOf, panValueShape]

/-- Flapjack bridge from HOL source `shape_of` over evaluated Call arguments
to the proof context's empty-struct shape function. The HOL premise
`EVERY is_wf_shape_v_nil args` uses exactly this context; named-struct values
do not satisfy that premise in the empty context. -/
theorem panSemShapeOfMapPanValueShapeNil (arguments : List (PanValue α)) :
    arguments.map panSemShapeOf = arguments.map (panValueShape []) := by
  exact List.map_congr_left (fun value _ => panSemShapeOf_eq_panValueShape_nil value)

/- Indexed-list form of the HOL Call premise
`LIST_REL (fun formal arg => formal.shape = shape_of arg) parameters arguments`.
The source-facing equality is kept untagged until the complete Call theorem is
ported. -/
/-! Flapjack support: `panShapeMatches` is an exact structural shape check, so
success entails equality of its two shape arguments. This is used to expose
the indexed formal/argument shape fact from `lookup_code`'s successful check. -/
mutual
  theorem panShapeMatches_eq (left right : Shape)
      (hmatch : panShapeMatches left right = true) : left = right := by
    cases left with
    | one => cases right <;> simp [panShapeMatches] at hmatch ⊢
    | named leftName =>
        cases right with
        | named rightName =>
            simp only [panShapeMatches] at hmatch
            have hname : leftName = rightName := beq_iff_eq.mp hmatch
            subst rightName
            rfl
        | one => simp [panShapeMatches] at hmatch
        | comb _ => simp [panShapeMatches] at hmatch
    | comb leftFields =>
        cases right with
        | comb rightFields =>
            simp only [panShapeMatches] at hmatch
            have hfields := panShapeListMatches_eq leftFields rightFields hmatch
            subst rightFields
            rfl
        | one => simp [panShapeMatches] at hmatch
        | named _ => simp [panShapeMatches] at hmatch

  theorem panShapeListMatches_eq (left right : List Shape)
      (hmatch : panShapeMatches.panShapeListMatches left right = true) :
      left = right := by
    cases left with
    | nil => cases right <;> simp [panShapeMatches.panShapeListMatches] at hmatch ⊢
    | cons leftHead leftTail =>
        cases right with
        | nil => simp [panShapeMatches.panShapeListMatches] at hmatch
        | cons rightHead rightTail =>
            simp only [panShapeMatches.panShapeListMatches, Bool.and_eq_true]
              at hmatch
            rcases hmatch with ⟨hhead, htail⟩
            rw [panShapeMatches_eq leftHead rightHead hhead,
              panShapeListMatches_eq leftTail rightTail htail]
end

theorem callParameterShapeMapEqPanSem
    (parameters : List (String × Shape)) (arguments : List (PanValue α))
    (hlength : parameters.length = arguments.length)
    (hshape : ∀ index (hparams : index < parameters.length)
      (hargs : index < arguments.length),
      (parameters[index]'hparams).2 = panSemShapeOf (arguments[index]'hargs)) :
    parameters.map Prod.snd = arguments.map panSemShapeOf := by
  apply List.ext_getElem
  · simp [hlength]
  · intro index hleft hright
    simpa only [List.getElem_map] using hshape index
      (by simpa using hleft) (by simpa using hright)

/-! A successful `globalsLookup` exposes each state-owned return-global cell.
This generic projection is useful when `exp_hdl` copies a multiword exception
payload into its handler local. -/
theorem globalsLookup_wordCell {state : CrepRuntimeState (RiscV.Word 64) σ}
    {value : PanValue (RiscV.Word 64)}
    (hwf : isWfShape [] (panSemShapeOf value) = true)
    (hlookup : globalsLookup state value =
      some ((panValueFlatten value).map PanWordLab.word))
    (index : Nat) (hindex : index < (panValueFlatten value).length) :
    state.globals (BitVec.ofNat 5 index) =
      some (.word ((panValueFlatten value)[index]'hindex)) := by
  have hwf' : isWfShape [] (panValueShape [] value) = true := by
    simpa [panSemShapeOf_eq_panValueShape_nil] using hwf
  have hshape : Shape.shapeSize (panSemShapeOf value) =
      (panValueFlatten value).length := by
    rw [panSemShapeOf_eq_panValueShape_nil]
    exact (panValueFlatten_length_eq_shapeSize value hwf').symm
  have hindexShape : index < Shape.shapeSize (panSemShapeOf value) := by
    omega
  have hpoint := list_mapM_getElem?
    (fun cellIndex => state.globals (BitVec.ofNat 5 cellIndex))
    (List.range (Shape.shapeSize (panSemShapeOf value)))
    ((panValueFlatten value).map PanWordLab.word) (by simpa [globalsLookup] using hlookup)
    index
  have hrange :
      (List.range (Shape.shapeSize (panSemShapeOf value)))[index]? = some index := by
    simp [hindexShape]
  have houtput : ((panValueFlatten value).map PanWordLab.word)[index]? =
      some (.word ((panValueFlatten value)[index]'hindex)) := by
    simp [hindex]
  rw [hrange] at hpoint
  simp only [Option.bind_some] at hpoint
  rw [houtput] at hpoint
  exact hpoint

/-- Flapjack analogue of HOL `flatten_nil_no_size[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:3001-3006`), which proves
    `is_wf_shape_nil (shape_of x) ⇒ (flatten x = [] ⇔ size_of_shape(shape_of x) = 0)`.
    This theorem mirrors that statement shape (`isWfShape [] ... = true` for
    `is_wf_shape_nil`, `panSemShapeOf` for `shape_of`, `panValueFlatten` for
    `flatten`, `Shape.shapeSize` for `size_of_shape`, `↔` for `⇔`), but its input
    is the production `PanValue α` carrier whose `nStruct` record/field names are
    `StructName`/`FieldName` = `String`, whereas HOL is over `panSem$v` with
    `stcname`/`fldname` = `mlstring`. These value/shape carrier differences
    exceed identifier representation, so `names_as_string` cannot qualify this
    analogue (no `NameRanged` witness applies either, since the conclusion is a
    biconditional over a flattened value, not a name). The withdrawn tag is
    recorded as a documented mismatch in `docs/HOL-THEOREM-MAP.json`; it is
    intentionally untagged. An exact MlString-carrier replacement is tracked by
    `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`). The statement is
    exercised against the original-domain fixtures in
    `Flapjack/Test/PanValueFlattenParity.lean` (notably
    `panValueFlatten_eq_nil_iff_shapeSize_eq_zero_fixture`), and HOL `flatten`
    output rows `word`/`record`/`named` live in
    `scripts/hol-probes/pan_flatten_probe.out`. -/
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
theorem loadShapeBytes_getElem_rel {width : Nat} [NeZero width]
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

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL
    `is_wf_shape_nil_length_flatten`: a word list chosen by the zero-size
    or positive-size branch has the size prescribed by the source value shape. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is over the
-- production `PanValue` carrier whose `nStruct` record/field names are
-- `StructName`/`FieldName` = `String`, while HOL `pan_to_crepProofScript.sml`
-- is over `panSem$v` with `stcname`/`fldname` = `mlstring`. The exact MlString
-- identifier carrier is tracked by `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`).
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

/-- Flapjack analogue of HOL `no_overlap_wrap_rt_some_all_distinct`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2461-2468`), which states
    `no_overlap fm ∧ wrap_rt (FLOOKUP fm r) = SOME (vsh, ns) ⇒ ALL_DISTINCT ns`.
    The statement shape is preserved (`noOverlap` for `no_overlap`, `wrapRt` for
    `wrap_rt`, `FLOOKUP` for `FLOOKUP`, `Nodup` for `ALL_DISTINCT`, same
    hypothesis/conclusion structure), but this declaration is deliberately
    untagged for substantive carrier differences: `fm` is keyed by
    `FunName`/`VarName` = `String` and stores the production `Shape` whose
    `Named` constructor carries a `String`, whereas HOL keys by
    `varname` = `mlstring` and stores `shape` whose `Named` carries an
    `mlstring`. The `names_as_string` qualifier cannot authorize the embedded
    `Shape` carrier, and no same-module `NameRanged` byte witness applies because
    the conclusion is `slots.Nodup`, a duplicate-freeness fact about a `Nat` list
    rather than a name. `docs/HOL-THEOREM-MAP.json` classifies this hol_name as
    `documented_mismatch`; the faithful exact-MlString carrier is tracked by
    `flapjack-pxn.18.3.5.8`. Oracle evidence for the two conjuncts is indirect:
    `scripts/hol-probes/pan_common_props_no_overlap_probe.out` pins
    `no_overlap` (rows `slot_nodup_x`, `slot_nodup_y`, `slots_disjoint`) and
    `scripts/hol-probes/wrap_rt_probe.out` pins `wrap_rt` (rows `none`,
    `empty_one`, `one_word`, `comb_empty`, `named`); there is no dedicated probe
    for this combined theorem. -/
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

/-- Flapjack analogue of HOL `mem_comp_field_lem`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:397-406`), which states
    `MEM x (FST (comp_field i l es)) ⇒ MEM x es ∨ x = Const 0w`. The clause
    structure is preserved, but this declaration is deliberately untagged for
    two substantive carrier differences: the production `Shape` embedded in
    `shapes` uses `String` for `Named` (HOL `shape` uses `mlstring`), and the
    expression payload is an arbitrary `α` word carrier rather than the HOL
    `crepLang$exp` indexed by a positive word width. `names_as_string` cannot
    authorize the `Shape`/expression carriers, and no `NameRanged` witness
    exists because the output is a membership disjunction, not a name. The
    exact-carrier `comp_field` port is the tagged `compFieldHOL`
    (`PanToCrep.lean`); a faithful exact port of this MEM lemma is tracked by
    `flapjack-pxn.18.3.5.8.8` (the production analogue is used by the
    `pan_to_crep` proof development). -/
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

/-- Production-carrier analogue of HOL `mem_comp_field`:
    every expression selected by `compileField` is from the flattened record
    input. It stays untagged because it uses production `Shape` (String-backed
    `Named`) and generic `PanValue α`; see the exact-carrier port below. -/
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

/-! The `mem_comp_field` proof helper over the faithful HOL carriers. -/
private theorem compFieldHOL_mem_of_index_lt {width : Nat} [NeZero width]
    (index : Nat) (shapes : List Flapjack.Pancake.PanLang.ShapeHOL)
    (expressions : List (CrepExpHOL width)) (candidate : CrepExpHOL width)
    (hindex : index < shapes.length)
    (hmem : candidate ∈ (compFieldHOL index shapes expressions).1) :
    candidate ∈ expressions := by
  induction shapes generalizing index expressions with
  | nil => simp at hindex
  | cons shape shapes ih =>
      cases index with
      | zero =>
          exact List.mem_of_mem_take (by simpa [compFieldHOL] using hmem)
      | succ index =>
          have hindex' : index < shapes.length := by simpa using hindex
          have hmem' : candidate ∈
              (compFieldHOL index shapes
                (expressions.drop
                  (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape))).1 := by
            simpa [compFieldHOL] using hmem
          exact List.mem_of_mem_drop (ih index
            (expressions.drop
              (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape)) hindex' hmem')

/-- Exact port of HOL `mem_comp_field`
    (`pan_to_crepProofScript.sml:666`). The value, shape, and expression
    carriers are `ValueHOL`, `ShapeHOL`, and `CrepExpHOL`; `hindex`, the
    flattened-size premise, the `comp_field` result equation, the record-shape
    equation, and the membership conclusion match HOL directly. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mem_comp_field"]
theorem memCompFieldHOLExact {width : Nat} [NeZero width]
    (shapes : List Flapjack.Pancake.PanLang.ShapeHOL) (index : Nat)
    (expressions : List (CrepExpHOL width))
    (selectedShape : Flapjack.Pancake.PanLang.ShapeHOL)
    (candidate : CrepExpHOL width) (selected : List (CrepExpHOL width))
    (values : List (ValueHOL width))
    (hindex : index < values.length)
    (_hlength : expressions.length =
      Flapjack.Pancake.PanLang.sizeOfShapeHOL
        (shapeOfHOLExact (.rStruct values)))
    (hcompiled : compFieldHOL index shapes expressions =
      (selected, selectedShape))
    (hshape : Flapjack.Pancake.PanLang.ShapeHOL.comb shapes =
      shapeOfHOLExact (.rStruct values))
    (hmem : candidate ∈ selected) :
    candidate ∈ expressions := by
  have hshapes : shapes = values.map shapeOfHOLExact :=
    Flapjack.Pancake.PanLang.ShapeHOL.comb.inj
      (by simpa [shapeOfHOLExact] using hshape)
  have hindex' : index < shapes.length := by
    simpa [hshapes] using hindex
  have hmem' : candidate ∈ (compFieldHOL index shapes expressions).1 := by
    simpa [hcompiled] using hmem
  exact compFieldHOL_mem_of_index_lt index shapes expressions candidate hindex' hmem'

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
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
def excpRel
    (compilerCodes : FiniteMap String α)
    (sourceShapes : FiniteMap String β) : Prop :=
  FDOM sourceShapes = FDOM compilerCodes ∧
    ∀ exception exception' code code',
      FLOOKUP compilerCodes exception = some code →
      FLOOKUP compilerCodes exception' = some code' →
      code = code' → exception = exception'

/-! ### HOL `get_eids_imp_excp_rel` (Flapjack-specific; tag withdrawn since
    `flapjack-pxn.18.3.5.7.2`)

    Flapjack-specific list support for the port below: membership in a zip
    yields aligned indices (HOL `MEM_ZIP`). -/
theorem mem_zip_getElem? {names : List α} {values : List β} {key : α} {value : β}
    (h : (key, value) ∈ names.zip values) :
    ∃ i : Nat, names[i]? = some key ∧ values[i]? = some value := by
  induction names generalizing values with
  | nil => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons val values =>
          rw [List.zip_cons_cons, List.mem_cons] at h
          rcases h with h | h
          · obtain ⟨rfl, rfl⟩ := h
            exact ⟨0, rfl, rfl⟩
          · obtain ⟨i, hni, hvi⟩ := ih h
            exact ⟨i + 1, by rw [List.getElem?_cons_succ]; exact hni,
              by rw [List.getElem?_cons_succ]; exact hvi⟩

/-- Flapjack-specific support: an exception table is no longer than the
    exception-identifier count of the same declaration list. -/
theorem exceptionEntries_length_le_sizeOfEids (pc : List (Decl (BitVec width))) :
    (exceptionEntries pc).length ≤ sizeOfEids pc := by
  induction pc with
  | nil => simp [exceptionEntries, sizeOfEids]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [exceptionEntries, sizeOfEids_cons, isExnDecl] <;> omega

/-- Flapjack-specific support: `BitVec.ofNat width` is injective below
    `2 ^ width`, which is where HOL's `LESS_MOD` step is used. -/
theorem bitVecOfNat_inj {width i j : Nat} (hi : i < 2 ^ width) (hj : j < 2 ^ width)
    (h : BitVec.ofNat width i = BitVec.ofNat width j) : i = j := by
  have hmod : i % 2 ^ width = j % 2 ^ width := by
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat] using this
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod

/-- Flapjack-specific unfolding of the `get_eids_from_decls`-shaped port (currently untagged). -/
theorem panToCrepGetEidsFromDeclsHOL_eq (declarations : List (Decl (BitVec width))) :
    panToCrepGetEidsFromDeclsHOL declarations =
      FUPDATE_LIST FEMPTY
        (((exceptionEntries declarations).map Prod.fst).zip
          ((List.range ((exceptionEntries declarations).map Prod.fst).length).map
            (BitVec.ofNat width))).reverse := rfl

/-- Flapjack-specific inverse lookup fact: a successful exception-code lookup
    comes from one of the zipped source entries. -/
theorem panToCrepGetEidsFromDeclsHOL_lookup_mem
    (declarations : List (Decl (BitVec width))) (exception : ExceptionId)
    (code : BitVec width)
    (h : FLOOKUP (panToCrepGetEidsFromDeclsHOL declarations) exception = some code) :
    (exception, code) ∈ ((exceptionEntries declarations).map Prod.fst).zip
        ((List.range ((exceptionEntries declarations).map Prod.fst).length).map
          (BitVec.ofNat width)) := by
  rw [panToCrepGetEidsFromDeclsHOL_eq declarations] at h
  rcases flookupFupdateList_mem_or_base (FEMPTY : FiniteMap ExceptionId (BitVec width))
      _ exception code h with ⟨entry, hentry, hkey, hvalue⟩ | hbase
  · rw [List.mem_reverse] at hentry
    have heq : entry = (exception, code) := by
      rw [← hkey, ← hvalue]
    rwa [heq] at hentry
  · exact absurd hbase (by simp)

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL `get_eids_imp_excp_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4656`): if the source
    exception map has the compiler's exception-code domain and the declaration
    list has fewer exception declarations than `2 ^ width`, then the compiler's
    code map is injective, matching HOL's `excp_rel`. The word type fixes the
    value conversion as in `get_eids_from_decls_def`; the HOL-vs-Lean
    equivalence is reviewed by comparing definitions (per SOUNDNESS), not
    proved by this theorem. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): source-shaped port of HOL
-- `get_eids_imp_excp_rel` (`pan_to_crepProofScript.sml:4656-4667`). The premise
-- `panLang$size_of_eids pc < dimword (:'a)` is mirrored by `sizeOfEids pc < 2 ^ width`
-- (with an executable `[NeZero width]`), and `FDOM seids = FDOM (get_eids_from_decls pc)`
-- / conclusion `excp_rel ...` by `FDOM ... = FDOM (panToCrepGetEidsFromDeclsHOL pc)` /
-- `excpRel ...`. The carriers differ: HOL quantifies a positive-width `'a decl list` whose
-- `get_eids_from_decls` returns an `(mlstring, 'a word) fmap`, while this statement uses the
-- production `Decl (BitVec width)` with `ExceptionId`/`VarName` = `String` and production
-- `Shape`, and `panToCrepGetEidsFromDeclsHOL : FiniteMap ExceptionId (BitVec width)`. The
-- result is an injectivity `Prop`; `names_as_string` cannot authorize the `Decl`/`Shape`/word
-- carriers and no `NameRanged` byte witness applies. Direct HOL-EVAL rows `empty_maps`,
-- `same_domain_injective`, `domain_mismatch`, `noninjective_compiler_codes` in
-- `scripts/hol-probes/excp_rel_probe.out` pin the HOL relation; the Lean statement is
-- exercised by the `example` and `getEidsGuard` in
-- `Flapjack/Test/PanToCrepCodeRelParity.lean:249-264` (registered `:443`). The map already
-- records `documented_mismatch`; exact MlString carrier tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem getEidsFromDeclsImpExcpRel [NeZero width]
    (seids : FiniteMap ExceptionId (BitVec width))
    (pc : List (Decl (BitVec width)))
    (hsize : sizeOfEids pc < 2 ^ width)
    (hdom : FDOM seids = FDOM (panToCrepGetEidsFromDeclsHOL pc)) :
    excpRel (panToCrepGetEidsFromDeclsHOL pc) seids := by
  refine ⟨hdom, ?_⟩
  intro exception exception' code code' hcode hcode' hcodeeq
  have hentry := panToCrepGetEidsFromDeclsHOL_lookup_mem pc exception code hcode
  have hentry' := panToCrepGetEidsFromDeclsHOL_lookup_mem pc exception' code' hcode'
  obtain ⟨i, hnamei, hvali⟩ := mem_zip_getElem? hentry
  obtain ⟨j, hnamej, hvalj⟩ := mem_zip_getElem? hentry'
  have hlti : i < ((exceptionEntries pc).map Prod.fst).length :=
    (List.getElem?_eq_some_iff.mp hnamei).1
  have hltj : j < ((exceptionEntries pc).map Prod.fst).length :=
    (List.getElem?_eq_some_iff.mp hnamej).1
  have hbound : ((exceptionEntries pc).map Prod.fst).length ≤ sizeOfEids pc := by
    simpa using exceptionEntries_length_le_sizeOfEids pc
  have hi : i < 2 ^ width := by omega
  have hj : j < 2 ^ width := by omega
  have hcodei : BitVec.ofNat width i = code := by
    rw [List.getElem?_map, List.getElem?_range hlti] at hvali
    exact Option.some.inj hvali
  have hcodej : BitVec.ofNat width j = code' := by
    rw [List.getElem?_map, List.getElem?_range hltj] at hvalj
    exact Option.some.inj hvalj
  have hij : i = j :=
    bitVecOfNat_inj hi hj (by rw [hcodei, hcodeeq, ← hcodej])
  have hnamej' : ((exceptionEntries pc).map Prod.fst)[i]? = some exception' := by
    rw [← hij] at hnamej
    exact hnamej
  rw [hnamei] at hnamej'
  exact Option.some.inj hnamej'

/-! HOL `ctxt_fc_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:25`).
    `FUPDATE_LIST` and `withShape` preserve the source definition's ZIP
    truncation and TAKE/DROP slicing, and `maxList` is Cake's `MAX_LIST`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
def ctxtFc
    (compilerFunctions : FiniteMap String (List (String × Shape) × Shape))
    (exceptionCodes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) : PanToCrepProofContext α :=
  { vars := FUPDATE_LIST FEMPTY
      (variables.zip (shapes.zip (withShape shapes names)))
    funcs := compilerFunctions
    eids := exceptionCodes
    vmax := maxList names }

/-- Flapjack-specific support for the HOL `MAX_LIST_i_genlist` step: dropping
    the first `n` entries of `List.range m` is the same as mapping `n + ·` over
    `List.range (m - n)` (used to line up `ctxt_fc`'s `with_shape` slices with
    `compileParamVars`'s per-parameter slot ranges). -/
theorem drop_range_map (m n : Nat) (h : n ≤ m) :
    (List.range m).drop n = (List.range (m - n)).map (fun index => n + index) := by
  rw [show m = n + (m - n) from (Nat.add_sub_cancel' h).symm]
  rw [List.range_add, List.drop_append_of_le_length (by simp [List.length_range])]
  simp

/-- Flapjack-specific bridge used by HOL `mk_ctxt_code_imp_code_rel`: the
    production parameter map built by `compileParamVars` and the proof-side
    `ctxt_fc` variable map agree after shifting the slot ranges by `offset`.
    This is the correspondence the HOL proof discharges with
    `gvs[ctxt_fc_def, make_vmap_def]`; HOL `make_vmap` is `panToCrepMakeVmapHOL`. -/
theorem compileParamVars_range_withShape (params : List (VarName × Shape)) (offset : Nat) :
    (compileParamVars params offset).1 =
      (params.map Prod.fst).zip
        ((params.map Prod.snd).zip
          (withShape (params.map Prod.snd)
            ((List.range (Shape.shapeSize (.comb (params.map Prod.snd)))).map
              (fun index => offset + index)))) := by
  induction params generalizing offset with
  | nil => simp [compileParamVars, withShape]
  | cons param params ih =>
      obtain ⟨name, shape⟩ := param
      simp only [compileParamVars, List.map_cons]
      rw [shapeSize_comb_cons]
      have htake :
          List.take (Shape.shapeSize shape)
              (List.map (fun index => offset + index)
                (List.range (Shape.shapeSize shape +
                  Shape.shapeSize (.comb (params.map Prod.snd))))) =
            List.map (fun index => offset + index)
              (List.range (Shape.shapeSize shape)) := by
        rw [← List.map_take, List.take_range]
        simp
      have hdrop :
          List.drop (Shape.shapeSize shape)
              (List.map (fun index => offset + index)
                (List.range (Shape.shapeSize shape +
                  Shape.shapeSize (.comb (params.map Prod.snd))))) =
            List.map (fun index => (offset + Shape.shapeSize shape) + index)
              (List.range (Shape.shapeSize (.comb (params.map Prod.snd)))) := by
        rw [← List.map_drop]
        rw [drop_range_map
          (Shape.shapeSize shape + Shape.shapeSize (.comb (params.map Prod.snd)))
          (Shape.shapeSize shape) (Nat.le_add_right _ _)]
        rw [Nat.add_sub_cancel_left]
        rw [List.map_map]
        congr 1
        funext index
        simp [Nat.add_assoc]
      simp only [withShape]
      rw [htake, hdrop, ih (offset + Shape.shapeSize shape)]
      simp only [List.zip_cons_cons]

/-- Flapjack-specific bridge used by HOL `mk_ctxt_code_imp_code_rel`: the
    production parameter map `panToCrepMakeVmapHOL` equals the `vars` field of
    the proof-side `ctxt_fc` context at the standard slot window. -/
theorem panToCrepMakeVmapHOL_eq_ctxtFcVars
    (params : List (VarName × Shape))
    (functions : FiniteMap FunName (List (VarName × Shape) × Shape))
    (exceptionCodes : FiniteMap ExceptionId α) :
    panToCrepMakeVmapHOL params =
      (ctxtFc functions exceptionCodes (params.map Prod.fst) (params.map Prod.snd)
        (panToCrepVars params)).vars := by
  simp only [panToCrepMakeVmapHOL, ctxtFc, panToCrepVars]
  rw [compileParamVars_range_withShape params 0]
  simp

/-! Indexed projection of the parameter variable map constructed by HOL
`ctxtFc`. This support lemma exposes the corresponding `withShape` slot window
without claiming the complete Call `locals_rel` theorem. -/
theorem ctxtFcVarsLookupGetElem
    (context : PanToCrepProofContext α) (parameters : List (String × Shape))
    (slots : List Nat) (index : Nat)
    (hdistinct : (parameters.map Prod.fst).Nodup)
    (hindex : index < parameters.length) :
    FLOOKUP
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots).vars
      ((parameters.map Prod.fst)[index]'(by simpa using hindex)) =
    some ((parameters.map Prod.snd)[index]'(by simpa using hindex),
      (withShape (parameters.map Prod.snd) slots)[index]'(by
        rw [withShape_length]
        simpa using hindex)) := by
  let names := parameters.map Prod.fst
  let shapes := parameters.map Prod.snd
  let slotGroups := withShape shapes slots
  have hindexNames : index < names.length := by simpa [names] using hindex
  have hdistinctNames : names.Nodup := by simpa [names] using hdistinct
  have hvaluesLength : names.length = (shapes.zip slotGroups).length := by
    simp [names, shapes, slotGroups, withShape_length]
  have hlookup := FLOOKUP_FUPDATE_LIST_zip_getElem names
    (shapes.zip slotGroups) FEMPTY index hdistinctNames hvaluesLength hindexNames
  simpa [ctxtFc, names, shapes, slotGroups] using hlookup

/-- HOL `ctxt_fc_funcs_eq`: constructing a function context preserves the
    supplied function map. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the HOL statement
-- (`pan_to_crepProofScript.sml:2295`) has no premises and is definitionally the
-- projection `(ctxt_fc cvs em vs shs ns).funcs = cvs`; the Lean projection
-- matches clause-for-clause but is keyed by the production identifiers
-- `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` with `String`-keyed finite maps
-- and production `Shape`), while HOL keys names by `funname`/`varname`/`eid` =
-- `mlstring` and shapes by `shape`. The `names_as_string` qualifier cannot cover
-- the `Shape` carrier, and no `NameRanged` byte witness exists because the
-- output is a finite map of function signatures, not a name. The direct HOL
-- EVAL row `functions_projection=T` is recorded in
-- `scripts/hol-probes/ctxt_fc_probe.out` and paired with the kernel-checked
-- fixture `ctxt_fc_funcs_eq_fixture` in
-- `Flapjack/Test/PanToCrepRelationsParity.lean`. The exact MlString identifier
-- carrier is tracked by `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`).
theorem ctxtFcFuncsEq
    (functions : FiniteMap String (List (String × Shape) × Shape))
    (codes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) :
    (ctxtFc functions codes variables shapes names).funcs = functions := rfl

/-- HOL `ctxt_fc_eids_eq`: constructing a function context preserves the
    supplied exception-code map. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem ctxtFcEidsEq
    (functions : FiniteMap String (List (String × Shape) × Shape))
    (codes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) :
    (ctxtFc functions codes variables shapes names).eids = codes := rfl

/-- HOL `ctxt_fc_vmax`: the constructed context's maximum slot is the
    maximum of the supplied slot list. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL
-- `pan_to_crepProofScript.sml:2307-2312` proves
-- `(ctxt_fc ctxt.funcs em vs shs ns).vmax = MAX_LIST ns` with no premises
-- (`rw [ctxt_fc_def]`); this theorem has the same no-premises projection shape
-- and is likewise definitional (`rfl`), but is keyed by the production
-- identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are
-- `String`-keyed) with production `Shape`, while HOL keys names by
-- `funname`/`varname`/`eid` = `mlstring` and slots by `shape`. The
-- `names_as_string` qualifier cannot cover the `Shape` carrier, and no
-- `NameRanged` byte witness exists because the output is a `num` slot bound,
-- not a name. Direct HOL-EVAL rows `vmax_nonempty_list=T`/`vmax_empty_list=T`
-- in `scripts/hol-probes/ctxt_fc_probe.out` are paired with the kernel-checked
-- instances `ctxt_fc_vmax_nonempty_fixture`/`ctxt_fc_vmax_empty_fixture` and
-- `ctxtFcVmaxGuard` in `Flapjack/Test/PanToCrepRelationsParity.lean`. The exact
-- MlString carrier is tracked by `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`); this analogue remains deliberately untagged.
theorem ctxtFcVmax
    (context : PanToCrepProofContext α) (codes : FiniteMap String α)
    (variables : List String) (shapes : List Shape) (names : List Nat) :
    (ctxtFc context.funcs codes variables shapes names).vmax = maxList names := rfl

/-- HOL `ctxt_max_el_leq`: a slot selected from a variable's flattened name
    list does not exceed the context's maximum slot. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem ctxtMaxGetElemLe
    (context : PanToCrepProofContext α) (varName : String)
    (shape : Shape) (names : List Nat) (index : Nat)
    (hmax : ctxtMax context.vmax context.vars)
    (hlookup : FLOOKUP context.vars varName = some (shape, names))
    (hindex : index < names.length) :
    names[index] ≤ context.vmax := by
  exact hmax.2 varName shape names hlookup names[index] (List.getElem_mem hindex)

/-- HOL `slc_def` (`pan_to_crepProofScript.sml:2313-2315`):
    `slc vshs args = FEMPTY |++ ZIP (MAP FST vshs, args)`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn, bead flapjack-4ac.5.36):
-- the production `slc` keys by `VarName = String` and stores the raw `PanValue α`
-- payload, while HOL keys by `varname = mlstring` and stores `'a v` (whose `Val`
-- constructor carries `'a word_lab`). The `names_as_string` qualifier cannot
-- authorize the value carrier, and `PanValue` is explicitly not statement-exact
-- (`.word` stores `α`, not `'a word_lab`). Faithful exact port tracked by
-- `flapjack-pxn.18.3.5.8` (MlString names) and `flapjack-0lj` (word_lab).
-- Untagged non-Proofs def, so no theorem-map entry is possible.
def slc (parameters : List (String × Shape))
    (arguments : List (PanValue α)) : FiniteMap String (PanValue α) :=
  FUPDATE_LIST FEMPTY ((parameters.map Prod.fst).zip arguments)

/-- HOL `tlc_def` (`pan_to_crepProofScript.sml:2317-2319`):
    `tlc ns args = FEMPTY |++ ZIP (ns, FLAT (MAP flatten args))`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag withdrawn, bead flapjack-4ac.5.37):
-- HOL `tlc` returns a finite map to `'a word_lab` (`flatten : 'a v -> 'a word_lab list`),
-- while production `tlc` returns `FiniteMap Nat α`, dropping the `PanWordLab.word`
-- wrapper (the keys `Nat`/`num` agree). `PanValue` is explicitly not statement-exact
-- (`.word` stores `α`, not `'a word_lab`), and no qualifier authorizes this element
-- carrier. The untagged `tlcWordLab` below is the `PanWordLab`-carrying analogue;
-- a faithful exact port is tracked by `flapjack-0lj` (word_lab) / `flapjack-pxn.18.3.5.8`.
def tlc (slots : List Nat) (arguments : List (PanValue α)) :
    FiniteMap Nat α :=
  FUPDATE_LIST FEMPTY (slots.zip (arguments.flatMap panValueFlatten))

/-- HOL `slc_tlc_rw`: both local-map constructor names unfold to their
    original finite-map updates. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem slcTlcRw
    (parameters : List (String × Shape)) (slots : List Nat)
    (arguments : List (PanValue α)) :
    (FUPDATE_LIST FEMPTY ((parameters.map Prod.fst).zip arguments) =
      slc parameters arguments) ∧
    (FUPDATE_LIST FEMPTY (slots.zip (arguments.flatMap panValueFlatten)) =
      tlc slots arguments) := ⟨rfl, rfl⟩

private theorem updatePanValueMap_eq_FUPDATE
    (locals : VarName → Option (PanValue α)) (name : VarName)
    (value : PanValue α) :
    updatePanValueMap locals name value = FUPDATE locals (name, value) := by
  funext key
  by_cases hkey : key = name
  · subst key
    simp [updatePanValueMap, FUPDATE]
  · have hkeyName : (key == name) = false :=
      beq_eq_false_iff_ne.mpr hkey
    have hnameKey : (name == key) = false :=
      beq_eq_false_iff_ne.mpr (Ne.symm hkey)
    simp [updatePanValueMap, FUPDATE, hkeyName, hnameKey]

private theorem updatePanValueMap_fold_eq_FUPDATE_LIST
    (entries : List (VarName × PanValue α))
    (locals : VarName → Option (PanValue α)) :
    entries.foldl
        (fun current (name, value) => updatePanValueMap current name value) locals =
      FUPDATE_LIST locals entries := by
  induction entries generalizing locals with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.foldl_cons, FUPDATE_LIST]
      rw [updatePanValueMap_eq_FUPDATE, ih]
      rfl

/-! Flapjack source-entry bridge: the actual evaluator binder and HOL `slc`
produce extensionally identical source-local maps. -/
theorem bindPanValueParameters_eq_slc
    (parameters : List (String × Shape)) (arguments : List (PanValue α))
    (hlength : parameters.length = arguments.length) :
    bindPanValueParameters (parameters.map Prod.fst) arguments =
      some (slc parameters arguments) := by
  have hnamesLength : (parameters.map Prod.fst).length = arguments.length := by
    simpa using hlength
  unfold bindPanValueParameters
  have hfold := updatePanValueMap_fold_eq_FUPDATE_LIST
    ((parameters.map Prod.fst).zip arguments)
    (FEMPTY : VarName → Option (PanValue α))
  have hlengthCheck :
      ¬ ((parameters.map Prod.fst).length != arguments.length) := by
    simp [hnamesLength]
  rw [if_neg hlengthCheck]
  apply congrArg some
  have hempty : (FEMPTY : VarName → Option (PanValue α)) = fun _ => none := rfl
  rw [hempty] at hfold
  change _ = FUPDATE_LIST (FEMPTY : VarName → Option (PanValue α))
    ((parameters.map Prod.fst).zip arguments)
  exact hfold

/-! A successful source-local lookup after `slc` comes from one of the zipped
formal/argument pairs. This Flapjack finite-map support lemma is used to expose
the source-side parameter index in the Call-entry `locals_rel` proof.

**Not the HOL `call_preserve_state_code_locals_rel` port.**
`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2355` concludes a four-way
conjunction `state_rel (dec_clock s with locals := slc vshs args) (... tlc ...)
∧ code_rel (ctxt_fc ...) ... ∧ excp_rel (ctxt_fc ...).eids ... ∧ locals_rel
(ctxt_fc ...) ...`, under HOL hypotheses `LIST_REL (λvshape arg. SND vshape =
shape_of arg)`, `state_rel`, `code_rel`, `excp_rel`, `locals_rel`, `FLOOKUP
s.code`/`t.code`, `FLOOKUP ctxt.funcs`, `ALL_DISTINCT ns`,
`size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args))`, and
`EVERY is_wf_shape_v_nil args`. No Lean declaration claims that statement:
every relation it mentions is a documented carrier mismatch — `state_rel` /
`code_rel` / `excp_rel` / `locals_rel` relate production `PanSemState` /
`CrepRuntimeState` with `VarName`/`FunName`/`ExceptionId`/`StructName = String`,
`PanValue α` and production `Shape`, whereas HOL relates `mlstring`-keyed states,
`panSem$v`, and `shape` with `'a word_lab` payloads. `slc`/`tlc` compound the gap
(`slc` keys by `String`; `tlc` returns `FiniteMap Nat α` not `word_lab`). The
theorem must not be `@[hol]`-tagged until the exact carrier ports land; faithful
port dependencies: `flapjack-pxn.18.3.5.8` (MlString carriers) and
`flapjack-0lj` (word_lab); the Call-case correctness work is tracked by
`flapjack-pxn.18.4.4`. The support lemmas below cover only individual
`slc`/`ctxt_fc`/`withShape` ingredients, not the HOL theorem. -/
theorem slcLookupGetElem
    (parameters : List (String × Shape)) (arguments : List (PanValue α))
    (name : String) (value : PanValue α)
    (hlookup : FLOOKUP (slc parameters arguments) name = some value) :
    ∃ i, ∃ (hi : i < (parameters.map Prod.fst).length),
      ∃ (harg : i < arguments.length),
      (parameters.map Prod.fst)[i]'hi = name ∧ arguments[i]'harg = value := by
  have hsource := flookupFupdateList_mem_or_base
    (FEMPTY : FiniteMap String (PanValue α))
    ((parameters.map Prod.fst).zip arguments) name value (by
      simpa [slc] using hlookup)
  rcases hsource with hentry | hempty
  · obtain ⟨entry, hmem, hname, hvalue⟩ := hentry
    obtain ⟨i, hi, harg, hnameIndex, hvalueIndex⟩ :=
      mem_zip_getElem (parameters.map Prod.fst) arguments entry hmem
    refine ⟨i, ⟨hi, ⟨harg, ?_⟩⟩⟩
    constructor
    · simpa [hname] using hnameIndex
    · simpa [hvalue] using hvalueIndex
  · simp [FLOOKUP_empty] at hempty

/-! Partitioning the concatenated flattenings by each argument's shape
reconstructs the per-argument flattenings. This supports matching the
`withShape` slot windows in HOL `ctxtFc` to their source arguments. -/
theorem withShape_mapPanValueFlatten (arguments : List (PanValue α))
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panValueShape [] value) = true) :
    withShape (arguments.map (panValueShape []))
        ((arguments.map panValueFlatten).flatten) =
      arguments.map panValueFlatten := by
  induction arguments with
  | nil => simp [withShape]
  | cons value values ih =>
      have hwfValue := hwf value (by simp)
      have hwfValues : ∀ other, other ∈ values →
          isWfShape [] (panValueShape [] other) = true := by
        intro other hmem
        exact hwf other (by simp [hmem])
      have hlength := panValueFlatten_length_eq_shapeSize value hwfValue
      have htail := ih hwfValues
      simp only [List.map_cons, List.flatten_cons]
      rw [withShape]
      have htake :
          (panValueFlatten value ++ (values.map panValueFlatten).flatten).take
              (Shape.shapeSize (panValueShape [] value)) = panValueFlatten value := by
        rw [← hlength]
        rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      have hdrop :
          (panValueFlatten value ++ (values.map panValueFlatten).flatten).drop
              (Shape.shapeSize (panValueShape [] value)) =
            (values.map panValueFlatten).flatten := by
        rw [← hlength]
        simp
      rw [htake, hdrop, htail]

/-- Source-facing form of `withShape_mapPanValueFlatten`: its shapes and
well-formedness premise use the HOL `panSem$shape_of` and
`is_wf_shape_v_nil` boundary. -/
theorem withShape_mapPanValueFlattenOfPanSem
    (arguments : List (PanValue α))
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true) :
    withShape (arguments.map panSemShapeOf)
        ((arguments.map panValueFlatten).flatten) =
      arguments.map panValueFlatten := by
  rw [panSemShapeOfMapPanValueShapeNil]
  apply withShape_mapPanValueFlatten
  intro value hmem
  simpa [panSemShapeOf_eq_panValueShape_nil] using hwf value hmem

/-! These list facts support the generated `ctxtFc` invariants: each
`withShape` slot group inherits duplicate-freedom and membership from its flat
source slot list. -/
theorem withShapeGetElemNodupOfSlotsNodup (shapes : List Shape) (slots : List Nat)
    (index : Nat) (hslots : slots.Nodup)
    (hsize : slots.length = Shape.shapeSize (.comb shapes))
    (hindex : index < shapes.length) :
    ((withShape shapes slots)[index]'(by rw [withShape_length]; exact hindex)).Nodup := by
  rw [withShape_getElem_eq_take_drop shapes slots index hsize hindex]
  exact (List.take_sublist _ _).nodup ((List.drop_sublist _ _).nodup hslots)

theorem withShapeGetElemMemOfSlotsMem (shapes : List Shape) (slots : List Nat)
    (index slot : Nat) (hsize : slots.length = Shape.shapeSize (.comb shapes))
    (hindex : index < shapes.length)
    (hmem : slot ∈ (withShape shapes slots)[index]'
      (by rw [withShape_length]; exact hindex)) :
    slot ∈ slots := by
  rw [withShape_getElem_eq_take_drop shapes slots index hsize hindex] at hmem
  exact (List.drop_sublist _ _).subset ((List.take_sublist _ _).subset hmem)

theorem withShapeMap (shapes : List Shape) (values : List α) (f : α → β) :
    withShape shapes (values.map f) = (withShape shapes values).map (List.map f) := by
  induction shapes generalizing values with
  | nil => simp [withShape]
  | cons shape shapes ih =>
      simp only [withShape, List.map_cons, List.map_take]
      rw [← List.map_drop]
      congr 1
      exact ih (values.drop (Shape.shapeSize shape))

/-- The generated `ctxtFc` variable map has HOL `no_overlap` when its flat
target slot list is duplicate-free. This is untagged support for
`call_preserve_state_code_locals_rel`. -/
theorem ctxtFcNoOverlapOfDistinctSlots
    (context : PanToCrepProofContext α) (parameters : List (String × Shape))
    (slots : List Nat) (hslots : slots.Nodup)
    (hsize : slots.length = Shape.shapeSize (.comb (parameters.map Prod.snd))) :
    noOverlap (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
      (parameters.map Prod.snd) slots).vars := by
  let names := parameters.map Prod.fst
  let shapes := parameters.map Prod.snd
  let groups := withShape shapes slots
  let entries := names.zip (shapes.zip groups)
  have hnamesShape : names.length = shapes.length := by simp [names, shapes]
  have hshapeGroups : shapes.length = groups.length := by
    simp [groups, withShape_length]
  have hvars :
      (ctxtFc context.funcs context.eids names shapes slots).vars =
        FUPDATE_LIST FEMPTY entries := by
    simp [ctxtFc, entries, names, shapes, groups]
  have hsourceSize : slots.length = Shape.shapeSize (.comb shapes) := by
    simpa [shapes] using hsize
  unfold noOverlap
  constructor
  · intro name shape ns hlookup
    rw [hvars] at hlookup
    dsimp only [entries] at hlookup
    rcases flookupFupdateList_mem_or_base FEMPTY
      (names.zip (shapes.zip groups)) name (shape, ns) hlookup with hmem | hbase
    · rcases hmem with ⟨entry, hentry, hname, hvalue⟩
      rcases entry with ⟨entryName, entryValue⟩
      rcases entryValue with ⟨entryShape, entrySlots⟩
      have hentryEq : (entryName, (entryShape, entrySlots)) = (name, (shape, ns)) := by
        cases hname
        cases hvalue
        rfl
      rw [hentryEq] at hentry
      have hzipMem : (name, (shape, ns)) ∈ names.zip (shapes.zip groups) := by
        simpa using hentry
      obtain ⟨index, hindexName, hindexPair, hnameAt, hpairAt⟩ :=
        mem_zip_getElem names (shapes.zip groups) (name, (shape, ns)) hzipMem
      have hindexZip : index < (shapes.zip groups).length := hindexPair
      rw [List.length_zip] at hindexZip
      have hindexShape : index < shapes.length := by omega
      have hindexGroup : index < groups.length := by omega
      have hpairAt' :
          (shapes[index]'hindexShape, groups[index]'hindexGroup) = (shape, ns) := by
        simpa using hpairAt
      have hslotsAt : groups[index]'hindexGroup = ns := congrArg Prod.snd hpairAt'
      rw [← hslotsAt]
      exact withShapeGetElemNodupOfSlotsNodup shapes slots index hslots hsourceSize hindexShape
    · simp at hbase
  · intro name other shape otherShape ns otherSlots hnameLookup hotherLookup ⟨slot, hslot, hotherSlot⟩
    by_cases hnamesEq : name = other
    · exact hnamesEq
    rw [hvars] at hnameLookup hotherLookup
    dsimp only [entries] at hnameLookup hotherLookup
    have hiLookup := flookupFupdateList_mem_or_base FEMPTY
      (names.zip (shapes.zip groups)) name (shape, ns) hnameLookup
    have hjLookup := flookupFupdateList_mem_or_base FEMPTY
      (names.zip (shapes.zip groups)) other (otherShape, otherSlots) hotherLookup
    rcases hiLookup with ⟨iEntry, hnameEntry, hnameKey, hnameValue⟩ | hbase
    · rcases hjLookup with ⟨jEntry, hotherEntry, hotherKey, hotherValue⟩ | hotherBase
      · rcases iEntry with ⟨iName, iPair⟩
        rcases iPair with ⟨iShape, iSlots⟩
        rcases jEntry with ⟨jName, jPair⟩
        rcases jPair with ⟨jShape, jSlots⟩
        have hiEntryEq : (iName, (iShape, iSlots)) = (name, (shape, ns)) := by
          cases hnameKey
          cases hnameValue
          rfl
        have hjEntryEq : (jName, (jShape, jSlots)) = (other, (otherShape, otherSlots)) := by
          cases hotherKey
          cases hotherValue
          rfl
        rw [hiEntryEq] at hnameEntry
        rw [hjEntryEq] at hotherEntry
        obtain ⟨i, hiName, hiPair, hiNameAt, hiPairAt⟩ :=
          mem_zip_getElem names (shapes.zip groups) (name, (shape, ns)) hnameEntry
        obtain ⟨j, hjName, hjPair, hjNameAt, hjPairAt⟩ :=
          mem_zip_getElem names (shapes.zip groups) (other, (otherShape, otherSlots)) hotherEntry
        have hiPairBound : i < min shapes.length groups.length := by
          simpa [List.length_zip] using hiPair
        have hjPairBound : j < min shapes.length groups.length := by
          simpa [List.length_zip] using hjPair
        have hiShape : i < shapes.length := Nat.lt_of_lt_of_le hiPairBound (Nat.min_le_left ..)
        have hjShape : j < shapes.length := Nat.lt_of_lt_of_le hjPairBound (Nat.min_le_left ..)
        have hiGroup : i < groups.length := Nat.lt_of_lt_of_le hiPairBound (Nat.min_le_right ..)
        have hjGroup : j < groups.length := Nat.lt_of_lt_of_le hjPairBound (Nat.min_le_right ..)
        have hiPair' : (shapes[i]'hiShape, groups[i]'hiGroup) = (shape, ns) := by
          simpa using hiPairAt
        have hjPair' : (shapes[j]'hjShape, groups[j]'hjGroup) = (otherShape, otherSlots) := by
          simpa using hjPairAt
        have hns : groups[i]'hiGroup = ns := congrArg Prod.snd hiPair'
        have hotherNs : groups[j]'hjGroup = otherSlots := congrArg Prod.snd hjPair'
        have hindexNe : i ≠ j := by
          intro heq
          subst j
          exact hnamesEq (calc
            name = names[i]'hiName := hiNameAt.symm
            _ = other := hjNameAt)
        have hdisjoint := listDisjoint_withShape_getElem shapes slots i j hslots
          hiShape hjShape hindexNe hsourceSize
        exact False.elim (hdisjoint slot (hns.symm ▸ hslot) (hotherNs.symm ▸ hotherSlot))
      · simp at hotherBase
    · simp at hbase

/-- The `ctxt_fc` slot bound is `MAX_LIST slots`, as in HOL `ctxt_fc_vmax`;
every generated component is a slice of that flat slot list. -/
theorem ctxtFcCtxtMaxOfSlots
    (context : PanToCrepProofContext α) (parameters : List (String × Shape))
    (slots : List Nat)
    (hsize : slots.length = Shape.shapeSize (.comb (parameters.map Prod.snd))) :
    ctxtMax (maxList slots)
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots).vars := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro name shape ns hlookup slot hslot
  let names := parameters.map Prod.fst
  let shapes := parameters.map Prod.snd
  let groups := withShape shapes slots
  let entries := names.zip (shapes.zip groups)
  have hsourceSize : slots.length = Shape.shapeSize (.comb shapes) := by
    simpa [shapes] using hsize
  have hlookup' : FLOOKUP (FUPDATE_LIST FEMPTY entries) name = some (shape, ns) := by
    simpa [ctxtFc, names, shapes, groups, entries] using hlookup
  rcases flookupFupdateList_mem_or_base FEMPTY entries name (shape, ns) hlookup' with
      ⟨entry, hentry, hname, hvalue⟩ | hbase
  · rcases entry with ⟨entryName, entryValue⟩
    rcases entryValue with ⟨entryShape, entrySlots⟩
    have hentryEq : (entryName, (entryShape, entrySlots)) = (name, (shape, ns)) := by
      cases hname
      cases hvalue
      rfl
    rw [hentryEq] at hentry
    obtain ⟨index, hindexName, hindexPair, hnameAt, hpairAt⟩ :=
      mem_zip_getElem names (shapes.zip groups) (name, (shape, ns)) hentry
    have hpairBound : index < min shapes.length groups.length := by
      simpa [List.length_zip] using hindexPair
    have hindexShape : index < shapes.length :=
      Nat.lt_of_lt_of_le hpairBound (Nat.min_le_left ..)
    have hindexGroup : index < groups.length :=
      Nat.lt_of_lt_of_le hpairBound (Nat.min_le_right ..)
    have hpairAt' :
        (shapes[index]'hindexShape, groups[index]'hindexGroup) = (shape, ns) := by
      simpa using hpairAt
    have hslotsAt : groups[index]'hindexGroup = ns := congrArg Prod.snd hpairAt'
    have hslotGroup : slot ∈ groups[index]'hindexGroup := hslotsAt.symm ▸ hslot
    have hslotFlat := withShapeGetElemMemOfSlotsMem shapes slots index slot
      hsourceSize hindexShape hslotGroup
    exact maxList_ge_of_mem slots slot hslotFlat
  · simp at hbase

/-! The target `tlc` map returns exactly the flattened words in the slot window
assigned by `withShape` to a given well-formed argument. This is the target
half of the Call formal/flattened `locals_rel` proof. -/
theorem tlcWithShapeGetElemMap
    (arguments : List (PanValue α)) (slots : List Nat) (index : Nat)
    (hdistinct : slots.Nodup)
    (hslotsLength : slots.length = (arguments.flatMap panValueFlatten).length)
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panValueShape [] value) = true)
    (hindex : index < arguments.length) :
    ((withShape (arguments.map (panValueShape [])) slots)[index]'(by
      rw [withShape_length]
      simpa using hindex)).mapM (FLOOKUP (tlc slots arguments)) =
      some (panValueFlatten (arguments[index]'hindex)) := by
  let shapes := arguments.map (panValueShape [])
  let words := arguments.flatMap panValueFlatten
  have hshapeSize : Shape.shapeSize (.comb shapes) = words.length := by
    simpa [shapes, words, Function.comp_def, List.length_flatMap] using
      shapeSize_comb_map_panValueShape_eq_flatten_length arguments hwf
  have hslotsShape : slots.length = Shape.shapeSize (.comb shapes) :=
    hslotsLength.trans hshapeSize.symm
  have hindexShapes : index < shapes.length := by simpa [shapes] using hindex
  have hslotsWindow := withShape_getElem_eq_take_drop shapes slots index
    hslotsShape hindexShapes
  have hwordsWindow := withShape_getElem_eq_take_drop shapes words index
    hshapeSize.symm hindexShapes
  have hwhole : slots.mapM (FLOOKUP (tlc slots arguments)) = some words := by
    have hlookup : FLOOKUP (tlc slots arguments) =
        fun key => FLOOKUP (FUPDATE_LIST FEMPTY
          (slots.zip (arguments.flatMap panValueFlatten))) key := by
      funext key
      unfold tlc
      rfl
    rw [hlookup]
    simpa [words] using
      (opt_mmap_some_eq_zip_flookup slots FEMPTY words hdistinct hslotsLength)
  have hwindow := list_mapM_takeDrop_of_success (FLOOKUP (tlc slots arguments))
    slots words (Shape.shapeSize (.comb (shapes.take index)))
    (Shape.shapeSize (shapes[index]'hindexShapes)) hwhole
  have hpartition := withShape_mapPanValueFlatten arguments hwf
  have hgroupBound : index < (withShape shapes words).length := by
    rw [withShape_length]
    exact hindexShapes
  have hpartitionIndex :
      (withShape shapes words)[index]'hgroupBound =
        panValueFlatten (arguments[index]'hindex) := by
    have hpartition' : withShape shapes words = arguments.map panValueFlatten := by
      simpa only [shapes, words, List.flatten_eq_flatMap, List.flatMap_map,
        id] using hpartition
    have hindexMap : index < (arguments.map panValueFlatten).length := by
      simpa only [List.length_map] using hindex
    have hindexed := congrArg (fun groups : List (List α) => groups[index]?) hpartition'
    have hindexedLeft : (withShape shapes words)[index]? =
        some ((withShape shapes words)[index]'hgroupBound) :=
      List.getElem?_eq_getElem hgroupBound
    have hindexedRight : (arguments.map panValueFlatten)[index]? =
        some ((arguments.map panValueFlatten)[index]'hindexMap) :=
      List.getElem?_eq_getElem hindexMap
    rw [hindexedLeft, hindexedRight] at hindexed
    have hmapElem : (arguments.map panValueFlatten)[index]'hindexMap =
        panValueFlatten (arguments[index]'hindex) := by
      rw [List.getElem_map]
    exact (Option.some.inj hindexed).trans hmapElem
  rw [hslotsWindow, hwindow]
  rw [← hwordsWindow, hpartitionIndex]

/-- Source-facing `tlc` slot projection. The slot grouping is expressed with
HOL `panSem$shape_of`, and its well-formedness premise is the empty-context
`is_wf_shape_v_nil` condition from the Call theorem. -/
theorem tlcWithShapeGetElemMapOfPanSem
    (arguments : List (PanValue α)) (slots : List Nat) (index : Nat)
    (hdistinct : slots.Nodup)
    (hslotsLength : slots.length = (arguments.flatMap panValueFlatten).length)
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true)
    (hindex : index < arguments.length) :
    ((withShape (arguments.map panSemShapeOf) slots)[index]'(by
      rw [withShape_length]
      simpa using hindex)).mapM (FLOOKUP (tlc slots arguments)) =
      some (panValueFlatten (arguments[index]'hindex)) := by
  have hwf' : ∀ value, value ∈ arguments →
      isWfShape [] (panValueShape [] value) = true := by
    intro value hmem
    simpa [panSemShapeOf_eq_panValueShape_nil] using hwf value hmem
  simpa only [panSemShapeOfMapPanValueShapeNil] using
    (tlcWithShapeGetElemMap arguments slots index hdistinct hslotsLength hwf' hindex)

/-- Target-state view of `tlc`: the finite map stores the HOL `word_lab`
constructor required by `locals_rel`, while the source-facing shape premise
remains `panSem$shape_of`/`is_wf_shape_v_nil`. -/
def tlcWordLab (slots : List Nat) (arguments : List (PanValue α)) :
    FiniteMap Nat (PanWordLab α) :=
  FUPDATE_LIST FEMPTY
    (slots.zip ((arguments.flatMap panValueFlatten).map PanWordLab.word))

theorem tlcWordLabWithShapeGetElemMapOfPanSem
    (arguments : List (PanValue α)) (slots : List Nat) (index : Nat)
    (hdistinct : slots.Nodup)
    (hslotsLength : slots.length = (arguments.flatMap panValueFlatten).length)
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true)
    (hindex : index < arguments.length) :
    ((withShape (arguments.map panSemShapeOf) slots)[index]'(by
      rw [withShape_length]
      simpa using hindex)).mapM (FLOOKUP (tlcWordLab slots arguments)) =
      some ((panValueFlatten (arguments[index]'hindex)).map PanWordLab.word) := by
  let shapes := arguments.map panSemShapeOf
  let words := arguments.flatMap panValueFlatten
  have hwf' : ∀ value, value ∈ arguments →
      isWfShape [] (panValueShape [] value) = true := by
    intro value hmem
    simpa [panSemShapeOf_eq_panValueShape_nil] using hwf value hmem
  have hshapeSize : Shape.shapeSize (.comb shapes) = words.length := by
    simpa [shapes, words, panSemShapeOfMapPanValueShapeNil,
      Function.comp_def, List.length_flatMap] using
      shapeSize_comb_map_panValueShape_eq_flatten_length arguments hwf'
  have hslotsShape : slots.length = Shape.shapeSize (.comb shapes) :=
    hslotsLength.trans hshapeSize.symm
  have hindexShapes : index < shapes.length := by simpa [shapes] using hindex
  have hslotsWindow := withShape_getElem_eq_take_drop shapes slots index
    hslotsShape hindexShapes
  have hwhole : slots.mapM (FLOOKUP (tlcWordLab slots arguments)) =
      some (words.map PanWordLab.word) := by
    have hlookup : FLOOKUP (tlcWordLab slots arguments) =
        fun key => FLOOKUP (FUPDATE_LIST FEMPTY (slots.zip (words.map PanWordLab.word))) key := by
      funext key
      rfl
    rw [hlookup]
    exact opt_mmap_some_eq_zip_flookup slots FEMPTY (words.map PanWordLab.word)
      hdistinct (by simpa [words] using hslotsLength)
  have hwindow := list_mapM_takeDrop_of_success
    (FLOOKUP (tlcWordLab slots arguments)) slots (words.map PanWordLab.word)
    (Shape.shapeSize (.comb (shapes.take index)))
    (Shape.shapeSize (shapes[index]'hindexShapes)) hwhole
  have hpartition := withShape_mapPanValueFlattenOfPanSem arguments hwf
  have hpartitionLab :
      withShape shapes (words.map PanWordLab.word) =
        arguments.map (fun value => (panValueFlatten value).map PanWordLab.word) := by
    have hpartition' : withShape shapes words = arguments.map panValueFlatten := by
      simpa only [shapes, words, List.flatten_eq_flatMap, List.flatMap_map, id] using hpartition
    rw [withShapeMap, hpartition']
    simp only [List.map_map, Function.comp_def]
  let wordGroups := arguments.map (fun value => (panValueFlatten value).map PanWordLab.word)
  have hgroupBound : index < (withShape shapes (words.map PanWordLab.word)).length := by
    rw [withShape_length]
    exact hindexShapes
  have hpartitionIndex :
      (withShape shapes (words.map PanWordLab.word))[index]'hgroupBound =
        (panValueFlatten (arguments[index]'hindex)).map PanWordLab.word := by
    have hindexed := congrArg
      (fun groups : List (List (PanWordLab α)) => groups[index]?) hpartitionLab
    have hindexedLeft := List.getElem?_eq_getElem hgroupBound
    have hindexMap : index < wordGroups.length := by
      simpa only [wordGroups, List.length_map] using hindex
    have hindexedRight :
        wordGroups[index]? = some (wordGroups[index]'hindexMap) :=
      List.getElem?_eq_getElem hindexMap
    rw [hindexedLeft, hindexedRight] at hindexed
    have hmapElem : wordGroups[index]'hindexMap =
        (panValueFlatten (arguments[index]'hindex)).map PanWordLab.word := by
      rw [List.getElem_map]
    exact (Option.some.inj hindexed).trans hmapElem
  have hwordLabSize : (words.map PanWordLab.word).length =
      Shape.shapeSize (.comb shapes) := by
    calc
      (words.map PanWordLab.word).length = words.length := by simp
      _ = Shape.shapeSize (.comb shapes) := hshapeSize.symm
  rw [hslotsWindow, hwindow]
  rw [← withShape_getElem_eq_take_drop shapes (words.map PanWordLab.word) index
    hwordLabSize hindexShapes, hpartitionIndex]

/-- The third conjunct of the Call entry `locals_rel` proof for one source
`slc` lookup. The indexed source formal selects the corresponding `ctxtFc`
slot group, whose actual word_lab `tlc` map yields the flattened value. -/
theorem slcTlcWordLabLocalsRelMemberOfPanSem
    (context : PanToCrepProofContext α) (parameters : List (String × Shape))
    (arguments : List (PanValue α)) (slots : List Nat)
    (name : String) (value : PanValue α)
    (hnames : (parameters.map Prod.fst).Nodup)
    (hshapeMap : parameters.map Prod.snd = arguments.map panSemShapeOf)
    (hslots : slots.Nodup)
    (hslotsLength : slots.length = (arguments.flatMap panValueFlatten).length)
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true)
    (hlookup : FLOOKUP (slc parameters arguments) name = some value) :
    ∃ names words,
      FLOOKUP (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots).vars name =
          some (panValueShape [] value, names) ∧
      names.mapM (FLOOKUP (tlcWordLab slots arguments)) = some words ∧
      (panValueFlatten value).map PanWordLab.word = words ∧
      isWfShape [] (panValueShape [] value) = true := by
  obtain ⟨index, hindexName, hindexArg, hnameAt, hargAt⟩ :=
    slcLookupGetElem parameters arguments name value hlookup
  have hindexShape : index < (parameters.map Prod.snd).length := by
    simpa only [List.length_map] using hindexName
  have hindexPanSemShape : index < (arguments.map panSemShapeOf).length := by
    simpa only [List.length_map] using hindexArg
  have hshapeAtMap := congrArg (fun shapes : List Shape => shapes[index]?) hshapeMap
  have hshapeAtSource : (parameters.map Prod.snd)[index]? =
      some ((parameters.map Prod.snd)[index]'hindexShape) :=
    List.getElem?_eq_getElem hindexShape
  have hshapeAtArgs : (arguments.map panSemShapeOf)[index]? =
      some ((arguments.map panSemShapeOf)[index]'hindexPanSemShape) :=
    List.getElem?_eq_getElem hindexPanSemShape
  rw [hshapeAtSource, hshapeAtArgs] at hshapeAtMap
  have hshapeAt : (parameters.map Prod.snd)[index]'hindexShape =
      panSemShapeOf (arguments[index]'hindexArg) := by
    simpa only [List.getElem_map] using Option.some.inj hshapeAtMap
  have hshapeValue : (parameters.map Prod.snd)[index]'hindexShape =
      panValueShape [] value := by
    calc
      (parameters.map Prod.snd)[index]'hindexShape =
          panSemShapeOf (arguments[index]'hindexArg) := hshapeAt
      _ = panValueShape [] (arguments[index]'hindexArg) :=
        panSemShapeOf_eq_panValueShape_nil _
      _ = panValueShape [] value := by rw [hargAt]
  have hindexParameter : index < parameters.length := by
    simpa only [List.length_map] using hindexName
  have hcontext := ctxtFcVarsLookupGetElem context parameters slots index hnames hindexParameter
  rw [hnameAt, hshapeValue] at hcontext
  have hgroupsEq := congrArg (fun shapes : List Shape => withShape shapes slots) hshapeMap
  have hindexSourceGroup : index <
      (withShape (parameters.map Prod.snd) slots).length := by
    rw [withShape_length]
    exact hindexShape
  have hindexTargetGroup : index <
      (withShape (arguments.map panSemShapeOf) slots).length := by
    rw [withShape_length]
    exact hindexPanSemShape
  have hgroupsAt := congrArg
    (fun groups : List (List Nat) => groups[index]?) hgroupsEq
  have hsourceGroupSome := List.getElem?_eq_getElem hindexSourceGroup
  have htargetGroupSome := List.getElem?_eq_getElem hindexTargetGroup
  rw [hsourceGroupSome, htargetGroupSome] at hgroupsAt
  have hgroupsAt' :
      (withShape (parameters.map Prod.snd) slots)[index]'hindexSourceGroup =
        (withShape (arguments.map panSemShapeOf) slots)[index]'hindexTargetGroup :=
    Option.some.inj hgroupsAt
  have hmap := tlcWordLabWithShapeGetElemMapOfPanSem arguments slots index hslots
    hslotsLength hwf hindexArg
  rw [← hgroupsAt'] at hmap
  rw [hargAt] at hmap
  have hwfValue : isWfShape [] (panValueShape [] value) = true := by
    rw [← hargAt]
    simpa [panSemShapeOf_eq_panValueShape_nil] using
      hwf (arguments[index]'hindexArg) (List.getElem_mem hindexArg)
  exact ⟨(withShape (parameters.map Prod.snd) slots)[index]'hindexSourceGroup,
    (panValueFlatten value).map PanWordLab.word, hcontext, hmap, rfl, hwfValue⟩

/-- The complete `locals_rel` conjunct for the Call-entry bindings, expressed
at the source panSem shape/empty-context premise and the target state's
`word_lab` locals map. This remains untagged support until the enclosing HOL
Call preservation theorem is ported with its state/code/excp conclusions. -/
theorem slcTlcWordLabLocalsRelOfPanSem
    (context : PanToCrepProofContext α) (parameters : List (String × Shape))
    (arguments : List (PanValue α)) (slots : List Nat)
    (hnames : (parameters.map Prod.fst).Nodup)
    (hshapeMap : parameters.map Prod.snd = arguments.map panSemShapeOf)
    (hslots : slots.Nodup)
    (hslotsLength : slots.length = (arguments.flatMap panValueFlatten).length)
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true) :
    noOverlap (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
      (parameters.map Prod.snd) slots).vars ∧
    ctxtMax
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots).vmax
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots).vars ∧
    (∀ name value, FLOOKUP (slc parameters arguments) name = some value →
      ∃ names words,
        FLOOKUP (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd) slots).vars name =
            some (panValueShape [] value, names) ∧
        names.mapM (FLOOKUP (tlcWordLab slots arguments)) = some words ∧
        (panValueFlatten value).map PanWordLab.word = words ∧
        isWfShape [] (panValueShape [] value) = true) := by
  have hwfNil : ∀ value, value ∈ arguments →
      isWfShape [] (panValueShape [] value) = true := by
    intro value hmem
    simpa [panSemShapeOf_eq_panValueShape_nil] using hwf value hmem
  have hshapeMapNil : parameters.map Prod.snd = arguments.map (panValueShape []) := by
    calc
      parameters.map Prod.snd = arguments.map panSemShapeOf := hshapeMap
      _ = arguments.map (panValueShape []) := panSemShapeOfMapPanValueShapeNil arguments
  have hshapeSize : Shape.shapeSize (.comb (parameters.map Prod.snd)) =
      (arguments.flatMap panValueFlatten).length := by
    rw [hshapeMapNil]
    simpa [Function.comp_def, List.length_flatMap] using
      shapeSize_comb_map_panValueShape_eq_flatten_length arguments hwfNil
  have hslotsShape : slots.length = Shape.shapeSize (.comb (parameters.map Prod.snd)) :=
    hslotsLength.trans hshapeSize.symm
  have hnoOverlap := ctxtFcNoOverlapOfDistinctSlots context parameters slots hslots hslotsShape
  have hmax := ctxtFcCtxtMaxOfSlots context parameters slots hslotsShape
  have hcontextMax : ctxtMax
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots).vmax
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots).vars := by
    simpa [ctxtFc] using hmax
  refine ⟨hnoOverlap, hcontextMax, ?_⟩
  intro name value hlookup
  exact slcTlcWordLabLocalsRelMemberOfPanSem context parameters arguments slots
    name value hnames hshapeMap hslots hslotsLength hwf hlookup

/-- HOL-`LIST_REL` presentation of the Call-entry `locals_rel` conjunct.
`hshapeAt` is the indexed form supplied by `LIST_REL_EL_EQN`; this theorem
constructs the source shape-map bridge explicitly before applying the
`panSem$shape_of`/`is_wf_shape_v_nil` proof above. -/
theorem slcTlcWordLabLocalsRelOfIndexedPanSem
    (context : PanToCrepProofContext α) (parameters : List (String × Shape))
    (arguments : List (PanValue α)) (slots : List Nat)
    (hnames : (parameters.map Prod.fst).Nodup)
    (hlength : parameters.length = arguments.length)
    (hshapeAt : ∀ index (hparam : index < parameters.length)
      (harg : index < arguments.length),
      (parameters[index]'hparam).2 = panSemShapeOf (arguments[index]'harg))
    (hslots : slots.Nodup)
    (hslotsLength : slots.length = (arguments.flatMap panValueFlatten).length)
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true) :
    noOverlap (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
      (parameters.map Prod.snd) slots).vars ∧
    ctxtMax
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots).vmax
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots).vars ∧
    (∀ name value, FLOOKUP (slc parameters arguments) name = some value →
      ∃ names words,
        FLOOKUP (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd) slots).vars name =
            some (panValueShape [] value, names) ∧
        names.mapM (FLOOKUP (tlcWordLab slots arguments)) = some words ∧
        (panValueFlatten value).map PanWordLab.word = words ∧
        isWfShape [] (panValueShape [] value) = true) := by
  exact slcTlcWordLabLocalsRelOfPanSem context parameters arguments slots hnames
    (callParameterShapeMapEqPanSem parameters arguments hlength hshapeAt)
    hslots hslotsLength hwf

/-! HOL `state_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:45`).
    The source Pancake state and target Crepe state agree on their memory
    domains, clock, endianness, FFI state, and address bounds; the source has
    no struct context (`s.structs = []`) and no globals (`s.globals = FEMPTY`).
    `word_lab` is a single-constructor type, so the target's raw word cells
    reconstruct the source `PanValue` cells with `PanValue.word`; a source cell
    that stored a structure could not be recovered from the target memory and
    therefore does not satisfy the relation. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
def stateRel (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ) : Prop :=
  s.memory = (fun address => some (PanValue.word (panTheWord (t.memory address)))) ∧
    s.memaddrs = t.memaddrs ∧
    s.sharedMemaddrs = t.shMemaddrs ∧ s.structs = [] ∧
    s.globals = (FEMPTY : FiniteMap VarName (PanValue α)) ∧
    s.clock = t.clock ∧ s.be = t.bigEndian ∧ s.ffi = t.ffi ∧
    s.baseAddress = t.baseAddress ∧ s.topAddress = t.topAddress

/-! The executable source state's memory is optional and carries `PanValue`,
whereas HOL `panSem$state.memory` is total and carries `word_lab`.  Under
`stateRel`, every source cell is exactly the target's word cell and the
`memaddrs`/endianness fields agree.  These untagged adapters expose that
boundary for the fixed RV64 source evaluator's byte and 32-bit loads.  They are
case lemmas, not claims that the enclosing `pc_compile_correct` proof is done. -/

/-- A source `LoadByte (Const address)` under the Pan-to-Crep state relation
uses the state-owned address domain, byte order, and total word memory found in
the related target state.  This is a RISC-V evaluator-case adapter, not a
standalone HOL theorem. -/
theorem panToCrepSourceLoadByteHOLCase
    [NeZero 64] [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0]
    [OfNat (RiscV.Word 64) 1] [OfNat (RiscV.Word 64) 2]
    [OfNat (RiscV.Word 64) 3] [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)]
    [Sub (RiscV.Word 64)] [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) (hstate : stateRel source target) :
    evalPanSemStateExp source (.loadByte (.const address)) =
      (panMemLoadByteHOL (width := 64)
        (fun current => match target.memory current with
          | .word value => .word value)
        (fun current =>
          (source.memaddrs current && panValueWordDefined source.memory current) = true)
        source.be address).map
          (fun byte => PanValue.word (BitVec.ofNat 64 byte.toNat)) := by
  rcases hstate with ⟨hmemory, _, _, _, _, _, _, _, _, _⟩
  simp only [evalPanSemStateExp, evalPanValueExp]
  change ((panSemBitVec64MemoryAccess source).readByte
      (panSemBitVec64MemoryAccess source).domain source.memory
      panSemBitVec64BytesInWord address).map PanValue.word = _
  rw [panSemBitVec64ReadByte_eq_panMemLoadByteHOL source source.memory address]
  have hmemoryView :
      (fun current => match target.memory current with
        | .word value => .word value) = panValueWordHOL source.memory := by
    funext current
    simp [panValueWordHOL, hmemory, panTheWord]
  rw [hmemoryView]
  have hdomainView :
      (fun current =>
        (source.memaddrs current && decide (panValueWordDefined source.memory current = true)) = true) =
      (fun current =>
        (source.memaddrs current && panValueWordDefined source.memory current) = true) := by
    funext current
    simp
  simp only [hdomainView]
  simp only [Option.map_map]
  rfl

/-- A source `Load32 (Const address)` under the Pan-to-Crep state relation
uses the related target's word cells, address domain, and byte order.  This is
an untagged RISC-V evaluator-case adapter. -/
theorem panToCrepSourceLoad32HOLCase
    [NeZero 64] [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0]
    [OfNat (RiscV.Word 64) 1] [OfNat (RiscV.Word 64) 2]
    [OfNat (RiscV.Word 64) 3] [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)]
    [Sub (RiscV.Word 64)] [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) (hstate : stateRel source target) :
    evalPanSemStateExp source (.load32 (.const address)) =
      (panMemLoad32HOL (width := 64)
        (fun current => match target.memory current with
          | .word value => .word value)
        (fun current =>
          (source.memaddrs current && panValueWordDefined source.memory current) = true)
        source.be address).map
          (fun value => PanValue.word (BitVec.ofNat 64 value.toNat)) := by
  rcases hstate with ⟨hmemory, _, _, _, _, _, _, _, _, _⟩
  simp only [evalPanSemStateExp, evalPanValueExp]
  change ((panSemBitVec64MemoryAccess source).read32
      (panSemBitVec64MemoryAccess source).domain source.memory
      panSemBitVec64BytesInWord address).map PanValue.word = _
  rw [panSemBitVec64Read32_eq_panMemLoad32HOL source source.memory address]
  have hmemoryView :
      (fun current => match target.memory current with
        | .word value => .word value) = panValueWordHOL source.memory := by
    funext current
    simp [panValueWordHOL, hmemory, panTheWord]
  rw [hmemoryView]
  have hdomainView :
      (fun current =>
        (source.memaddrs current && decide (panValueWordDefined source.memory current = true)) = true) =
      (fun current =>
        (source.memaddrs current && panValueWordDefined source.memory current) = true) := by
    funext current
    simp
  simp only [hdomainView]
  simp only [Option.map_map]
  rfl

/-- Source-shaped port of HOL `state_rel_structs[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:59`), a projection of
    `state_rel`.

    FLAPJACK-SPECIFIC (not an exact HOL port; review `flapjack-pxn.18.3.7.1.3`): the
    hypothesis is the Flapjack-specific `stateRel` over production `PanSemState`/
    `CrepRuntimeState`, not HOL `state_rel`. Independently of the identifier carrier:
    (a) `stateRel` relates the source's *optional* `PanValue` memory to the target's
    *total* `word_lab` memory (`s.memory = fun a => some (PanValue.word (panTheWord
    (t.memory a)))`, see the `state_rel_def` note above), whereas HOL `state_rel`
    equates two total `word_lab` memories directly; (b) the source field types are
    `StructContext` (`StructName`/`FieldName` = `String`, `StructInfo` also carrying
    the production-only `shapedFields`) and `PanValue α`, while HOL uses
    `(stcname # struct_info) list` with `stcname`/`fldname` = `mlstring` and the
    `'a v` value type; (c) finite-map keys are `VarName` = `String` vs HOL
    `varname` = `mlstring`. The mismatch is therefore not limited to String-backed
    names, so the `(names_as_string := ...)` qualifier does not apply. The exact
    projection depends on an exact MlString/`word_lab` Crep target relation, tracked
    by `flapjack-pxn.18.3.7.1.3.1` (carrier work `flapjack-pxn.18.3.5.8`). -/
theorem stateRel_structs (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ)
    (hrel : stateRel s t) : s.structs = [] := by
  rcases hrel with ⟨_, _, _, hstructs, _, _, _, _, _, _⟩
  exact hstructs

/-- Source-shaped port of HOL `state_rel_globals[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:65`), a projection of
    `state_rel`.

    FLAPJACK-SPECIFIC (not an exact HOL port; review `flapjack-pxn.18.3.7.1.3`): the
    hypothesis is the Flapjack-specific `stateRel` over production `PanSemState`/
    `CrepRuntimeState`, not HOL `state_rel`, and the conclusion is stated over the
    production carrier `FiniteMap VarName (PanValue α)` rather than HOL
    `varname |-> 'a v`. The mismatch is not limited to the String-vs-`mlstring` domain
    key (`VarName` vs `varname`): `stateRel` also relates an optional `PanValue`
    source memory to a total `word_lab` target memory and the value type is
    `PanValue α` vs `'a v` (see `stateRel_structs` above and the `state_rel_def` note),
    so the `(names_as_string := ...)` qualifier does not apply. The exact projection
    is tracked by `flapjack-pxn.18.3.7.1.3.1` (carrier work `flapjack-pxn.18.3.5.8`). -/
theorem stateRel_globals (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ)
    (hrel : stateRel s t) : s.globals = (FEMPTY : FiniteMap VarName (PanValue α)) := by
  rcases hrel with ⟨_, _, _, _, hglobals, _, _, _, _, _⟩
  exact hglobals

/-- Canonicalizing the target with `riscv64CrepRuntimeTarget` does not change
    the state relation: it only edits fields (`bytesInWord`, `memoryModel`,
    `ffiContext`) that `stateRel` does not constrain, together with `bigEndian`,
    which agrees with the source once the source is little-endian. Flapjack-only
    convenience for the canonical RISC-V 64 target; no HOL original. -/
theorem stateRel_riscv64CrepRuntimeTarget_iff
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (hbe : base.bigEndian = false) :
    stateRel source (riscv64CrepRuntimeTarget base) ↔ stateRel source base := by
  constructor
  · intro hrel
    unfold stateRel at hrel ⊢
    obtain ⟨hm, hma, hsm, hst, hg, hcl, hbe', hffi, hba, hta⟩ := hrel
    exact ⟨hm, hma, hsm, hst, hg, hcl, hbe'.trans hbe.symm, hffi, hba, hta⟩
  · intro hrel
    unfold stateRel at hrel ⊢
    obtain ⟨hm, hma, hsm, hst, hg, hcl, hbe', hffi, hba, hta⟩ := hrel
    exact ⟨hm, hma, hsm, hst, hg, hcl, hbe'.trans hbe, hffi, hba, hta⟩

/-- Flapjack-specific bridge for the target memory representation. HOL
    `crepSem$state.memory` and executable `CrepRuntimeState.memory` are both
    total `word → word_lab` functions; the separate `memaddrs` set guards
    accessible addresses (`crepSemScript.sml:24-26`). This relation states
    equality of the complete memories and is the target-side hypothesis of
    the `mem_load_def` correspondence below. -/
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
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
def localsRel (context : PanToCrepProofContext α)
    (sLocals : FiniteMap String (PanValue α))
    (tLocals : FiniteMap Nat (PanWordLab α)) : Prop :=
  noOverlap context.vars ∧ ctxtMax context.vmax context.vars ∧
    ∀ vname v, FLOOKUP sLocals vname = some v →
      ∃ ns vs, FLOOKUP context.vars vname = some (panValueShape [] v, ns) ∧
        ns.mapM (FLOOKUP tLocals) = some vs ∧
        (panValueFlatten v).map PanWordLab.word = vs ∧
        isWfShape [] (panValueShape [] v) = true

/-! The preceding Call-entry bridge is phrased as the expanded body of
`locals_rel_def`, so it can also be supplied directly wherever the recursive
Call case asks for the relation itself. This wrapper keeps the literal HOL
relation at the callee-entry boundary; it adds no premise or HOL tag. -/
theorem slcTlcWordLabLocalsRelOfIndexedPanSem_exact
    (context : PanToCrepProofContext α) (parameters : List (String × Shape))
    (arguments : List (PanValue α)) (slots : List Nat)
    (hnames : (parameters.map Prod.fst).Nodup)
    (hlength : parameters.length = arguments.length)
    (hshapeAt : ∀ index (hparam : index < parameters.length)
      (harg : index < arguments.length),
      (parameters[index]'hparam).2 = panSemShapeOf (arguments[index]'harg))
    (hslots : slots.Nodup)
    (hslotsLength : slots.length = (arguments.flatMap panValueFlatten).length)
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true) :
    localsRel
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots)
      (slc parameters arguments) (tlcWordLab slots arguments) := by
  unfold localsRel
  exact slcTlcWordLabLocalsRelOfIndexedPanSem context parameters arguments slots
    hnames hlength hshapeAt hslots hslotsLength hwf

/-! Relate the successful source evaluator binder directly to the target
callee-entry word_lab locals. This is the state-owned Call boundary: the
source's `bindPanValueParameters` result is identified with HOL `slc`, then
the exact expanded `locals_rel` proof above applies. It remains support for the
enclosing recursive Call case and is not itself a HOL theorem port. -/
theorem bindPanValueParametersLocalsRelOfPanSem
    (context : PanToCrepProofContext α) (parameters : List (String × Shape))
    (arguments : List (PanValue α)) (slots : List Nat)
    (sourceLocals : String → Option (PanValue α))
    (hnames : (parameters.map Prod.fst).Nodup)
    (hlength : parameters.length = arguments.length)
    (hshapeMap : parameters.map Prod.snd = arguments.map panSemShapeOf)
    (hslots : slots.Nodup)
    (hslotsLength : slots.length = (arguments.flatMap panValueFlatten).length)
    (hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true)
    (hbind : bindPanValueParameters (parameters.map Prod.fst) arguments =
      some sourceLocals) :
    localsRel
      (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
        (parameters.map Prod.snd) slots)
      sourceLocals (tlcWordLab slots arguments) := by
  have hbindSlc := bindPanValueParameters_eq_slc parameters arguments hlength
  have hsourceLocals : sourceLocals = slc parameters arguments :=
    Option.some.inj (hbind.symm.trans hbindSlc)
  rw [hsourceLocals]
  exact slcTlcWordLabLocalsRelOfPanSem context parameters arguments slots
    hnames hshapeMap hslots hslotsLength hwf

/-- HOL `locals_rel_wf_shape`: every source local covered by the local-state
    relation is a well-formed value in the empty struct context. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
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

/-- HOL `mk_ctxt_imp_locals_rel` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4677-4682`):
    the initial compiler context built from the source function table has an empty
    variable map and slot bound, so the locals relation holds against any target
    locals for the empty source locals map. The proof-context record mirrors Cake
    `mk_ctxt FEMPTY (make_funcs pc) 0 es`.

    The statement shape is mirrored (`∀ pc lcl es. locals_rel (mk_ctxt …) FEMPTY lcl`
    becomes a universally quantified `declarations`/`eids`/`locals` with the same
    `mk_ctxt`-shaped context and conclusion). It is intentionally untagged because
    the carriers differ from the reviewed exact HOL carriers: this declaration uses
    the production `Decl α`, `FunName`/`VarName`/`ExceptionId = String`, production
    `Shape` and `PanToCrepProofContext`, plus `FiniteMap`-valued `eids` and
    `PanWordLab`-valued `locals`, whereas HOL quantifies an `'a decl list` and
    `(mlstring,'a word) fmap` with `mlstring` keys and HOL `shape`. It also delegates
    to the production `panToCrepMakeFuncs`/`infoMapToFiniteMap` rather than HOL
    `make_funcs`, and carries the executable `[LawfulBEq String]` condition. A
    `names_as_string` qualifier cannot authorize the `Decl`/`Shape`/value carriers,
    and no `NameRanged` byte witness applies (`locals_rel` is a relation, not a name).
    The reviewed exact carrier is tracked by `flapjack-pxn.18.3.5.8` (parent
    `flapjack-pxn.18.3.5.7.2`). `docs/HOL-THEOREM-MAP.json` already records this
    hol_name as `documented_mismatch`. Evidence:
    `Flapjack/Test/MkCtxtImpLocalsRelParity.lean` instantiates the theorem against
    the `mk_ctxt`-shaped `initialContext`. -/
theorem mkCtxtImpLocalsRel [LawfulBEq String]
    (declarations : List (Decl α)) (eids : FiniteMap String α)
    (locals : FiniteMap Nat (PanWordLab α)) :
    localsRel
      { vars := (FEMPTY : FiniteMap String (Shape × List Nat))
        funcs := infoMapToFiniteMap (panToCrepMakeFuncs declarations)
        eids := eids
        vmax := 0 }
      FEMPTY locals := by
  refine ⟨?_, ?_, ?_⟩
  · simp [noOverlap, FLOOKUP_empty]
  · simp [ctxtMax]
  · intro name value hlookup
    simp [FLOOKUP_empty] at hlookup

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

/-- HOL `locals_rel_lookup_ctxt` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:527-534`):
    `locals_rel ctxt lcl lcl' /\ FLOOKUP lcl vr = SOME v ==>
      ?ns. FLOOKUP ctxt.vars vr = SOME (shape_of v,ns) /\
        LENGTH ns = LENGTH (flatten v) /\
        OPT_MMAP (FLOOKUP lcl') ns = SOME (flatten v) /\
        is_wf_shape_nil (shape_of v)`.
    The Lean statement mirrors the two hypotheses and the four existential
    conjuncts clause for clause: HOL `OPT_MMAP` becomes the `List.mapM` result
    `slots.mapM (FLOOKUP targetLocals) = some (...)`, and `shape_of`/`flatten`/
    `is_wf_shape_nil` become `panValueShape []`/`panValueFlatten`/`isWfShape []`.
-/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the carriers differ from the HOL
-- declaration. `locals_rel`/its context is the production `localsRel` over
-- `PanToCrepProofContext α` (or `PanToCrepHOLContext α`) whose `vars`/`funcs`/`eids`
-- finite maps are keyed by the production `FunName`/`VarName`/`ExceptionId` = `String`,
-- and locals carry the production `PanValue α`/`Shape` (`named : String`) over a generic
-- word `α`; HOL keys names by `funname`/`varname`/`eid` = `mlstring` and uses
-- `panSem$v`/`shape` (`named : mlstring`) over a positive-width `'a word`. The
-- production `shape_of`/`flatten`/`is_wf_shape_nil` mirrors are the untagged
-- `panValueShape`/`panValueFlatten`/`isWfShape`. `names_as_string` cannot authorize
-- the embedded `PanValue`/`Shape` carriers (identifiers occur inside the local value,
-- not at the theorem boundary), and no `NameRanged`/`holMlStringWitness_*` byte witness
-- applies because the conclusion is an existential over slot lists and `localsRel`, not
-- a name. Oracle evidence: the kernel-checked fixture `localsRelLookupCtxt_fixture`
-- (`Flapjack/Test/PanToCrepStateRelParity.lean:231`) derives the exact four conjuncts
-- for a one-word local (`slot [0]`, flattened `[.word 5]`); the local-update/well-formed
-- behaviour used here is pinned by the HOL-oracle rows of
-- `scripts/hol-probes/pan_upd_locals_probe.out` (`pan_upd_locals_hit=SOME 7`,
-- `pan_upd_locals_empty=NONE`) and `scripts/hol-probes/pan_empty_locals_probe.out`.
-- The exact MlString/value carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
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
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
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

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL
    `local_rel_le_zip_update_preserved`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2263-2269`): replacing a
    source local `x` by a shape-compatible value `v'` and writing its flattened
    words to the associated distinct slots `ns` preserves `locals_rel`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port), source-reviewed 2026-09-25:
-- statement shape is mirrored clause-for-clause: `locals_rel ct l l'` ->
-- `localsRel context sourceLocals targetLocals`; `FLOOKUP l x = SOME v` ->
-- `FLOOKUP sourceLocals name = some oldValue`; `FLOOKUP ct.vars x = SOME (sh,ns)`
-- -> `FLOOKUP context.vars name = some (shape, slots)`; `shape_of v = shape_of v'`
-- -> `panValueShape [] oldValue = panValueShape [] newValue`; `ALL_DISTINCT ns`
-- -> `slots.Nodup`; and `locals_rel ct (l |+ (x,v')) (l' |++ ZIP (ns,flatten v'))`
-- -> `localsRel context (FUPDATE sourceLocals (name,newValue)) (FUPDATE_LIST
-- targetLocals (slots.zip ((panValueFlatten newValue).map PanWordLab.word)))`.
-- Carrier mismatch: the Lean statement is keyed by the production identifiers
-- `FunName`/`VarName`/`ExceptionId` = `String` and embeds a
-- `PanToCrepProofContext α` whose finite maps are `String`-keyed, while HOL
-- keys names by `funname`/`varname`/`eid` = `mlstring`; the source-local
-- carrier is production `PanValue α` (with embedded production `Shape`,
-- `named : String`) over a generic word `α`, while HOL uses `panSem$v` /
-- `shape` over a positive-width `'a word` with no typeclass side condition.
-- `names_as_string` cannot authorize the `PanValue`/`Shape` carriers (the
-- identifiers occur inside the local value, not at the theorem boundary), and
-- no `NameRanged` byte witness applies because the conclusion is a `localsRel`
-- relation. `docs/HOL-THEOREM-MAP.json` already classifies this hol_name as
-- `documented_mismatch`; the declaration is intentionally untagged.
-- Evidence: this theorem is exercised by the `Primitive` case of the
-- compile-correctness proof (`Flapjack/Pancake/Proofs/PanToCrep/EvaluateCases.lean:1801`);
-- the `flatten`/`shape_of` components have HOL-oracle rows in
-- `scripts/hol-probes/pan_flatten_probe.out` (`word`/`record`/`named`), and the
-- accompanying `locals_rel` lemmas (`locals_rel_extend_new_var`,
-- `locals_rel_lookup_ctxt`) are tracked under the same withdrawn-tag review.
-- The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
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

/-! `localsRelUpdateExistingValue` proves the local-map relation after a
shape-preserving source update, using the slots recorded in `context.vars`.
The target runtime `exp_hdl` execution for a one-word payload is already proved
by `EvaluateCases.crepRuntimeExpHdlOneWord`; its
`crepRuntimeExpHdlOneWord_localsRel` companion proves the `locals_rel`
postcondition. The one-word target evaluator is therefore not a remaining
proof step. The corresponding arbitrary-width flattened execution and
local relation are `EvaluateCases.crepRuntimeExpHdlFiniteMapWords` and
`crepRuntimeExpHdlFiniteMapWords_localsRel`. The actual state and relation
setup for a matching handler is available as untagged induction support in
`crepRuntimeExpHdlFiniteMapWords_handlerPrestateRelations`. This lemma supplies
the source-to-target map-update relation used by those proofs. The remaining
gap is composing the recursive callee and handler induction hypotheses into
the full source/target HOL `Call_Ret_Exception` case. -/
theorem localsRelUpdateExistingValue
    (context : PanToCrepProofContext α)
    (sourceLocals : FiniteMap String (PanValue α))
    (targetLocals : FiniteMap Nat (PanWordLab α))
    (name : String) (oldValue newValue : PanValue α)
    (hrel : localsRel context sourceLocals targetLocals)
    (hsource : FLOOKUP sourceLocals name = some oldValue)
    (hshape : panValueShape [] oldValue = panValueShape [] newValue) :
    ∃ slots,
      FLOOKUP context.vars name = some (panValueShape [] newValue, slots) ∧
      slots.Nodup ∧
      localsRel context (FUPDATE sourceLocals (name, newValue))
        (FUPDATE_LIST targetLocals
          (slots.zip ((panValueFlatten newValue).map PanWordLab.word))) := by
  obtain ⟨slots, hcontextOld, _hlen, _hwords, _hwf⟩ :=
    localsRelLookupCtxt context sourceLocals targetLocals name oldValue hrel hsource
  have hcontextNew : FLOOKUP context.vars name =
      some (panValueShape [] newValue, slots) := by
    rw [← hshape]
    exact hcontextOld
  have hdistinct : slots.Nodup := hrel.1.1 name
    (panValueShape [] oldValue) slots hcontextOld
  refine ⟨slots, hcontextNew, hdistinct, ?_⟩
  exact localRelLeZipUpdatePreserved context sourceLocals targetLocals name
    oldValue newValue (panValueShape [] oldValue) slots hrel hsource hcontextOld
    hshape hdistinct

/-- HOL `locals_rel_extend_new_var` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4179-4186`):
    a fresh, well-shaped source local can be allocated in distinct target slots
    above the old context maximum:
    `locals_rel ct s t /\ is_wf_shape_nil (shape_of v) /\ ALL_DISTINCT ns /\
      (!x. MEM x ns ==> ct.vmax < x /\ x <= ct.vmax + size_of_shape (shape_of v)) /\
      LENGTH ns = size_of_shape (shape_of v) ==>
      locals_rel (ct with <|vars := ct.vars |+ (x,(shape_of v,ns));
        vmax := ct.vmax + size_of_shape (shape_of v)|>) (s |+ (x,v))
        (t |++ ZIP(ns, flatten v))`.
    The Lean statement mirrors the HOL hypothesis set and conclusion clause for
    clause: `locals_rel`/`is_wf_shape_nil`/`ALL_DISTINCT`/the slot-bounds condition/
    `LENGTH` become `localsRel`/`isWfShape []`/`slots.Nodup`/`hbounds`/`hlen`, and
    `shape_of`/`flatten` become `panValueShape []`/`panValueFlatten`.
-/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the carriers differ from the HOL
-- declaration. `locals_rel`/its context is the production `localsRel` over
-- `PanToCrepProofContext α` (or `PanToCrepHOLContext α`) whose `vars`/`funcs`/`eids`
-- finite maps are keyed by the production `FunName`/`VarName`/`ExceptionId` = `String`,
-- and locals carry the production `PanValue α`/`Shape` (`named : String`) over a generic
-- word `α`; HOL keys names by `funname`/`varname`/`eid` = `mlstring` and uses
-- `panSem$v`/`shape` (`named : mlstring`) over a positive-width `'a word`. The
-- production `isWfShape`/`panValueShape`/`panValueFlatten` are the untagged production
-- mirrors of HOL `is_wf_shape_nil`/`shape_of`/`flatten`. `names_as_string` cannot
-- authorize the embedded `PanValue`/`Shape` carriers (the identifiers occur inside the
-- local value, not at the theorem boundary), and no `NameRanged`/`holMlStringWitness_*`
-- byte witness applies because the conclusion is the `localsRel` relation, not a name.
-- The exact MlString/value carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
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


/-- Bridge from the proof-side finite-map context to the HOL finite-map
    compiler context; the two records have the same four fields. -/
def PanToCrepProofContext.toHOLContext (context : PanToCrepProofContext α) :
    PanToCrepHOLContext α :=
  { vars := context.vars, funcs := context.funcs, eids := context.eids,
    vmax := context.vmax }

/-- `compileProgRiscV` is the untagged, `compile_def`-shaped Flapjack helper.
    Its production syntax carriers do not match HOL; see the declaration-local
    note in `PanToCrep/Compile.lean`. It is definitionally the generic
    `compileProgHOL` on the same context. -/
theorem compileProgRiscV_eq_compileProgHOL
    (context : PanToCrepHOLContext (BitVec width))
    (program : Prog (BitVec width)) :
    compileProgRiscV context program = compileProgHOL context program := rfl

/-- The proof-side compiler expression `compileCodeRelProg` is exactly the
    `compile_def`-shaped compiler (`compileProgRiscV`, untagged) on the bridged
    context, for EVERY proof context, not only declaration-derived ones. -/
theorem compileCodeRelProg_eq_compileProgRiscV
    (context : PanToCrepProofContext (BitVec width))
    (program : Prog (BitVec width)) :
    compileCodeRelProg context program =
      compileProgRiscV context.toHOLContext program := rfl

/-! Flapjack's code relation, shaped after HOL `code_rel_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:32`). It quantifies over
    every source code entry, requires localisation and the exact
    parameter/return-shape lookup in `ctxt.funcs`, derives parameter slots
    from `GENLIST I (size_of_shape (Comb shs))`, and constructs the target
    context with `ctxt_fc`.

    This declaration is intentionally untagged: it is generic in the word
    element type `α`, while the `compile_def`-shaped RISC-V
    specialization `compileProgRiscV`. The bridge
    `compileCodeRelProg_eq_compileProgRiscV` (with
    `compileProgRiscV_eq_compileProgHOL`) proves that `compileCodeRelProg` is
    definitionally that compiler for EVERY proof context at `BitVec
    width`, not only declaration-derived ones, so the remaining gaps to an exact HOL
    `code_rel_def` tag are (a) the width-indexing of this relation (tracked in
    the Exp/word-indexing migration beads) and (b) the `String`-vs-`mlstring`
    key carrier (`FunName`/`VarName`/`ExceptionId` = `String` vs HOL
    `funname`/`varname`/`eid` = `mlstring`, tracked by
    `flapjack-pxn.18.3.5.8`) - not the compiler expression. -/

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

/-- Width-indexed proof-side `code_rel` interface: the HOL reference is
    word-length polymorphic (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:32-43`),
    so this width-indexed form makes the compiler expression the
    `compileProgRiscV` (`compile_def`-shaped) boundary. The generic `codeRel` is its
    `alpha`-instantiated view (`codeRelW_iff_codeRel` below).

    Source-reviewed decision: the `code_rel_def` tag stays WITHDRAWN as a
    documented carrier mismatch, not an exact port. Clause for clause this matches
    HOL `code_rel` (`∀ f vshs prog rsh, FLOOKUP s_code f = SOME (...) ==>
    localised_prog prog ∧ FLOOKUP ctxt.funcs f = SOME (vshs, rsh) ∧ let ... ns =
    GENLIST I (size_of_shape (Comb shs)); nctxt = ctxt_fc ... in FLOOKUP t_code f =
    SOME (ns, compile nctxt prog)`), but the carriers differ: (1) the
    source/target/context maps are keyed by production `FunName`/`VarName`/
    `ExceptionId` = `String`, while HOL keys them by `funname`/`varname`/`eid` =
    `mlstring` (the direct probe prints the HOL type as `(mlstring |->
    (mlstring # shape) list # α panLang$prog # shape) -> (mlstring |-> num list #
    α crepLang$prog) -> bool`); (2) the source shapes are the production `Shape`
    and the target code the production `CrepProg (BitVec width)` whose `Call`/
    `ExtCall` funnames are `String`, compiled through the production
    `compileProgRiscV` rather than HOL's `crepLang$prog`-returning `compile`; (3)
    `names_as_string` cannot authorize the `Shape`/`CrepProg` carriers, and no
    `NameRanged` witness can be stated for a `Prop`-valued relation. Direct
    HOL-EVAL/proof rows (`code_rel_matching`, `code_rel_rejects_wrong_body`,
    `code_rel_rejects_missing_function_signature`,
    `code_rel_rejects_unlocalised_source`) are recorded in
    `scripts/hol-probes/code_rel_probe.out` and reproduced by
    `Flapjack/Test/PanToCrepCodeRelParity.lean`. Exact-carrier replacement is
    tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`); the
    width-indexing part is now handled by this `codeRelW`. -/
def codeRelW (width : Nat)
    (context : PanToCrepProofContext (BitVec width))
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog (BitVec width) × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg (BitVec width))) : Prop :=
  ∀ function variableShapes program returnShape,
    FLOOKUP sourceCode function = some (variableShapes, program, returnShape) →
      localisedProg program ∧
      FLOOKUP context.funcs function = some (variableShapes, returnShape) ∧
      let variables := variableShapes.map Prod.fst
      let shapes := variableShapes.map Prod.snd
      let names := List.range (Shape.shapeSize (.comb shapes))
      let nextContext := ctxtFc context.funcs context.eids variables shapes names
      FLOOKUP targetCode function = some
        (names, compileProgRiscV nextContext.toHOLContext program)

/-- The width-indexed relation is the generic `codeRel` instantiated at
    `BitVec width`, definitionally via the rfl compiler bridges. -/
theorem codeRelW_iff_codeRel (width : Nat)
    (context : PanToCrepProofContext (BitVec width))
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog (BitVec width) × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg (BitVec width))) :
    codeRelW width context sourceCode targetCode ↔
      codeRel context sourceCode targetCode :=
  Iff.rfl

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL
    `compile_exp_not_mem_load_glob`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2013-2020`): under a
    successful `compile_exp` plus `state_rel`, `code_rel`, and `locals_rel`, no
    compiled expression contains a `LoadGlob`. The conclusion
    `CrepExp.loadGlob address ∉ expressions.flatMap crepExps` mirrors HOL's
    `~MEM (LoadGlob ad) (FLAT (MAP exps es))`, and the explicit state/code/locals
    relation premises match HOL. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (and a
-- `PanToCrepProofContext` whose finite maps are `String`-keyed), while HOL keys
-- names by `funname`/`varname`/`eid` = `mlstring`; it also quantifies over the
-- production `Exp α`/`Shape` with an arbitrary word carrier `α` and the extra
-- `[BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]` typeclass
-- arguments (executable-only artifacts absent from HOL), rather than HOL's
-- word-indexed `exp` at a positive word width. The `names_as_string` qualifier
-- cannot authorize the `Exp`/`Shape`/word carriers, and no same-module byte
-- witness applies because the conclusion is a universally quantified `Prop` over
-- expressions, not a name. The HOL statement shape was reviewed against lines
-- 2013-2020 before keeping the tag withdrawn. The faithful exact-carrier port is
-- tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
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

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL `code_rel_imp`: an entry in related source code is localised and
    has the corresponding function metadata and compiled target entry. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the production
-- identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose `FiniteMap`s are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` = `mlstring`.
-- The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
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

/-! Source-shaped analogue of HOL `code_rel_empty_locals`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:96`), not an exact HOL
port. The state updates do preserve both code fields: HOL `empty_locals_def`
at panSemScript.sml:436 and crepSemScript.sml:71 update only `locals`, and
the two Lean updates do the same. The relation carried across those unchanged
fields is still production-specific, however. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL `code_rel_def` at
-- pan_to_crepProofScript.sml:30-42 relates `mlstring`-keyed finite maps whose
-- source entries contain HOL `prog` and whose target entries contain HOL
-- `crep_prog` compiled by `compile`. This theorem instead relates
-- `panSemCodeAsLookup source.code` and `target.code` through production
-- `codeRel`: its keys are `String` (`FunName`/`VarName`), its source entries
-- use production `Prog α`, and its target entries use production `CrepProg α`
-- / `compileCodeRelProg`. There is no `NameRanged` or same-module byte witness
-- premise, and no proved state/code-carrier bridge in this statement. The
-- identifier dependency is `flapjack-pxn.18.3.5.8`; exact HOL Prog/Crep code
-- carriers and their compiler bridge are also still prerequisites. Do not tag
-- this analogue with `code_rel_empty_locals` until those boundaries are exact.
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

/-- Flapjack analogue of HOL `first_compile_to_crep_all_distinct`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4566-4573`), which proves
    `ALL_DISTINCT (MAP FST (functions prog)) ==>
      ALL_DISTINCT (MAP FST (compile_to_crep prog))`. This theorem mirrors that
    statement shape (`Nodup`/`List.map` for `ALL_DISTINCT`/`MAP`), but its input
    is the production `Decl (BitVec width)` carrier with `String`
    `FunName`/`VarName`/`ExceptionId` and production `Shape`, and its output
    uses `FunName`/generic `CrepProg`; HOL quantifies over the `DeclHOL`/panLang
    carrier (`mlstring` identifiers and HOL expression/shape types) and returns
    `mlstring` names with `CrepProgHOL width` bodies. These input and output
    carrier differences exceed identifier representation, so `names_as_string`
    cannot qualify this analogue (no `NameRanged` witness applies either, since
    the conclusion is `Nodup` of a name list derived from a compiled program).
    The withdrawn tag is recorded as a documented mismatch in
    `docs/HOL-THEOREM-MAP.json`; it is intentionally untagged. An exact-carrier
    replacement depends on `DeclHOL` and compiler-boundary work tracked by
    `flapjack-yao.1` (MlString carrier umbrella `flapjack-pxn.18.3.5.8`).
    Distinctness across the `compile_inl_top` boundary is exercised against the
    HOL EVAL row `duplicate_first` of
    `scripts/hol-probes/compile_prog_probe.out` by
    `Flapjack/Test/CompileProgParity.lean`. -/
theorem firstCompileToCrepAllDistinct [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdistinct : ((functionEntries declarations).map
      fun (name, _, _, _) => name).Nodup) :
    ((compileToCrepHOL declarations).map
      fun (name, _, _) => name).Nodup := by
  simpa [compileToCrepHOL, List.map_map, Function.comp_def] using hdistinct

/-- `compileToCrepHOL` is the source function list mapped through `comp_func`
    and `crep_vars`, with the context built from the same declaration list. -/
theorem compileToCrepHOL_eq_map
    (declarations : List (Decl (BitVec width))) :
    compileToCrepHOL declarations =
      (functionEntries declarations).map
        (fun entry =>
          (entry.1,
           (panToCrepVars entry.2.1,
            panToCrepCompFuncRiscV
              (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
                (panToCrepGetEidsFromDeclsHOL declarations))
              entry.2.1 entry.2.2.1))) := by
  simp [compileToCrepHOL, functionInfosHOL_eq_makeFuncsHOL,
    panToCrepCompFuncRiscV_eq_compFuncHOL, panToCrepMkCtxtHOL]

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL `alookup_compile_prog_code`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4575`): a source
    function entry with empty parameters and body `prog` is compiled to the
    Crepe entry whose argument slots are `crep_vars []` and whose body is
    `comp_func (make_funcs (functions pan_code)) (get_eids_from_decls pan_code)
    [] prog`.  `List.lookup` on the nested-pair triple list is HOL's `ALOOKUP`.

    Source-shaped counterparts used here (all currently untagged since the
    `flapjack-pxn.18.3.5.7.2` String-carrier withdrawal): `compileToCrepHOL` (`compile_to_crep_def`),
    `panToCrepVars` (`crep_vars_def`), `panToCrepGetEidsFromDeclsHOL`
    (`get_eids_from_decls_def`), `panToCrepMkCtxtHOL` (`mk_ctxt_def`),
    `panToCrepMakeVmapHOL` (`make_vmap_def`) and `compileProgRiscV`
    (`compile_def`).  Two further helpers are deliberate untagged adapters:
    * `functionInfosHOL` computes the HOL finite-map value
      `alist_to_fmap (make_funcs (functions pan_code))`: `panToCrepMakeFuncs`
      produces the same source-order `(name, (params, return))` list as HOL
      `make_funcs`, and `FUPDATE_LIST FEMPTY ·.reverse` is `alist_to_fmap`
      (`FOLDR FUPDATE FEMPTY`, first duplicate wins);
    * `panToCrepCompFuncRiscV` is `comp_func` after threading the context as a
      record: it reads `context.funcs`/`context.eids` instead of HOL's separate
      `fs`/`eids` arguments and applies the `compile_def`-shaped compiler to the
      `mk_ctxt_def`/`make_vmap_def`. No HOL side condition or body step is
      dropped.  The HOL-vs-Lean equivalence of the statement is not proved by
      this theorem: the theorem is a within-Lean lookup fact, and the HOL
      correspondence is reviewed by comparing the definitions (per SOUNDNESS),
      not established by the proof below. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port). Source-reviewed against HOL
-- `alookup_compile_prog_code` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4575-4586`),
-- which states: `ALL_DISTINCT (MAP FST (functions pan_code)) /\
-- ALOOKUP (functions pan_code) start = SOME ([],prog,rshape) ==>
-- ALOOKUP (compile_to_crep pan_code) start =
--   SOME ([], comp_func (make_funcs (functions pan_code))
--                       (get_eids_from_decls pan_code) [] prog)`.
-- The Lean statement has the same premise/conclusion shape (Nodup + `List.lookup`
-- for `ALL_DISTINCT`/`ALOOKUP`), but its carriers and compilation terms differ:
--   * keyed by production `FunName`/`VarName`/`ExceptionId` = `String` (and the
--     embedded `PanToCrepProofContext`/`PanToCrepHOLContext` `FiniteMap`s are
--     `String`-keyed), while HOL keys by `funname`/`varname`/`eid` = `mlstring`;
--   * `Prog (BitVec width)`/production `Shape` vs HOL's word-indexed `prog`/`shape`;
--   * the body is `panToCrepCompFuncRiscV` (a `comp_func` after threading the
--     context as a record) over `functionInfosHOL` rather than HOL's literal
--     `comp_func (make_funcs (functions pan_code)) (get_eids_from_decls pan_code)`;
--   * the width is a parameter with `[NeZero width]`, an executable condition HOL
--     does not need.
-- `names_as_string` cannot authorize the `Shape`/`Prog` carriers or the adapter
-- terms, and no `NameRanged` byte witness applies (the conclusion is an `ALOOKUP`
-- equation over compiled programs, not a name).  Direct HOL-EVAL rows are recorded
-- in `scripts/hol-probes/crep_alookup_compile_probe.out`
-- (`source_names_distinct=T`, `alookup_empty_params=T`, `alookup_param_entry=T`)
-- and reproduced by `alookupGuard` plus the worked `example`s in
-- `Flapjack/Test/PanToCrepCodeRelParity.lean:158-195` (registered at :440).
-- The `docs/HOL-THEOREM-MAP.json` entry `alookup_compile_prog_code` ->
-- `alookupCompileToCrepCode` is already `documented_mismatch`, so the tag stays
-- WITHDRAWN.  The exact MlString carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem alookupCompileToCrepCode [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (start : FunName) (prog : Prog (BitVec width)) (rshape : Shape)
    (_hdistinct : ((functionEntries declarations).map Prod.fst).Nodup)
    (hlookup : List.lookup start (functionEntries declarations) =
      some ([], (prog, rshape))) :
    List.lookup start (compileToCrepHOL declarations) =
      some ([], panToCrepCompFuncRiscV
        (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
          (panToCrepGetEidsFromDeclsHOL declarations)) [] prog) := by
  obtain ⟨l₁, l₂, hdecomp, hnotin⟩ :=
    List.lookup_eq_some_iff.mp hlookup
  rw [compileToCrepHOL_eq_map]
  apply (List.lookup_eq_some_iff
    (b := ([], panToCrepCompFuncRiscV
      (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
        (panToCrepGetEidsFromDeclsHOL declarations)) [] prog))).mpr
  refine ⟨l₁.map (fun entry =>
      (entry.1, (panToCrepVars entry.2.1,
        panToCrepCompFuncRiscV
          (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
            (panToCrepGetEidsFromDeclsHOL declarations))
          entry.2.1 entry.2.2.1))),
    l₂.map (fun entry =>
      (entry.1, (panToCrepVars entry.2.1,
        panToCrepCompFuncRiscV
          (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
            (panToCrepGetEidsFromDeclsHOL declarations))
          entry.2.1 entry.2.2.1))), ?_, ?_⟩
  · rw [hdecomp, List.map_append, List.map_cons]
    simp [panToCrepVars, Shape.shapeSize]
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa using hnotin q hq

/-! Flapjack-specific finite-map support: reversing an association list before
    `FUPDATE_LIST` makes the first source occurrence win, exactly like
    `List.lookup` (HOL `ALOOKUP`). This is list infrastructure, not a standalone
    HOL theorem port. -/
theorem FLOOKUP_FUPDATE_LIST_reverse_eq_lookup [BEq α] [LawfulBEq α]
    (entries : List (α × β)) (key : α) :
    FLOOKUP (FUPDATE_LIST FEMPTY entries.reverse) key = List.lookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨entryKey, entryValue⟩ := entry
      rw [List.reverse_cons, FUPDATE_LIST_append, FUPDATE_LIST_cons,
        FUPDATE_LIST_nil, FLOOKUP_update, List.lookup_cons]
      by_cases h : entryKey = key
      · subst h
        simp
      · have h1 : (entryKey == key) = false := beq_eq_false_iff_ne.mpr h
        have h2 : (key == entryKey) = false :=
          beq_eq_false_iff_ne.mpr (fun he => h he.symm)
        simp [h1, h2, ih]

/-- Flapjack-specific list fact: mapping a key-preserving projection through an
    association list commutes with `List.lookup` (the list-level `ALOOKUP_MAP`
    step used by HOL inside `mk_ctxt_code_imp_code_rel`). -/
theorem lookup_map_preserveFst [BEq α] [LawfulBEq α] (functions : List (α × β))
    (project : β → γ) (key : α) :
    List.lookup key (functions.map (fun entry => (entry.1, project entry.2))) =
      (List.lookup key functions).map project := by
  induction functions with
  | nil => rfl
  | cons entry functions ih =>
      obtain ⟨entryKey, entryValue⟩ := entry
      rw [List.map_cons, List.lookup_cons, List.lookup_cons]
      by_cases h : (key == entryKey) = true
      · simp [h]
      · simp [h, ih]

/-- Flapjack-specific lookup link for HOL `make_funcs`: a source function entry
    (name, params, body, return) is visible in the `make_funcs` finite map with
    the parameter list and return shape (the body is dropped). -/
theorem makeFuncsHOL_lookup_of_lookup
    (functions : List (FunName × List (VarName × Shape) × Prog α × Shape))
    (start : FunName) (vshs : List (VarName × Shape)) (prog : Prog α) (rshape : Shape)
    (h : List.lookup start functions = some (vshs, (prog, rshape))) :
    FLOOKUP (makeFuncsHOL functions) start = some (vshs, rshape) := by
  have hrewrite : FLOOKUP (makeFuncsHOL functions) start =
      List.lookup start
        (functions.map (fun entry => (entry.1, (entry.2.1, entry.2.2.2)))) := by
    rw [makeFuncsHOL]
    exact FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _
  rw [hrewrite, lookup_map_preserveFst
    (project := fun value : List (VarName × Shape) × Prog α × Shape =>
      (value.1, value.2.2))]
  rw [h]
  rfl

/-- General form of the compiled-function lookup: a source entry with
    parameters `vshs` and body `prog` is compiled to the entry whose argument
    slots are `crep_vars vshs` and whose body is `comp_func ... vshs prog`.
    This is the parameter-general companion of the
    `alookupCompileToCrepCode`; HOL discharges it inside
    `mk_ctxt_code_imp_code_rel` rather than as a separate theorem, so it
    deliberately carries no `@[hol]` tag. -/
theorem alookupCompileToCrepCodeGeneral
    (declarations : List (Decl (BitVec width)))
    (start : FunName) (vshs : List (VarName × Shape)) (prog : Prog (BitVec width))
    (rshape : Shape)
    (hlookup : List.lookup start (functionEntries declarations) =
      some (vshs, (prog, rshape))) :
    List.lookup start (compileToCrepHOL declarations) =
      some (panToCrepVars vshs, panToCrepCompFuncRiscV
        (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
          (panToCrepGetEidsFromDeclsHOL declarations)) vshs prog) := by
  obtain ⟨l₁, l₂, hdecomp, hnotin⟩ :=
    List.lookup_eq_some_iff.mp hlookup
  rw [compileToCrepHOL_eq_map]
  apply (List.lookup_eq_some_iff
    (b := (panToCrepVars vshs, panToCrepCompFuncRiscV
      (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
        (panToCrepGetEidsFromDeclsHOL declarations)) vshs prog))).mpr
  refine ⟨l₁.map (fun entry =>
      (entry.1, (panToCrepVars entry.2.1,
        panToCrepCompFuncRiscV
          (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
            (panToCrepGetEidsFromDeclsHOL declarations))
          entry.2.1 entry.2.2.1))),
    l₂.map (fun entry =>
      (entry.1, (panToCrepVars entry.2.1,
        panToCrepCompFuncRiscV
          (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
            (panToCrepGetEidsFromDeclsHOL declarations))
          entry.2.1 entry.2.2.1))), ?_, ?_⟩
  · rw [hdecomp, List.map_append, List.map_cons]
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa using hnotin q hq

/-- Production/proof-context bridge used by HOL `mk_ctxt_code_imp_code_rel`: the
    checked compiler's per-function body (`panToCrepCompFuncRiscV`) is the
    `codeRel` proof-context compilation (`compileCodeRelProg`) at the `ctxt_fc`
    context. The variable map agrees by `panToCrepMakeVmapHOL_eq_ctxtFcVars`
    and `vmax` by `maxList_range`. -/
theorem panToCrepCompFuncRiscV_eq_compileCodeRelProg
    (declarations : List (Decl (BitVec width)))
    (vshs : List (VarName × Shape)) (prog : Prog (BitVec width)) :
    panToCrepCompFuncRiscV
        (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
          (panToCrepGetEidsFromDeclsHOL declarations)) vshs prog =
      compileCodeRelProg
        (ctxtFc (functionInfosHOL declarations)
          (panToCrepGetEidsFromDeclsHOL declarations)
          (vshs.map Prod.fst) (vshs.map Prod.snd) (panToCrepVars vshs)) prog := by
  simp only [panToCrepCompFuncRiscV, compileProgRiscV, compileCodeRelProg,
    panToCrepMkCtxtHOL, ctxtFc]
  rw [panToCrepMakeVmapHOL_eq_ctxtFcVars vshs (functionInfosHOL declarations)
    (panToCrepGetEidsFromDeclsHOL declarations)]
  simp only [panToCrepVars, maxList_range, ctxtFc]

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL `mk_ctxt_code_imp_code_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4604`): with distinct
    function names and localised bodies, the checked compiler's code table is
    `code_rel` to the source function table under the `mk_ctxt`/`make_funcs`/
    `get_eids_from_decls` context. The source map is the finite-map list form
    (`FUPDATE_LIST … .reverse`), the `make_funcs` lookup drops the body
    (`makeFuncsHOL_lookup_of_lookup`), the target entry comes from
    `alookupCompileToCrepCodeGeneral`, and the compiled body is rewritten to
    `compileCodeRelProg` by `panToCrepCompFuncRiscV_eq_compileCodeRelProg`. Lean
    splits HOL's single `ctxt` record into `PanToCrepHOLContext`/
    `PanToCrepProofContext`, so the relation is stated with the proof-context
    literal (as for `mk_ctxt_imp_locals_rel`). The HOL-vs-Lean equivalence of
    the statement is reviewed by comparing the definitions (per SOUNDNESS). -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): this source-shaped theorem still uses
-- production carriers. Its input is `Decl (BitVec width)`, whose identifiers are
-- `String` and whose shapes are production `Shape`; its `codeRel` conclusion uses
-- String-keyed `PanToCrepProofContext` maps and production `CrepProg` code. HOL's
-- declaration, context, and code carriers instead use `mlstring`, `shape`, and
-- `crepLang$prog` respectively. The generic production `Prog (BitVec width)` does
-- not repair those surrounding carrier differences. Keep this useful theorem
-- untagged until the faithful identifier and compiler carriers are used. The
-- exact carrier work is tracked by `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`).
theorem mkCtxtCodeImpCodeRel [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (_hdistinct : ((functionEntries declarations).map Prod.fst).Nodup)
    (hlocalised : ∀ entry ∈ functionEntries declarations,
      localisedProg entry.2.2.1) :
    codeRel
      { vars := (FEMPTY : FiniteMap String (Shape × List Nat))
        funcs := functionInfosHOL declarations
        eids := panToCrepGetEidsFromDeclsHOL declarations
        vmax := 0 }
      (FUPDATE_LIST FEMPTY (functionEntries declarations).reverse)
      (FUPDATE_LIST FEMPTY (compileToCrepHOL declarations).reverse) := by
  intro function vshs prog rshape hsource
  rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup] at hsource
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨l₁, l₂, hdecomp, _hnotin⟩ := List.lookup_eq_some_iff.mp hsource
    have hmem : (function, vshs, prog, rshape) ∈ functionEntries declarations := by
      rw [hdecomp]
      simp
    have hloc := hlocalised (function, vshs, prog, rshape) hmem
    simpa using hloc
  · simp only []
    rw [functionInfosHOL_eq_makeFuncsHOL]
    exact makeFuncsHOL_lookup_of_lookup (functionEntries declarations)
      function vshs prog rshape hsource
  · simp only []
    rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup]
    rw [alookupCompileToCrepCodeGeneral declarations function vshs prog rshape
      hsource]
    rw [panToCrepCompFuncRiscV_eq_compileCodeRelProg]
    rfl

/-- Consumption adapter: a width-indexed `codeRelW` hypothesis is the generic
    `codeRel` at `BitVec width` (`codeRelW_iff_codeRel`), so the existing
    generic `codeRel` helper lemmas apply unchanged when the full correctness
    theorem is stated with `codeRelW`. -/
theorem codeRel_of_codeRelW (width : Nat)
    (context : PanToCrepProofContext (BitVec width))
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog (BitVec width) × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg (BitVec width)))
    (h : codeRelW width context sourceCode targetCode) :
    codeRel context sourceCode targetCode :=
  (codeRelW_iff_codeRel width context sourceCode targetCode).mp h

/-- The `mk_ctxt` initial-context code relation in the width-indexed HOL
    `code_rel_def`-shaped form (`codeRelW`, currently untagged), derived from the existing
    `mk_ctxt_code_imp_code_rel` port via `codeRelW_iff_codeRel`. This is the
    relation used at the start of the full `pc_compile_correct` statement. -/
theorem mkCtxtCodeImpCodeRelW [NeZero width] (declarations : List (Decl (BitVec width)))
    (_hdistinct : ((functionEntries declarations).map Prod.fst).Nodup)
    (hlocalised : ∀ entry ∈ functionEntries declarations,
      localisedProg entry.2.2.1) :
    codeRelW width
      { vars := (FEMPTY : FiniteMap String (Shape × List Nat))
        funcs := functionInfosHOL declarations
        eids := panToCrepGetEidsFromDeclsHOL declarations
        vmax := 0 }
      (FUPDATE_LIST FEMPTY (functionEntries declarations).reverse)
      (FUPDATE_LIST FEMPTY (compileToCrepHOL declarations).reverse) :=
  (codeRelW_iff_codeRel width _ _ _).mpr
    (mkCtxtCodeImpCodeRel declarations _hdistinct hlocalised)

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL
    `el_compile_prog_el_prog_eq`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4589-4599`): if the
    compiled table's entry at index `n` is `(start, [], cprog)`, the source
    names are distinct, `n` is in range, and the source table maps `start` to
    `([], p, rshape)`, then the source entry at `n` is exactly
    `(start, [], p, rshape)`.  The HOL `EL`/`ALL_DISTINCT`/`LENGTH`/`ALOOKUP`
    hypotheses appear here as the bounded `[n]?`, `Nodup`, `length`, and
    `lookupFunctionEntry`; the conclusion is the same indexed-table fact.  The
    HOL-vs-Lean equivalence of the statement is reviewed by comparing the
    definitions (per SOUNDNESS), not proved by this theorem.
    Direct HOL-EVAL rows are recorded in
    `scripts/hol-probes/crep_el_compile_probe.out` (`source_el_f=T`,
    `alookup_f=T`, `compiled_el_f=T`) and exercised by the `elCompileGuard`
    fixture and the worked `example` in
    `Flapjack/Test/PanToCrepCodeRelParity.lean:190-212`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port), source-reviewed: the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId` =
-- `String` (or embeds a `PanToCrepProofContext`/`PanToCrepHOLContext` whose
-- `FiniteMap`s are `String`-keyed), while HOL `pan_to_crepProofScript.sml` keys
-- names by `funname`/`varname`/`eid` = `mlstring`; the `Decl (BitVec width)`
-- list uses production `Shape` (`named : String`) rather than HOL word-indexed
-- `decl`/`shape`.  `names_as_string` cannot authorize the `Decl`/`Shape`/program
-- carriers, and no `NameRanged` byte witness applies (the conclusion is an
-- indexed-table equality, not a name).  The exact MlString carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem elCompileToCrepElProgEq [NeZero width]
    (declarations : List (Decl (BitVec width))) (n : Nat) (start : FunName)
    (cprog : CrepProg (BitVec width)) (p : Prog (BitVec width)) (rshape : Shape)
    (hentry : (compileToCrepHOL declarations)[n]? = some (start, [], cprog))
    (hdistinct : ((functionEntries declarations).map Prod.fst).Nodup)
    (_hlen : n < (functionEntries declarations).length)
    (hlookup : lookupFunctionEntry start (functionEntries declarations) =
      some ([], p, rshape)) :
    (functionEntries declarations)[n]? = some (start, [], p, rshape) := by
  rw [compileToCrepHOL_eq_map, List.getElem?_map] at hentry
  have hsome : (functionEntries declarations)[n]? ≠ none := by
    intro hnone
    rw [hnone] at hentry
    simp at hentry
  obtain ⟨entry, hentry_eq⟩ := Option.ne_none_iff_exists'.mp hsome
  have hproj :
      (entry.1, panToCrepVars entry.2.1,
        panToCrepCompFuncRiscV
          (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL declarations) 0
            (panToCrepGetEidsFromDeclsHOL declarations))
          entry.2.1 entry.2.2.1) = (start, [], cprog) := by
    rw [hentry_eq] at hentry
    simpa using hentry
  have h1 : entry.1 = start := by
    simpa using congrArg Prod.fst hproj
  have hlookupEntry :=
    lookupFunctionEntry_of_getElem? (functionEntries declarations) hdistinct hentry_eq
  rw [h1] at hlookupEntry
  rw [hlookup] at hlookupEntry
  have hp : (entry.2.1, entry.2.2.1, entry.2.2.2) = ([], p, rshape) :=
    (Option.some.inj hlookupEntry).symm
  have g1 : entry.2.1 = [] := by simpa using congrArg Prod.fst hp
  have g2 : entry.2.2.1 = p := by
    simpa using congrArg Prod.fst (congrArg Prod.snd hp)
  have g3 : entry.2.2.2 = rshape := by
    simpa using congrArg Prod.snd (congrArg Prod.snd hp)
  rw [hentry_eq]
  congr 1
  refine Prod.ext (by simpa using h1) ?_
  refine Prod.ext (by simpa using g1) ?_
  exact Prod.ext (by simpa using g2) (by simpa using g3)

/-- Flapjack analogue of HOL `first_compile_prog_all_distinct`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4556-4564`), which proves
    `ALL_DISTINCT (MAP FST (functions prog)) ==>
      ALL_DISTINCT (MAP FST (compile_prog prog))`. This theorem mirrors that
    statement shape (`Nodup`/`List.map`) and derives the `compileProgTopHOL`
    result from the `compileToCrepHOL` result above, but it quantifies over the
    production `Decl (BitVec width)` carrier with `String` identifiers and
    production `Shape`, and concludes about `compileProgTopHOL`, whose output
    uses production `FunName`/generic `CrepProg`. HOL instead quantifies over
    the `DeclHOL`/`panLang` carrier (`mlstring` identifiers and HOL
    expression/shape types) and concludes about the exact `compile_prog` output
    (`mlstring` names and `CrepProgHOL width` bodies). These input and output
    carrier differences are not covered by `names_as_string`; therefore this
    analogue is intentionally untagged and recorded as a documented mismatch in
    `docs/HOL-THEOREM-MAP.json`. An exact-carrier replacement depends on the
    `DeclHOL` and compiler-boundary work tracked by `flapjack-wur.1` (MlString
    carrier umbrella `flapjack-pxn.18.3.5.8`). Distinctness across the
    `compile_inl_top` boundary is exercised against the HOL EVAL row
    `duplicate_first` of `scripts/hol-probes/compile_prog_probe.out` by
    `Flapjack/Test/CompileProgParity.lean`. -/
theorem firstCompileProgAllDistinct {width : Nat} [NeZero width]
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

/-- `state_rel` records that source and target ffi states coincide; installing the
    same `call_FFI` result on both therefore preserves the whole relation (the
    other components are untouched, so they reduce definitionally). -/
theorem stateRel_ffiUpdate (source : PanSemState α (FfiState σ))
    (target : CrepRuntimeState α σ) (ffi : FfiState σ)
    (hrel : stateRel source target) :
    stateRel { source with ffi := ffi } { target with ffi := ffi } := by
  unfold stateRel at hrel ⊢
  obtain ⟨hm, hma, hsm, hst, hg, hcl, hbe, hffi, hba, hta⟩ := hrel
  exact ⟨hm, hma, hsm, hst, hg, hcl, hbe, rfl, hba, hta⟩

/-- Failing-read target-evaluation step for `ExtCall`: a failed configuration or
    array read returns `Error` with the target state unchanged (HOL `_ => (SOME
    Error, s)`), independently of the ffi state, and therefore also for a source
    state related by `stateRel`. -/
theorem crepRuntimeExtCallValues_stateRel_error
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (_hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (h : riscv64ReadByteArray base configuration configurationLength.toNat = none ∨
         riscv64ReadByteArray base array arrayLength.toNat = none) :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.error, riscv64CrepRuntimeTarget base) :=
  crepRuntimeExtCallValues_target_error base function configuration
    configurationLength array arrayLength h

/-- Source/target dispatch equation for `ExtCall` on the canonical
    RISC-V 64 target.  Given `stateRel source (riscv64CrepRuntimeTarget base)` and
    both argument reads, the production `crepRuntimeExtCallValues` step follows
    the Lean `callFfi` (HOL `call_FFI`) on the *source* ffi state: `FFI_return`
    yields `Normal` with the returned bytes written back and the returned ffi
    installed on the target, while `FFI_final` yields `FinalFFI` unchanged.  The
    separate `stateRel_ffiUpdate` lemma covers an ffi-only update; the write-back
    post-state is `crepRuntimeExtCallValues_stateRel_returned` (and the assembled
    dispatched form is `crepRuntimeExtCallValues_stateRel_dispatch_returned`).
    The failing-read case is `crepRuntimeExtCallValues_stateRel_error`, so the
    equations cover every production `ExtCall` dispatch outcome. -/
theorem crepRuntimeExtCallValues_stateRel_dispatch
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (configurationBytes arrayBytes : List UInt8)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configuration configurationLength.toNat =
      some configurationBytes)
    (ha : riscv64ReadByteArray base array arrayLength.toNat = some arrayBytes) :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (match callFfi source.ffi (.extCall function) configurationBytes arrayBytes with
       | .returned ffi bytes =>
           (.normal, riscv64WriteState { base with ffi := ffi } array bytes)
       | .final event => (.finalFfi event, riscv64CrepRuntimeTarget base)) := by
  have hffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  rw [crepRuntimeExtCallValues_target_dispatch base function configuration
    configurationLength array arrayLength configurationBytes arrayBytes hc ha, hffi]
  rfl

/-- Post-state `stateRel` for the `FFI_return` write-back branch of `ExtCall`.
    Given the source/target relation, the source `write_bytearray`
    (`panSemWriteBytearray` over the source memory) and the target
    `riscv64WriteState` (HOL `write_bytearray` over the canonical RISC-V target)
    remain related, with the returned ffi installed on both.  The memory
    conjunct is `panSemWriteBytearray_target_eq_riscv` (valid for every memory
    domain, including the HOL failed-store fallback); the remaining conjuncts are
    unchanged target fields.  This is the write-back companion of
    `stateRel_ffiUpdate`; the dispatched step result is
    `crepRuntimeExtCallValues_stateRel_dispatch_returned`. -/
theorem crepRuntimeExtCallValues_stateRel_returned
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (array : RiscV.Word 64) (bytes : List UInt8) (ffi : FfiState σ)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base)) :
    stateRel
      { source with
        memory := panSemWriteBytearray
          (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
          (riscv64PanValueFfiContext base.shMemaddrs) source.memory
          (8 : RiscV.Word 64) array bytes,
        ffi := ffi }
      (riscv64WriteState { base with ffi := ffi } array bytes) := by
  unfold stateRel at hstate ⊢
  obtain ⟨hm, hma, hsm, hst, hg, hcl, hbe, _hffi0, hba, hta⟩ := hstate
  have hmView : source.memory = panValueMemoryView base.memory := by
    rw [hm]; rfl
  have hmemT : (riscv64WriteState { base with ffi := ffi } array bytes).memory =
      (riscv64WriteState base array bytes).memory := by
    rw [riscv64WriteState_withFfi]
  have hffiT : (riscv64WriteState { base with ffi := ffi } array bytes).ffi = ffi := by
    rw [riscv64WriteState_withFfi]
  have hmaT : (riscv64WriteState { base with ffi := ffi } array bytes).memaddrs =
      base.memaddrs := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have hsmT : (riscv64WriteState { base with ffi := ffi } array bytes).shMemaddrs =
      base.shMemaddrs := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have hclkT : (riscv64WriteState { base with ffi := ffi } array bytes).clock =
      base.clock := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have hbeT : (riscv64WriteState { base with ffi := ffi } array bytes).bigEndian =
      false := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have hbaT : (riscv64WriteState { base with ffi := ffi } array bytes).baseAddress =
      base.baseAddress := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have htaT : (riscv64WriteState { base with ffi := ffi } array bytes).topAddress =
      base.topAddress := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmView, panSemWriteBytearray_target_eq_riscv base array bytes, hmemT]
    rfl
  · rw [hmaT]; exact hma
  · rw [hsmT]; exact hsm
  · exact hst
  · exact hg
  · rw [hclkT]; exact hcl
  · rw [hbeT]; exact hbe
  · rw [hffiT]
  · rw [hbaT]; exact hba
  · rw [htaT]; exact hta

/-- The dispatched production `ExtCall` step when `call_ffi` returns
    (`FFI_return`): the target step is `Normal` with the returned bytes written
    back, and the source/target post-states are related (`stateRel`).  Connects
    the read/handler premises of `crepRuntimeExtCallValues_target_returned` to
    the post-state relation of `crepRuntimeExtCallValues_stateRel_returned`. -/
theorem crepRuntimeExtCallValues_stateRel_dispatch_returned
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (configurationBytes arrayBytes : List UInt8) (ffi : FfiState σ)
    (bytes : List UInt8)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configuration configurationLength.toNat =
      some configurationBytes)
    (ha : riscv64ReadByteArray base array arrayLength.toNat = some arrayBytes)
    (hr : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .returned ffi bytes) :
    (crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.normal, riscv64WriteState { base with ffi := ffi } array bytes)) ∧
    stateRel
      { source with
        memory := panSemWriteBytearray
          (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
          (riscv64PanValueFfiContext base.shMemaddrs) source.memory
          (8 : RiscV.Word 64) array bytes,
        ffi := ffi }
      (riscv64WriteState { base with ffi := ffi } array bytes) :=
  ⟨crepRuntimeExtCallValues_target_returned base function configuration
      configurationLength array arrayLength configurationBytes arrayBytes hc ha
      ffi bytes hr,
   crepRuntimeExtCallValues_stateRel_returned source base array bytes ffi hstate⟩

/-- Four-local production `ExtCall` wrapper dispatch.  The actual Crep runtime
    entry point `crepRuntimeExtCall` looks the four arguments up in the target
    `locals` (Nat-indexed, the target image of HOL `FLOOKUP s.locals`), reads the
    configuration/array bytes from the target memory, and runs the same
    `crepRuntimeExtCallValues` step.  Given those four local lookups (each holding
    a `.word`) and the canonical-target argument reads, the wrapper's `FFI_return`
    result is `Normal` with the returned bytes written back, and the source
    `PanSemState` (`panSemWriteBytearray` over the source memory) and the target
    `riscv64WriteState` post-states stay related, with the returned ffi installed
    on both.  This is the four-local companion of
    `crepRuntimeExtCallValues_stateRel_dispatch_returned`: the source post-state is
    built by the theorem, not assumed.  Flapjack-only bridge (no HOL original). -/
theorem crepRuntimeExtCall_stateRel_dispatch_returned
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (configurationBytes arrayBytes : List UInt8) (ffi : FfiState σ)
    (bytes : List UInt8)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configurationValue
      configurationLengthValue.toNat = some configurationBytes)
    (ha : riscv64ReadByteArray base arrayValue arrayLengthValue.toNat =
      some arrayBytes)
    (hr : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .returned ffi bytes) :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.normal, riscv64WriteState { base with ffi := ffi } arrayValue bytes)) ∧
    stateRel
      { source with
        memory := panSemWriteBytearray
          (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
          (riscv64PanValueFfiContext base.shMemaddrs) source.memory
          (8 : RiscV.Word 64) arrayValue bytes,
        ffi := ffi }
      (riscv64WriteState { base with ffi := ffi } arrayValue bytes) := by
  have hlocals : (riscv64CrepRuntimeTarget base).locals = base.locals := rfl
  have hwrapper : crepRuntimeExtCall riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget base) function configuration configurationLength
      array arrayLength =
      crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function configurationValue
        configurationLengthValue arrayValue arrayLengthValue := by
    simp only [crepRuntimeExtCall, hlocals]
    rw [hconfiguration, hconfigurationLength, harray, harrayLength]
    rfl
  rw [hwrapper]
  exact crepRuntimeExtCallValues_stateRel_dispatch_returned source base function
    configurationValue configurationLengthValue arrayValue arrayLengthValue
    configurationBytes arrayBytes ffi bytes hstate hc ha hr

/-- Non-returned `FFI_final` dispatch of `crepRuntimeExtCallValues`.  When the
    handler reports a `final` event, HOL `call_FFI` returns `(SOME (FinalFFI
    outcome), s)` with the state unchanged, so the target step is `FinalFFI` with
    `riscv64CrepRuntimeTarget base` and the source/target states stay exactly the
    related pre-states.  This is the non-returned companion of
    `crepRuntimeExtCallValues_stateRel_dispatch_returned`; the failing-read case
    is `crepRuntimeExtCallValues_stateRel_error`. -/
theorem crepRuntimeExtCallValues_stateRel_dispatch_final
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (configurationBytes arrayBytes : List UInt8) (event : FfiFinalEvent)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configuration configurationLength.toNat =
      some configurationBytes)
    (ha : riscv64ReadByteArray base array arrayLength.toNat = some arrayBytes)
    (hf : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .final event) :
    (crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.finalFfi event, riscv64CrepRuntimeTarget base)) ∧
    stateRel source (riscv64CrepRuntimeTarget base) :=
  ⟨crepRuntimeExtCallValues_target_final base function configuration
      configurationLength array arrayLength configurationBytes arrayBytes hc ha
      event hf,
   hstate⟩

/-- Four-local production `ExtCall` wrapper dispatch for the failing-read branch
    (HOL `_ => (SOME Error, s)`).  The wrapper's argument lookups succeed but the
    configuration or array read fails, so the step is `Error` with the target state
    unchanged and the source/target states stay related.  Flapjack-only bridge (no
    HOL original). -/
theorem crepRuntimeExtCall_stateRel_error
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (h : riscv64ReadByteArray base configurationValue configurationLengthValue.toNat =
        none ∨
         riscv64ReadByteArray base arrayValue arrayLengthValue.toNat = none) :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.error, riscv64CrepRuntimeTarget base)) ∧
    stateRel source (riscv64CrepRuntimeTarget base) := by
  have hlocals : (riscv64CrepRuntimeTarget base).locals = base.locals := rfl
  have hwrapper : crepRuntimeExtCall riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget base) function configuration configurationLength
      array arrayLength =
      crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function configurationValue
        configurationLengthValue arrayValue arrayLengthValue := by
    simp only [crepRuntimeExtCall, hlocals]
    rw [hconfiguration, hconfigurationLength, harray, harrayLength]
    rfl
  rw [hwrapper]
  exact ⟨crepRuntimeExtCallValues_target_error base function configurationValue
      configurationLengthValue arrayValue arrayLengthValue h, hstate⟩

/-- Four-local production `ExtCall` wrapper dispatch for the non-returned
    `FFI_final` branch: the wrapper resolves its four locals, the reads succeed and
    the handler reports a `final` event, so the step is `FinalFFI` with the target
    state unchanged and the source/target states stay related.  This is the
    four-local companion of `crepRuntimeExtCallValues_stateRel_dispatch_final`.
    Flapjack-only bridge (no HOL original). -/
theorem crepRuntimeExtCall_stateRel_dispatch_final
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (configurationBytes arrayBytes : List UInt8) (event : FfiFinalEvent)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configurationValue
      configurationLengthValue.toNat = some configurationBytes)
    (ha : riscv64ReadByteArray base arrayValue arrayLengthValue.toNat =
      some arrayBytes)
    (hf : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .final event) :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.finalFfi event, riscv64CrepRuntimeTarget base)) ∧
    stateRel source (riscv64CrepRuntimeTarget base) := by
  have hlocals : (riscv64CrepRuntimeTarget base).locals = base.locals := rfl
  have hwrapper : crepRuntimeExtCall riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget base) function configuration configurationLength
      array arrayLength =
      crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function configurationValue
        configurationLengthValue arrayValue arrayLengthValue := by
    simp only [crepRuntimeExtCall, hlocals]
    rw [hconfiguration, hconfigurationLength, harray, harrayLength]
    rfl
  rw [hwrapper]
  exact crepRuntimeExtCallValues_stateRel_dispatch_final source base function
    configurationValue configurationLengthValue arrayValue arrayLengthValue
    configurationBytes arrayBytes event hstate hc ha hf

/-- One-shot dispatch of the four-local production `crepRuntimeExtCall` wrapper on
    the canonical RISC-V 64 target.  This is the four-local companion of
    `crepRuntimeExtCallValues_target_dispatch_any`: after resolving the four source
    locals it reduces to `crepRuntimeExtCallValues`, so its result is the Lean
    `callFfi` (HOL `call_FFI`) match over the two `read_bytearray`s: `FFI_return`
    yields `Normal` with the returned bytes written back and the returned ffi
    installed, `FFI_final` yields `FinalFFI`, and a failed read yields `Error`.
    Flapjack-only bridge (no HOL original); it assembles the branch lemmas
    `crepRuntimeExtCall_stateRel_dispatch_returned`,
    `crepRuntimeExtCall_stateRel_dispatch_final` and `crepRuntimeExtCall_stateRel_error`. -/
theorem crepRuntimeExtCall_dispatch
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue)) :
    crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (match riscv64ReadByteArray base configurationValue configurationLengthValue.toNat,
             riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
       | some configurationBytes, some arrayBytes =>
           (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | .returned ffi bytes =>
                (.normal, riscv64WriteState { base with ffi := ffi } arrayValue bytes)
            | .final event => (.finalFfi event, riscv64CrepRuntimeTarget base))
       | _, _ => (.error, riscv64CrepRuntimeTarget base)) := by
  have hlocals : (riscv64CrepRuntimeTarget base).locals = base.locals := rfl
  simp only [crepRuntimeExtCall, hlocals]
  rw [hconfiguration, hconfigurationLength, harray, harrayLength]
  exact crepRuntimeExtCallValues_target_dispatch_any base function configurationValue
    configurationLengthValue arrayValue arrayLengthValue

/-- Assembled four-local `ExtCall` dispatch with source/target post-state relation:
    the wrapper's one-shot dispatch matches the `call_FFI`-shaped branch selection,
    and the corresponding post-states remain related (`stateRel`).  The source
    post-state is built by the theorem (the `write_bytearray`-based memory update on
    `FFI_return`, otherwise unchanged), never assumed; there is no target-run or
    post-state premise.  This packages every branch of
    `crepRuntimeExtCall_stateRel_dispatch_returned`/`_dispatch_final`/`_error` into a
    single case-split.  Flapjack-only bridge (no HOL original). -/
theorem crepRuntimeExtCall_stateRel_dispatch
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (hstate : stateRel source (riscv64CrepRuntimeTarget base)) :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (match riscv64ReadByteArray base configurationValue configurationLengthValue.toNat,
             riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
       | some configurationBytes, some arrayBytes =>
           (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | .returned ffi bytes =>
                (.normal, riscv64WriteState { base with ffi := ffi } arrayValue bytes)
            | .final event => (.finalFfi event, riscv64CrepRuntimeTarget base))
       | _, _ => (.error, riscv64CrepRuntimeTarget base))) ∧
    stateRel
      (match riscv64ReadByteArray base configurationValue configurationLengthValue.toNat,
             riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
       | some configurationBytes, some arrayBytes =>
           (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | .returned ffi bytes =>
                { source with
                  memory := panSemWriteBytearray
                    (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
                    (riscv64PanValueFfiContext base.shMemaddrs) source.memory
                    (8 : RiscV.Word 64) arrayValue bytes,
                  ffi := ffi }
            | .final _event => source)
       | _, _ => source)
      (match riscv64ReadByteArray base configurationValue configurationLengthValue.toNat,
             riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
       | some configurationBytes, some arrayBytes =>
           (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | .returned ffi bytes =>
                riscv64WriteState { base with ffi := ffi } arrayValue bytes
            | .final _event => riscv64CrepRuntimeTarget base)
       | _, _ => riscv64CrepRuntimeTarget base) := by
  constructor
  · exact crepRuntimeExtCall_dispatch base function configuration configurationLength
      array arrayLength configurationValue configurationLengthValue arrayValue
      arrayLengthValue hconfiguration hconfigurationLength harray harrayLength
  · cases hc : riscv64ReadByteArray base configurationValue configurationLengthValue.toNat with
    | none => simpa only [hc] using hstate
    | some configurationBytes =>
        cases ha : riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
        | none => simpa only [hc, ha] using hstate
        | some arrayBytes =>
            cases hf : callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | returned ffi bytes =>
                simpa only [hc, ha, hf] using
                  crepRuntimeExtCallValues_stateRel_returned source base arrayValue bytes ffi
                    hstate
            | final _event => simpa only [hc, ha, hf] using hstate

/-- Source-evaluator ExtCall step: from a genuine `panValueFfiExtCall` outcome
    (`FFI_return` write-back) on a source state related to the canonical RISC-V
    64 target, derive the target `crepRuntimeExtCall` result and the post-state
    `stateRel`.  No hypothesis states the target result or the post-relation;
    the returned bytes are derived from the source `call_FFI` outcome. -/
theorem panValueFfiExtCall_stateRel_target
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (nextMemory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (nextFfi : FfiState σ)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hsource : panValueFfiExtCall
        (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
        (riscv64PanValueFfiContext base.shMemaddrs) source.memory
        (8 : RiscV.Word 64) source.ffi function
        configurationValue configurationLengthValue arrayValue arrayLengthValue =
      some (.returned nextMemory nextFfi)) :
    ∃ arrayBytes bytes,
      riscv64ReadByteArray base arrayValue arrayLengthValue.toNat = some arrayBytes ∧
      crepRuntimeExtCall riscv64ExtCallCallFfiHandler
          (riscv64CrepRuntimeTarget base) function
          configuration configurationLength array arrayLength =
        (.normal, riscv64WriteState { base with ffi := nextFfi } arrayValue bytes) ∧
      nextMemory =
        panValueMemoryView
          (riscv64WriteState { base with ffi := nextFfi } arrayValue bytes).memory ∧
      stateRel { source with memory := nextMemory, ffi := nextFfi }
        (riscv64WriteState { base with ffi := nextFfi } arrayValue bytes) := by
  obtain ⟨configurationBytes, arrayBytes, bytes, hcr, har, hffiR, hmem⟩ :=
    panValueFfiExtCall_returned_inv
      (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
      (riscv64PanValueFfiContext base.shMemaddrs) source.memory
      (8 : RiscV.Word 64) source.ffi function
      configurationValue configurationLengthValue arrayValue arrayLengthValue
      nextMemory nextFfi hsource
  have hmemView : source.memory = panValueMemoryView base.memory := hstate.1
  rw [hmemView] at hcr har
  rw [riscv64PanValueFfiContext_valueToNat_eq_riscv] at hcr har
  rw [panValueFfiReadBytes_view_eq_riscv] at hcr har
  have hbaseffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  have hfBase : callFfi base.ffi (.extCall function)
      configurationBytes arrayBytes = .returned nextFfi bytes := by
    rw [hbaseffi]; exact hffiR
  have hdispatch := crepRuntimeExtCall_stateRel_dispatch source base
    function configuration configurationLength array arrayLength
    configurationValue configurationLengthValue arrayValue arrayLengthValue
    hconfiguration hconfigurationLength harray harrayLength hstate
  refine ⟨arrayBytes, bytes, har, ?_, ?_, ?_⟩
  · rw [hdispatch.1]
    simp only [hcr, har, hfBase]
  · rw [hmem, panValueFfiWriteBytes_eq_panSemWriteBytearray, hmemView,
      panSemWriteBytearray_target_eq_riscv]
    conv => rhs; rw [riscv64WriteState_withFfi]
  · rw [hmem, panValueFfiWriteBytes_eq_panSemWriteBytearray]
    simpa only [hcr, har, hfBase] using hdispatch.2

/-- A successful source `sh_mem_load` outcome drives the target shared-memory
    `load` dispatch: the mapped read reaches `callFfi` with the HOL `SharedMem
    MappedRead` name and width byte, the loaded word is installed into the named
    local, and the ffi-only source update is a `stateRel` post-state.  The target
    dispatch and post-state are derived from the source evaluator outcome, not
    assumed.  HOL `sh_mem_load` (`panSemScript.sml:510`).  Direct oracle:
    `scripts/hol-probes/crep_runtime_shared_mem_probe.out`. -/
theorem panValueFfiSharedLoad_stateRel_target
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (size : OpSize) (name : Nat) (address : RiscV.Word 64)
    (nextFfi : FfiState σ) (value : RiscV.Word 64)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hsource : panValueFfiSharedLoad (riscv64PanValueFfiContext base.shMemaddrs)
        source.ffi size address = some (.loaded nextFfi value)) :
    crepRuntimeSharedMem riscv64SharedMemCallFfiHandler
        (riscv64CrepRuntimeTarget base) (opSizeToCrepLoadOp size) name address =
      (.normal, { riscv64CrepRuntimeTarget base with
        ffi := nextFfi,
        locals := updateCrepRuntimeLocal (riscv64CrepRuntimeTarget base).locals
          name (.word value) }) ∧
    stateRel { source with ffi := nextFfi }
      { riscv64CrepRuntimeTarget base with
        ffi := nextFfi,
        locals := updateCrepRuntimeLocal (riscv64CrepRuntimeTarget base).locals
          name (.word value) } := by
  obtain ⟨hdom, bytes, hcall, hvalue⟩ :=
    panValueFfiSharedLoad_loaded_inv (riscv64PanValueFfiContext base.shMemaddrs)
      source.ffi size address nextFfi value hsource
  have hbaseffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  have hcallBase : callFfi base.ffi (.sharedMem .mappedRead)
      [UInt8.ofNat (panValueFfiWidth size)]
      ((riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false) =
        .returned nextFfi bytes := by
    rw [hbaseffi]; exact hcall
  have hvalid : crepRuntimeSharedAddressValid (riscv64CrepRuntimeTarget base)
      (opSizeToCrepLoadOp size) address = true := by
    rw [crepRuntimeSharedAddressValid_opSizeToCrepLoadOp]; exact hdom
  constructor
  · cases size <;>
      (simp only [opSizeToCrepLoadOp] at hvalid
       simp only [panValueFfiWidth] at hcallBase
       simp only [opSizeToCrepLoadOp, crepRuntimeMemWidth,
         riscv64CrepRuntimeTarget_ffi, riscv64CrepRuntimeTarget_ffiContext,
         riscv64SharedMemCallFfiHandler_sharedMem, crepSharedMemOperator,
         crepRuntimeSharedMem, setCrepRuntimeLocal_eq_update, hvalid, if_true,
         hcallBase, ← hvalue])
  · simpa only [stateRel] using stateRel_ffiUpdate source (riscv64CrepRuntimeTarget base)
      nextFfi hstate

/-- A successful source `sh_mem_store` outcome drives the target shared-memory
    `store` dispatch: the mapped write reaches `callFfi` with the HOL `SharedMem
    MappedWrite` name, the width byte, and the HOL payload, and the ffi-only
    result is a `stateRel` post-state.  HOL `sh_mem_store`
    (`panSemScript.sml:527`).  Direct oracle:
    `scripts/hol-probes/crep_runtime_shared_mem_probe.out`. -/
theorem panValueFfiSharedStore_stateRel_target
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (size : OpSize) (name : Nat) (address : RiscV.Word 64)
    (value : RiscV.Word 64)
    (hname : (riscv64CrepRuntimeTarget base).locals name = some (.word value))
    (nextFfi : FfiState σ)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hsource : panValueFfiSharedStore (riscv64PanValueFfiContext base.shMemaddrs)
        source.ffi size address value = some (.stored nextFfi)) :
    crepRuntimeSharedMem riscv64SharedMemCallFfiHandler
        (riscv64CrepRuntimeTarget base) (opSizeToCrepStoreOp size) name address =
      (.normal, { riscv64CrepRuntimeTarget base with ffi := nextFfi }) ∧
    stateRel { source with ffi := nextFfi }
      { riscv64CrepRuntimeTarget base with ffi := nextFfi } := by
  obtain ⟨hdom, bytes, hcall⟩ :=
    panValueFfiSharedStore_stored_inv (riscv64PanValueFfiContext base.shMemaddrs)
      source.ffi size address value nextFfi hsource
  have hbaseffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  have hcallBase : callFfi base.ffi (.sharedMem .mappedWrite)
      [UInt8.ofNat (panValueFfiWidth size)]
      (if panValueFfiWidth size = 0 then
          (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false
        else
          ((riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false).take
              (panValueFfiWidth size) ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false) =
        .returned nextFfi bytes := by
    rw [hbaseffi]; exact hcall
  have hvalid : crepRuntimeSharedAddressValid (riscv64CrepRuntimeTarget base)
      (opSizeToCrepStoreOp size) address = true := by
    rw [crepRuntimeSharedAddressValid_opSizeToCrepStoreOp]; exact hdom
  have hcallGoal : callFfi base.ffi (.sharedMem .mappedWrite)
      [UInt8.ofNat (crepRuntimeMemWidth (opSizeToCrepStoreOp size))]
      (if crepRuntimeMemWidth (opSizeToCrepStoreOp size) = 0 then
          (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false
        else
          ((riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false).take
              (crepRuntimeMemWidth (opSizeToCrepStoreOp size)) ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false) =
        .returned nextFfi bytes := by
    rw [crepRuntimeSharedStorePayload_eq (riscv64PanValueFfiContext base.shMemaddrs)
      value address size]
    rw [crepRuntimeMemWidth_opSizeToCrepStoreOp]
    exact hcallBase
  constructor
  · cases size <;>
      (simp only [opSizeToCrepStoreOp] at hvalid
       simp only [opSizeToCrepStoreOp,
         riscv64CrepRuntimeTarget_ffi, riscv64CrepRuntimeTarget_ffiContext,
         riscv64SharedMemCallFfiHandler_sharedMem, crepSharedMemOperator,
         crepRuntimeSharedMem, hname, Option.map_some, panTheWord, hvalid, if_true]
       erw [hcallGoal])
  · simpa only [stateRel] using stateRel_ffiUpdate source (riscv64CrepRuntimeTarget base)
      nextFfi hstate

/-- The source `sh_mem_load` `FFI_final` outcome drives the target shared-memory
    `load` dispatch to `FinalFFI` with the locals cleared and the pre-state
    relation (HOL `(SOME FinalFFI, empty_locals s)`).  Direct oracle:
    `scripts/hol-probes/crep_runtime_shared_mem_probe.out` (`load_final`). -/
theorem panValueFfiSharedLoad_stateRel_final
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (size : OpSize) (name : Nat) (address : RiscV.Word 64)
    (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hsource : panValueFfiSharedLoad (riscv64PanValueFfiContext base.shMemaddrs)
        source.ffi size address = some (.final nextFfi event)) :
    crepRuntimeSharedMem riscv64SharedMemCallFfiHandler
        (riscv64CrepRuntimeTarget base) (opSizeToCrepLoadOp size) name address =
      (.finalFfi event,
        clearCrepRuntimeLocals (riscv64CrepRuntimeTarget base)) ∧
    stateRel { source with ffi := nextFfi }
      (clearCrepRuntimeLocals (riscv64CrepRuntimeTarget base)) := by
  obtain ⟨hdom, hffi, hcall⟩ :=
    panValueFfiSharedLoad_final_inv (riscv64PanValueFfiContext base.shMemaddrs)
      source.ffi size address nextFfi event hsource
  subst hffi
  have hbaseffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  have hcallBase : callFfi base.ffi (.sharedMem .mappedRead)
      [UInt8.ofNat (panValueFfiWidth size)]
      ((riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false) =
        .final event := by
    rw [hbaseffi]; exact hcall
  have hvalid : crepRuntimeSharedAddressValid (riscv64CrepRuntimeTarget base)
      (opSizeToCrepLoadOp size) address = true := by
    rw [crepRuntimeSharedAddressValid_opSizeToCrepLoadOp]; exact hdom
  constructor
  · cases size <;>
      (simp only [opSizeToCrepLoadOp] at hvalid
       simp only [panValueFfiWidth] at hcallBase
       simp only [opSizeToCrepLoadOp, crepRuntimeMemWidth,
         riscv64CrepRuntimeTarget_ffi, riscv64CrepRuntimeTarget_ffiContext,
         riscv64SharedMemCallFfiHandler_sharedMem, crepSharedMemOperator,
         crepRuntimeSharedMem, clearCrepRuntimeLocals, hvalid, if_true,
         hcallBase])
  · simpa only [stateRel, clearCrepRuntimeLocals] using hstate

/-- The source `sh_mem_store` `FFI_final` outcome drives the target
    shared-memory `store` dispatch to `FinalFFI` with the pre-state relation
    (HOL `(SOME FinalFFI, s)`).  Direct oracle:
    `scripts/hol-probes/crep_runtime_shared_mem_probe.out` (`store_final`). -/
theorem panValueFfiSharedStore_stateRel_final
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (size : OpSize) (name : Nat) (address : RiscV.Word 64)
    (value : RiscV.Word 64)
    (hname : (riscv64CrepRuntimeTarget base).locals name = some (.word value))
    (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hsource : panValueFfiSharedStore (riscv64PanValueFfiContext base.shMemaddrs)
        source.ffi size address value = some (.final nextFfi event)) :
    crepRuntimeSharedMem riscv64SharedMemCallFfiHandler
        (riscv64CrepRuntimeTarget base) (opSizeToCrepStoreOp size) name address =
      (.finalFfi event, riscv64CrepRuntimeTarget base) ∧
    stateRel { source with ffi := nextFfi }
      (riscv64CrepRuntimeTarget base) := by
  obtain ⟨hdom, hffi, hcall⟩ :=
    panValueFfiSharedStore_final_inv (riscv64PanValueFfiContext base.shMemaddrs)
      source.ffi size address value nextFfi event hsource
  subst hffi
  have hbaseffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  have hcallBase : callFfi base.ffi (.sharedMem .mappedWrite)
      [UInt8.ofNat (panValueFfiWidth size)]
      (if panValueFfiWidth size = 0 then
          (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false
        else
          ((riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false).take
              (panValueFfiWidth size) ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false) =
        .final event := by
    rw [hbaseffi]; exact hcall
  have hvalid : crepRuntimeSharedAddressValid (riscv64CrepRuntimeTarget base)
      (opSizeToCrepStoreOp size) address = true := by
    rw [crepRuntimeSharedAddressValid_opSizeToCrepStoreOp]; exact hdom
  have hcallGoal : callFfi base.ffi (.sharedMem .mappedWrite)
      [UInt8.ofNat (crepRuntimeMemWidth (opSizeToCrepStoreOp size))]
      (if crepRuntimeMemWidth (opSizeToCrepStoreOp size) = 0 then
          (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false
        else
          ((riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false).take
              (crepRuntimeMemWidth (opSizeToCrepStoreOp size)) ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false) =
        .final event := by
    rw [crepRuntimeSharedStorePayload_eq (riscv64PanValueFfiContext base.shMemaddrs)
      value address size]
    rw [crepRuntimeMemWidth_opSizeToCrepStoreOp]
    exact hcallBase
  constructor
  · cases size <;>
      (simp only [opSizeToCrepStoreOp] at hvalid
       simp only [opSizeToCrepStoreOp, riscv64CrepRuntimeTarget_ffi,
         riscv64CrepRuntimeTarget_ffiContext,
         riscv64SharedMemCallFfiHandler_sharedMem, crepSharedMemOperator,
         crepRuntimeSharedMem, hname, Option.map_some, panTheWord, hvalid, if_true]
       erw [hcallGoal])
  · simpa only [stateRel] using hstate

private theorem compileProgHOL_call_none [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α)) :
    compileProgHOL context (Prog.call none function arguments) =
      CrepProg.call none function (compileArgsHOL context arguments) := by
  simp only [compileProgHOL.eq_def] <;> rfl

private theorem compileProgHOL_call_destNone_handlerNone [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α)) :
    compileProgHOL context (Prog.call (some (none, none)) function arguments) =
      nestedDecs (functionReturnNamesHOL context function)
        ((functionReturnNamesHOL context function).map (fun _ => CrepExp.const 0))
        (CrepProg.call (some (functionReturnNamesHOL context function, none)) function
          (compileArgsHOL context arguments)) := by
  simp only [compileProgHOL.eq_def] <;> rfl

private theorem compileProgHOL_call_destNone_handlerSome_eidsNone [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α))
    (exception : ExceptionId) (handlerVar : VarName) (handlerProgram : Prog α)
    (heid : FLOOKUP context.eids exception = none) :
    compileProgHOL context (Prog.call (some (none, some (exception, handlerVar, handlerProgram))) function arguments) =
      nestedDecs (functionReturnNamesHOL context function)
        ((functionReturnNamesHOL context function).map (fun _ => CrepExp.const 0))
        (CrepProg.call (some (functionReturnNamesHOL context function, none)) function
          (compileArgsHOL context arguments)) := by
  simp only [compileProgHOL.eq_def, heid] <;> rfl

private theorem compileProgHOL_call_destNone_handlerSome_eidsSome [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α))
    (exception : ExceptionId) (handlerVar : VarName) (handlerProgram : Prog α)
    (code : α) (heid : FLOOKUP context.eids exception = some code) :
    compileProgHOL context (Prog.call (some (none, some (exception, handlerVar, handlerProgram))) function arguments) =
      nestedDecs (functionReturnNamesHOL context function)
        ((functionReturnNamesHOL context function).map (fun _ => CrepExp.const 0))
        (CrepProg.call (some (functionReturnNamesHOL context function,
            some (code, CrepProg.seq (expHdlFiniteMap context.vars handlerVar)
              (compileProgHOL context handlerProgram)))) function
          (compileArgsHOL context arguments)) := by
  rw [compileProgHOL.eq_def]
  simp only [heid] <;> rfl

private theorem compileProgHOL_call_destSome_nocall_handlerNone [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α))
    (kind : VarKind) (name : VarName)
    (hcall : callDestinationNamesHOL context kind name = none) :
    compileProgHOL context (Prog.call (some (some (kind, name), none)) function arguments) =
      CrepProg.call none function (compileArgsHOL context arguments) := by
  simp only [compileProgHOL.eq_def, hcall] <;> rfl

private theorem compileProgHOL_call_destSome_nocall_handlerSome_eidsNone [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α))
    (kind : VarKind) (name : VarName)
    (hcall : callDestinationNamesHOL context kind name = none)
    (exception : ExceptionId) (handlerVar : VarName) (handlerProgram : Prog α)
    (heid : FLOOKUP context.eids exception = none) :
    compileProgHOL context (Prog.call (some (some (kind, name), some (exception, handlerVar, handlerProgram))) function arguments) =
      CrepProg.call none function (compileArgsHOL context arguments) := by
  simp only [compileProgHOL.eq_def, hcall, heid] <;> rfl

private theorem compileProgHOL_call_destSome_nocall_handlerSome_eidsSome [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α))
    (kind : VarKind) (name : VarName)
    (hcall : callDestinationNamesHOL context kind name = none)
    (exception : ExceptionId) (handlerVar : VarName) (handlerProgram : Prog α)
    (code : α) (heid : FLOOKUP context.eids exception = some code) :
    compileProgHOL context (Prog.call (some (some (kind, name), some (exception, handlerVar, handlerProgram))) function arguments) =
      CrepProg.call (some ([], some (code, CrepProg.seq (expHdlFiniteMap context.vars handlerVar)
          (compileProgHOL context handlerProgram)))) function
        (compileArgsHOL context arguments) := by
  rw [compileProgHOL.eq_def]
  simp only [hcall, heid] <;> rfl

private theorem compileProgHOL_call_destSome_somecall_handlerNone [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α))
    (kind : VarKind) (name : VarName) (names : List Nat)
    (hcall : callDestinationNamesHOL context kind name = some names) :
    compileProgHOL context (Prog.call (some (some (kind, name), none)) function arguments) =
      CrepProg.call (some (names, none)) function (compileArgsHOL context arguments) := by
  simp only [compileProgHOL.eq_def, hcall] <;> rfl

private theorem compileProgHOL_call_destSome_somecall_handlerSome_eidsNone [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α))
    (kind : VarKind) (name : VarName) (names : List Nat)
    (hcall : callDestinationNamesHOL context kind name = some names)
    (exception : ExceptionId) (handlerVar : VarName) (handlerProgram : Prog α)
    (heid : FLOOKUP context.eids exception = none) :
    compileProgHOL context (Prog.call (some (some (kind, name), some (exception, handlerVar, handlerProgram))) function arguments) =
      CrepProg.call (some (names, none)) function (compileArgsHOL context arguments) := by
  simp only [compileProgHOL.eq_def, hcall, heid] <;> rfl

private theorem compileProgHOL_call_destSome_somecall_handlerSome_eidsSome [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (function : FunName) (arguments : List (Exp α))
    (kind : VarKind) (name : VarName) (names : List Nat)
    (hcall : callDestinationNamesHOL context kind name = some names)
    (exception : ExceptionId) (handlerVar : VarName) (handlerProgram : Prog α)
    (code : α) (heid : FLOOKUP context.eids exception = some code) :
    compileProgHOL context (Prog.call (some (some (kind, name), some (exception, handlerVar, handlerProgram))) function arguments) =
      CrepProg.call (some (names, some (code, CrepProg.seq (expHdlFiniteMap context.vars handlerVar)
          (compileProgHOL context handlerProgram)))) function
        (compileArgsHOL context arguments) := by
  rw [compileProgHOL.eq_def]
  simp only [hcall, heid] <;> rfl

/-- Workhorse for Cake `not_mem_context_assigned_mem_gt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1252`): any slot above the
    context bound cannot be assigned by `compileProgHOL`, provided no context
    variable's slot list contains it.  Proved by strong induction on
    `sizeOf program` because `Prog` is a nested inductive type whose generated
    induction principle is not usable. -/
theorem compileProgHOL_not_mem_assignedFreeVars
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α] :
    ∀ (program : Prog α) (context : PanToCrepHOLContext α) (x : Nat),
      (∀ v sh ns', FLOOKUP context.vars v = some (sh, ns') → x ∉ ns') →
      x ≤ context.vmax →
      x ∉ crepAssignedFreeVars (compileProgHOL context program) := by
  have main : ∀ n, ∀ (program : Prog α), sizeOf program = n →
      ∀ (context : PanToCrepHOLContext α) (x : Nat),
        (∀ v sh ns', FLOOKUP context.vars v = some (sh, ns') → x ∉ ns') →
        x ≤ context.vmax →
        x ∉ crepAssignedFreeVars (compileProgHOL context program) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro program hn context x hfresh hx
      cases program with
      | skip => simp [compileProgHOL, crepAssignedFreeVars]
      | dec name shape value body =>
          cases hcomp : compileExpHOL context value with
          | mk expressions compiledShape =>
            simp only [compileProgHOL, hcomp]
            split
            · next hlen =>
              intro hmem
              rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _
                (by rw [allocatedNamesHOL_length]; exact hlen)] at hmem
              have hnames : x ∉ allocatedNamesHOL context compiledShape :=
                not_mem_allocatedNamesHOL context compiledShape hx
              have hfreshNext :=
                hfresh_update context name compiledShape
                  (allocatedNamesHOL context compiledShape) x hfresh hnames
              have hxNext : x ≤ context.vmax + Shape.shapeSize compiledShape := by omega
              exact ih (sizeOf body) (by rw [← hn]; decreasing_trivial) body rfl
                { context with
                  vars := FUPDATE context.vars (name, (compiledShape, allocatedNamesHOL context compiledShape))
                  vmax := context.vmax + Shape.shapeSize compiledShape }
                x hfreshNext hxNext hmem.1
            · next hlen =>
              intro hmem
              simp [crepAssignedFreeVars] at hmem
      | assign kind name value =>
          cases kind with
          | «global» => simp [compileProgHOL, crepAssignedFreeVars]
          | «local» =>
              cases hlookup : FLOOKUP context.vars name with
              | none => simp [compileProgHOL, hlookup, crepAssignedFreeVars]
              | some pair =>
                  obtain ⟨variableShape, names⟩ := pair
                  cases hcomp : compileExpHOL context value with
                  | mk expressions expressionShape =>
                    simp only [compileProgHOL, hlookup, hcomp]
                    split
                    · next hlen =>
                        split
                        · next hdistinct =>
                            intro hmem
                            rw [crepAssignedFreeVars_nestedSeq_assign_zipWith _ _ hlen] at hmem
                            exact hfresh name variableShape names hlookup hmem
                        · next hnotdistinct =>
                            intro hmem
                            rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _
                              (by rw [freshNamesHOL_length]; exact hlen)] at hmem
                            rw [crepAssignedFreeVars_nestedSeq_assign_var_zipWith _ _
                              (by rw [freshNamesHOL_length])] at hmem
                            exact hfresh name variableShape names hlookup hmem.1
                    · next hlen =>
                        intro hmem
                        simp [crepAssignedFreeVars] at hmem
      | primitive name operator arguments =>
          cases hlookup : FLOOKUP context.vars name with
          | none => simp [compileProgHOL, hlookup, crepAssignedFreeVars]
          | some pair =>
              obtain ⟨variableShape, names⟩ := pair
              simp only [compileProgHOL, hlookup]
              intro hmem
              rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _
                (by rw [freshNamesHOL_length])] at hmem
              rw [mem_crepAssignedFreeVars_primitive] at hmem
              exact hfresh name variableShape names hlookup hmem.1
      | store address value =>
          cases hcompA : compileExpHOL context address with
          | mk addressExpressions addressShape =>
            cases hcompV : compileExpHOL context value with
            | mk valueExpressions valueShape =>
              cases addressExpressions with
              | nil => simp [compileProgHOL, hcompA, hcompV, crepAssignedFreeVars]
              | cons addressHead addressTail =>
                simp only [compileProgHOL, hcompA, hcompV]
                split
                · next hlen =>
                    intro hmem
                    rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _
                      (by simp [freshNamesHOL_length])] at hmem
                    rw [crepAssignedFreeVars_nestedSeq_stores] at hmem
                    simp at hmem
                · next hne =>
                    intro hmem
                    simp [crepAssignedFreeVars] at hmem
      | store32 address value =>
          cases hcompA : compileExpHOL context address with
          | mk addressExpressions addressShape =>
            cases hcompV : compileExpHOL context value with
            | mk valueExpressions valueShape =>
              cases addressExpressions with
              | nil => simp [compileProgHOL, hcompA, hcompV, crepAssignedFreeVars]
              | cons addressHead addressTail =>
                cases valueExpressions with
                | nil => simp [compileProgHOL, hcompA, hcompV, crepAssignedFreeVars]
                | cons valueHead valueTail =>
                  simp [compileProgHOL, hcompA, hcompV, crepAssignedFreeVars]
      | storeByte address value =>
          cases hcompA : compileExpHOL context address with
          | mk addressExpressions addressShape =>
            cases hcompV : compileExpHOL context value with
            | mk valueExpressions valueShape =>
              cases addressExpressions with
              | nil => simp [compileProgHOL, hcompA, hcompV, crepAssignedFreeVars]
              | cons addressHead addressTail =>
                cases valueExpressions with
                | nil => simp [compileProgHOL, hcompA, hcompV, crepAssignedFreeVars]
                | cons valueHead valueTail =>
                  simp [compileProgHOL, hcompA, hcompV, crepAssignedFreeVars]
      | seq first second =>
          intro hmem
          simp only [compileProgHOL] at hmem
          rw [mem_crepAssignedFreeVars_seq] at hmem
          rcases hmem with hmem | hmem
          · exact ih (sizeOf first) (by rw [← hn]; decreasing_trivial) first rfl
              context x hfresh hx hmem
          · exact ih (sizeOf second) (by rw [← hn]; decreasing_trivial) second rfl
              context x hfresh hx hmem
      | ite condition thenBranch elseBranch =>
          cases hcomp : compileExpHOL context condition with
          | mk expressions conditionShape =>
            simp only [compileProgHOL, hcomp]
            cases expressions with
            | nil => simp [crepAssignedFreeVars]
            | cons head tail =>
                intro hmem
                rw [mem_crepAssignedFreeVars_ite] at hmem
                rcases hmem with hmem | hmem
                · exact ih (sizeOf thenBranch) (by rw [← hn]; decreasing_trivial) thenBranch rfl
                    context x hfresh hx hmem
                · exact ih (sizeOf elseBranch) (by rw [← hn]; decreasing_trivial) elseBranch rfl
                    context x hfresh hx hmem
      | «while» condition body =>
          cases hcomp : compileExpHOL context condition with
          | mk expressions conditionShape =>
            simp only [compileProgHOL, hcomp]
            cases expressions with
            | nil => simp [crepAssignedFreeVars]
            | cons head tail =>
                intro hmem
                rw [mem_crepAssignedFreeVars_while] at hmem
                exact ih (sizeOf body) (by rw [← hn]; decreasing_trivial) body rfl
                  context x hfresh hx hmem
      | «break» => simp [compileProgHOL, crepAssignedFreeVars]
      | «continue» => simp [compileProgHOL, crepAssignedFreeVars]
      | decCall name shape function arguments body =>
          simp only [compileProgHOL]
          intro hmem
          rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _
            (by simp [allocatedNamesHOL_length])] at hmem
          rcases hmem with ⟨hmem, hnotNames⟩
          rw [mem_crepAssignedFreeVars_seq] at hmem
          rcases hmem with hmem | hmem
          · rw [mem_crepAssignedFreeVars_call_some_none] at hmem
            exact hnotNames hmem
          · have hnames : x ∉ allocatedNamesHOL context shape :=
              not_mem_allocatedNamesHOL context shape hx
            have hfreshNext :=
              hfresh_update context name shape (allocatedNamesHOL context shape) x hfresh hnames
            have hxNext : x ≤ context.vmax + Shape.shapeSize shape := by omega
            exact ih (sizeOf body) (by rw [← hn]; decreasing_trivial) body rfl
              { context with
                vars := FUPDATE context.vars (name, (shape, allocatedNamesHOL context shape))
                vmax := context.vmax + Shape.shapeSize shape }
              x hfreshNext hxNext hmem
      | extCall function configuration configurationLength array arrayLength =>
          cases h1 : compileExpHOL context configuration with
          | mk configurationExpressions configurationShape =>
            cases h2 : compileExpHOL context configurationLength with
            | mk configurationLengthExpressions configurationLengthShape =>
              cases h3 : compileExpHOL context array with
              | mk arrayExpressions arrayShape =>
                cases h4 : compileExpHOL context arrayLength with
                | mk arrayLengthExpressions arrayLengthShape =>
                  cases configurationExpressions with
                  | nil => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                  | cons configurationHead configurationTail =>
                    cases configurationShape with
                    | one =>
                      cases configurationLengthExpressions with
                      | nil => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                      | cons configurationLengthHead configurationLengthTail =>
                        cases configurationLengthShape with
                        | one =>
                          cases arrayExpressions with
                          | nil => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                          | cons arrayHead arrayTail =>
                            cases arrayShape with
                            | one =>
                              cases arrayLengthExpressions with
                              | nil => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                              | cons arrayLengthHead arrayLengthTail =>
                                cases arrayLengthShape with
                                | one =>
                                  simp only [compileProgHOL, h1, h2, h3, h4]
                                  intro hmem
                                  rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _
                                    (by simp)] at hmem
                                  simp [crepAssignedFreeVars] at hmem
                                | comb fields => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                                | named structName => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                            | comb fields => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                            | named structName => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                        | comb fields => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                        | named structName => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                    | comb fields => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
                    | named structName => simp [compileProgHOL, h1, h2, h3, h4, crepAssignedFreeVars]
      | raise exception value =>
          cases heid : FLOOKUP context.eids exception with
          | none => simp [compileProgHOL, heid, crepAssignedFreeVars]
          | some code =>
              cases hcomp : compileExpHOL context value with
              | mk expressions expressionShape =>
                simp only [compileProgHOL, heid, hcomp]
                split
                · next hlen =>
                    intro hmem
                    rw [mem_crepAssignedFreeVars_seq] at hmem
                    rcases hmem with hmem | hmem
                    · rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _
                        (by rw [freshNamesHOL_length])] at hmem
                      rw [crepAssignedFreeVars_nestedSeq_storeGlobals] at hmem
                      simp at hmem
                    · simp [crepAssignedFreeVars] at hmem
                · next hne =>
                    intro hmem
                    simp [crepAssignedFreeVars] at hmem
      | «return» value =>
          cases hcomp : compileExpHOL context value with
          | mk expressions expressionShape =>
            simp only [compileProgHOL, hcomp]
            split <;> (intro hmem; simp [crepAssignedFreeVars] at hmem)
      | shMemLoad size kind name address =>
          cases kind with
          | «global» => simp [compileProgHOL, crepAssignedFreeVars]
          | «local» =>
              cases hlookup : FLOOKUP context.vars name with
              | none => simp [compileProgHOL, hlookup, crepAssignedFreeVars]
              | some pair =>
                  obtain ⟨variableShape, slotList⟩ := pair
                  cases haddress : firstCompiledExpAnyShapeHOL context address with
                  | none => simp [compileProgHOL, hlookup, haddress, crepAssignedFreeVars]
                  | some addressExpression =>
                      simp only [compileProgHOL, hlookup, haddress]
                      cases slotList with
                      | nil => simp [crepAssignedFreeVars]
                      | cons destination tail =>
                          intro hmem
                          rw [mem_crepAssignedFreeVars_shMem] at hmem
                          exact hfresh name variableShape (destination :: tail) hlookup
                            (by rw [hmem]; exact List.mem_cons_self)
      | shMemStore size address value =>
          cases haddress : firstCompiledExpAnyShapeHOL context address with
          | none => simp [compileProgHOL, haddress, crepAssignedFreeVars]
          | some addressExpression =>
              cases hvalue : firstCompiledExpAnyShapeHOL context value with
              | none => simp [compileProgHOL, haddress, hvalue, crepAssignedFreeVars]
              | some valueExpression =>
                  simp only [compileProgHOL, haddress, hvalue]
                  intro hmem
                  rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _
                    (by simp)] at hmem
                  rw [mem_crepAssignedFreeVars_shMem] at hmem
                  exact hmem.2 (by rw [hmem.1]; exact List.mem_cons_self)
      | tick => simp [compileProgHOL, crepAssignedFreeVars]
      | annot tag text => simp [compileProgHOL, crepAssignedFreeVars]
      | call info function arguments =>
          cases info with
          | none =>
              intro hmem
              rw [compileProgHOL_call_none context function arguments] at hmem
              simp only [crepAssignedFreeVars] at hmem
              simp at hmem
          | some destinationHandler =>
              obtain ⟨destination, handler⟩ := destinationHandler
              cases handler with
              | none =>
                  cases destination with
                  | none =>
                      intro hmem
                      rw [compileProgHOL_call_destNone_handlerNone context function arguments] at hmem
                      rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _ (by simp)] at hmem
                      simp only [mem_crepAssignedFreeVars_call_some_none] at hmem
                      exact hmem.2 hmem.1
                  | some destinationPair =>
                      obtain ⟨kind, name⟩ := destinationPair
                      cases hcall : callDestinationNamesHOL context kind name with
                      | none =>
                          intro hmem
                          rw [compileProgHOL_call_destSome_nocall_handlerNone context function arguments kind name hcall] at hmem
                          simp only [crepAssignedFreeVars] at hmem
                          simp at hmem
                      | some names =>
                          intro hmem
                          rw [compileProgHOL_call_destSome_somecall_handlerNone context function arguments kind name names hcall] at hmem
                          simp only [mem_crepAssignedFreeVars_call_some_none] at hmem
                          obtain ⟨sh, ns, hlk, hslots⟩ :=
                            callDestinationNamesHOL_mem context kind name hcall
                          rw [hslots] at hmem
                          exact hfresh name sh ns hlk hmem
              | some handlerTriple =>
                  obtain ⟨exception, handlerVar, handlerProgram⟩ := handlerTriple
                  cases heid : FLOOKUP context.eids exception with
                  | none =>
                      cases destination with
                      | none =>
                          intro hmem
                          rw [compileProgHOL_call_destNone_handlerSome_eidsNone context function arguments exception handlerVar handlerProgram heid] at hmem
                          rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _ (by simp)] at hmem
                          simp only [mem_crepAssignedFreeVars_call_some_none] at hmem
                          exact hmem.2 hmem.1
                      | some destinationPair =>
                          obtain ⟨kind, name⟩ := destinationPair
                          cases hcall : callDestinationNamesHOL context kind name with
                          | none =>
                              intro hmem
                              rw [compileProgHOL_call_destSome_nocall_handlerSome_eidsNone context function arguments kind name hcall exception handlerVar handlerProgram heid] at hmem
                              simp only [crepAssignedFreeVars] at hmem
                              simp at hmem
                          | some names =>
                              intro hmem
                              rw [compileProgHOL_call_destSome_somecall_handlerSome_eidsNone context function arguments kind name names hcall exception handlerVar handlerProgram heid] at hmem
                              simp only [mem_crepAssignedFreeVars_call_some_none] at hmem
                              obtain ⟨sh, ns, hlk, hslots⟩ :=
                                callDestinationNamesHOL_mem context kind name hcall
                              rw [hslots] at hmem
                              exact hfresh name sh ns hlk hmem
                  | some code =>
                      have hprog : x ∉ crepAssignedFreeVars (compileProgHOL context handlerProgram) :=
                        ih (sizeOf handlerProgram) (by rw [← hn]; decreasing_trivial)
                          handlerProgram rfl context x hfresh hx
                      have hsetup : x ∉ crepAssignedFreeVars (expHdlFiniteMap (α := α) context.vars handlerVar) := by
                        cases hvh : FLOOKUP context.vars handlerVar with
                        | none => simp [expHdlFiniteMap, hvh, crepAssignedFreeVars]
                        | some pair =>
                            obtain ⟨handlerShape, handlerNames⟩ := pair
                            rw [expHdlFiniteMap_eq_assignRet (shape := handlerShape) hvh,
                              crepAssignedFreeVars_assignRet]
                            exact hfresh handlerVar handlerShape handlerNames hvh
                      have hseq : x ∉ crepAssignedFreeVars
                          (CrepProg.seq (expHdlFiniteMap (α := α) context.vars handlerVar)
                            (compileProgHOL context handlerProgram)) := by
                        rw [mem_crepAssignedFreeVars_seq]
                        rintro (h | h)
                        · exact hsetup h
                        · exact hprog h
                      cases destination with
                      | none =>
                          intro hmem
                          rw [compileProgHOL_call_destNone_handlerSome_eidsSome context function arguments exception handlerVar handlerProgram code heid] at hmem
                          rw [crepAssignedFreeVars_nestedDecs_mem_iff _ _ _ (by simp)] at hmem
                          simp only [mem_crepAssignedFreeVars_call_some_some] at hmem
                          rcases hmem.1 with hmem1 | hmem1
                          · exact hmem.2 hmem1
                          · exact hseq hmem1
                      | some destinationPair =>
                          obtain ⟨kind, name⟩ := destinationPair
                          cases hcall : callDestinationNamesHOL context kind name with
                          | none =>
                              intro hmem
                              rw [compileProgHOL_call_destSome_nocall_handlerSome_eidsSome context function arguments kind name hcall exception handlerVar handlerProgram code heid] at hmem
                              simp only [mem_crepAssignedFreeVars_call_some_some] at hmem
                              rcases hmem with h0 | hmem
                              · simp at h0
                              · exact hseq hmem
                          | some names =>
                              intro hmem
                              rw [compileProgHOL_call_destSome_somecall_handlerSome_eidsSome context function arguments kind name names hcall exception handlerVar handlerProgram code heid] at hmem
                              simp only [mem_crepAssignedFreeVars_call_some_some] at hmem
                              rcases hmem with hnames | hmem
                              · obtain ⟨sh, ns, hlk, hslots⟩ :=
                                  callDestinationNamesHOL_mem context kind name hcall
                                rw [hslots] at hnames
                                exact hfresh name sh ns hlk hnames
                              · exact hseq hmem
  intro program context x hfresh hx
  exact main (sizeOf program) program rfl context x hfresh hx

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake
    `not_mem_context_assigned_mem_gt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1252-1258`):
    `ctxt_max ctxt.vmax ctxt.vars ∧ (∀ v sh ns'. FLOOKUP ctxt.vars v =
    SOME (sh, ns') ⇒ ¬ MEM x ns') ∧ x ≤ ctxt.vmax ⇒ ¬ MEM x
    (assigned_free_vars (compile ctxt p))`. The statement shape is preserved
    (`ctxtMax` for `ctxt_max`, `FLOOKUP`, `≤`, `∉` for `¬ MEM`, `crepAssignedFreeVars`
    for `assigned_free_vars`, `compileProgHOL` for `compile`, same hypothesis and
    conclusion order). `ctxtMax` is retained only to match the HOL hypothesis,
    although the executable proof path derives the bound from the freshness
    hypothesis (`x ∉ ns` for the variable lookup), so the argument `_hmax` is
    unused.
    This declaration is deliberately untagged: the statement is keyed by the
    production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (and
    embeds a `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are
    `String`-keyed) with the production `Shape` (`Named : String`), while HOL
    keys names by `funname`/`varname`/`eid` = `mlstring` and uses `shape`
    (`Named : mlstring`). The `names_as_string` qualifier cannot authorize the
    embedded `Shape` carrier, and no same-module `NameRanged` byte witness
    applies because the conclusion is a membership `Prop` over a `Nat`, not a
    name. `docs/HOL-THEOREM-MAP.json` classifies this hol_name as
    `documented_mismatch`; the faithful exact-MlString carrier is tracked by
    `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`). Oracle evidence
    for the statement shape is the worked `example` in
    `Flapjack/Test/PanToCrepCodeRelParity.lean` (lines 393-405, `freshContext`,
    slot `5` absent from the compiled `dec`), together with
    `scripts/hol-probes/crep_assigned_free_vars_probe.out` (rows `skip`,
    `assign`, `dec_filter`, `seq`, `if_while`, `shmem_fallback`) pinning
    `assigned_free_vars`; there is no dedicated probe for this combined theorem.
    The executable workhorse is `compileProgHOL_not_mem_assignedFreeVars`
    above. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): String-keyed identifiers + production
-- `Shape` vs HOL `mlstring`/`shape`; exact MlString carrier tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem notMemContextAssignedMemGt
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (program : Prog α) (x : Nat)
    (_hmax : ctxtMax context.vmax context.vars)
    (hfresh : ∀ v sh ns', FLOOKUP context.vars v = some (sh, ns') → x ∉ ns')
    (hx : x ≤ context.vmax) :
    x ∉ crepAssignedFreeVars (compileProgHOL context program) :=
  compileProgHOL_not_mem_assignedFreeVars program context x hfresh hx

/-- `distinctLists` as a set-disjointness predicate: every element of the left
    list is absent from the right list. -/
theorem distinctLists_eq_true_iff {left right : List Nat} :
    distinctLists left right = true ↔ ∀ x ∈ left, x ∉ right := by
  simp [distinctLists, List.all_eq_true, List.contains_eq_mem, decide_eq_false_iff_not]

/-- Source-shaped but FLAPJACK-SPECIFIC statement (NOT an exact HOL port), mirroring
    Cake `rewritten_context_unassigned`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1457-1468`):

    HOL: `!p nctxt v ctxt ns nvars sh sh'.`
      `nctxt = ctxt with <| vars := ctxt.vars |+ (v,sh,nvars);`
      `vmax := ctxt.vmax + size_of_shape sh |> /\`
      `FLOOKUP ctxt.vars v = SOME (sh',ns) /\ no_overlap ctxt.vars /\`
      `ctxt_max ctxt.vmax ctxt.vars /\ no_overlap nctxt.vars /\`
      `ctxt_max nctxt.vmax nctxt.vars /\ distinct_lists nvars ns ==>`
      `distinct_lists ns (assigned_free_vars (compile nctxt p))`.

    The Lean statement keeps the same hypothesis set and conclusion shape:
    the context-extension equation `h_nctxt` (via `FUPDATE` and
    `Shape.shapeSize`), the lookup `h_lookup`, `noOverlap`/`ctxtMax` for both
    the original and rewritten context, `distinctLists nvars ns = true`, and the
    conclusion `distinctLists ns (crepAssignedFreeVars (compileProgHOL nctxt program)) = true`.

    Carrier mismatch (why the tag stays withdrawn): the statement is keyed by
    the production identifiers `FunName`/`VarName`/`ExceptionId` = `String`
    (embedded in a `PanToCrepHOLContext` whose `FiniteMap`s are `String`-keyed),
    by the production `Shape` (`named : String`), and by the production
    `Prog α`/`compileProgHOL`, whereas HOL `pan_to_crepProofScript.sml` keys by
    `funname`/`varname`/`eid` = `mlstring`, uses HOL `shape`, and compiles the
    word-indexed `'a prog` with `compile`. The executable-only typeclass
    arguments `[BEq α] [OfNat α 0] [OfNat α 1] [Add α] [CrepBytesInWord α]`
    also have no HOL counterpart. `names_as_string` cannot authorize the
    embedded `Shape`/program carriers, and no `NameRanged` byte witness applies
    (the conclusion is a `distinctLists` membership predicate over `Nat`, not a
    name). The statement is recorded as `documented_mismatch` in
    `docs/HOL-THEOREM-MAP.json` (intentionally untagged), and the exact MlString
    carrier is tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).

    Oracle evidence: the `rewritten_context_unassigned` statement is exercised
    by the kernel-checked `example` in `Flapjack/Test/PanToCrepCodeRelParity.lean`
    (lines 413-429), and the supporting `no_overlap`/`distinct_lists` predicates
    are pinned by `scripts/hol-probes/pan_common_props_no_overlap_probe.out`
    (rows `slot_nodup_x`, `slot_nodup_y`, `slots_disjoint`, `distinct_lists_self`,
    `nested_zip_lookup`); there is no dedicated probe for this combined theorem. -/
theorem rewrittenContextUnassigned [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (program : Prog α) (nctxt ctxt : PanToCrepHOLContext α) (v : VarName)
    (ns nvars : List Nat) (sh sh' : Shape)
    (hnctxt : nctxt =
      { ctxt with
        vars := FUPDATE ctxt.vars (v, (sh, nvars))
        vmax := ctxt.vmax + Shape.shapeSize sh })
    (hlookup : FLOOKUP ctxt.vars v = some (sh', ns))
    (hnoOverlap : noOverlap ctxt.vars) (hctxtMax : ctxtMax ctxt.vmax ctxt.vars)
    (_hnoOverlapN : noOverlap nctxt.vars)
    (hctxtMaxN : ctxtMax nctxt.vmax nctxt.vars)
    (hdistinct : distinctLists nvars ns = true) :
    distinctLists ns (crepAssignedFreeVars (compileProgHOL nctxt program)) = true := by
  rw [distinctLists_eq_true_iff] at hdistinct ⊢
  intro x hxns hxafv
  subst hnctxt
  have hxle : x ≤ ctxt.vmax + Shape.shapeSize sh := by
    have hle := hctxtMax.2 v sh' ns hlookup x hxns
    omega
  have hfreshN :
      ∀ v' sh'' ns'', FLOOKUP (FUPDATE ctxt.vars (v, (sh, nvars))) v' =
        some (sh'', ns'') → x ∉ ns'' := by
    intro v' sh'' ns'' hlk
    rw [FLOOKUP_update] at hlk
    by_cases hv : (v == v') = true
    · rw [if_pos hv] at hlk
      have hpair : (sh, nvars) = (sh'', ns'') := Option.some.inj hlk
      have hn : nvars = ns'' := congrArg Prod.snd hpair
      intro hxns''
      exact (hdistinct x (by rw [hn]; exact hxns'')) hxns
    · rw [if_neg hv] at hlk
      intro hxns''
      have hveq : v = v' :=
        hnoOverlap.2 v v' sh' sh'' ns ns'' hlookup hlk ⟨x, hxns, hxns''⟩
      rw [beq_iff_eq] at hv
      exact hv hveq
  exact notMemContextAssignedMemGt
    { ctxt with
      vars := FUPDATE ctxt.vars (v, (sh, nvars))
      vmax := ctxt.vmax + Shape.shapeSize sh }
    program x hctxtMaxN hfreshN hxle hxafv

/-- Flapjack-specific analogue of HOL `pan_to_crepProofScript.sml:3051`
`evaluate_replicate_const`.  NOT a port: the production Crep evaluator
`evalCrepRuntimeExp`/`evalCrepRuntimeExps` returns the bare `α` carried by a
`word_lab` cell, and this statement is proved over the separate word_lab core
`evalCrepRuntimeExpsWordLab`, whose recursive children still call the bare
`evalCrepRuntimeExp` and whose arithmetic/`crepOp` cases delegate to the
arbitrary runtime `memoryModel` hooks rather than HOL's fixed `crepSem$eval`.
So it is not yet kernel-checked equal to `crepSem$eval` and must not carry a
`@[hol]` tag.  Establishing a faithful production evaluator/projection and
revisiting the tag is tracked by bead `flapjack-pxn.18.4.3.48.1`. -/
theorem evaluateReplicateConst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (count : Nat) (state : CrepRuntimeState α σ) :
    evalCrepRuntimeExpsWordLab state (List.replicate count (.const (0 : α))) =
      some (List.replicate count (.word (0 : α))) := by
  induction count with
  | zero => simp [evalCrepRuntimeExpsWordLab]
  | succ count ih =>
      simp [List.replicate_succ, evalCrepRuntimeExpsWordLab, evalCrepRuntimeExpWordLab, ih]

/-! ## Exact HOL `pan_to_crep` `is_wf_shape_nil_length_flatten`

The match above is the source-shaped port over the production `PanValue`/`String`
carrier. The declaration below is the exact port of the same HOL theorem over
the HOL-shaped `ValueHOL`/`StructContextExact` carriers. -/
open Flapjack.Pancake.PanLang

/-- Exact port of HOL Cake `pan_to_crepProof$is_wf_shape_nil_length_flatten`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2469`). Over the
    HOL-shaped `ValueHOL`/`StructContextExact` carriers, a word list selected
    by the zero-size or positive-size branch has the size prescribed by the
    source value shape. Reuses the exact `flattenHOL_length_eq_sizeOfShapeHOL`
    (HOL `panPropsScript.sml:171`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "is_wf_shape_nil_length_flatten"]
theorem isWfShapeExactHOL_length_flatten {width : Nat} [NeZero width]
    (value : ValueHOL width) (words : List (HolWordLab width))
    (hwf : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true)
    (hzero : sizeOfShapeHOL (shapeOfHOLExact value) = 0 → words = [])
    (hpositive : 0 < sizeOfShapeHOL (shapeOfHOLExact value) →
      words = flattenHOL value) :
    words.length = sizeOfShapeHOL (shapeOfHOLExact value) := by
  by_cases hz : sizeOfShapeHOL (shapeOfHOLExact value) = 0
  · simp [hzero hz, hz]
  · have hpos : 0 < sizeOfShapeHOL (shapeOfHOLExact value) := Nat.pos_of_ne_zero hz
    rw [hpositive hpos]
    exact flattenHOL_length_eq_sizeOfShapeHOL value hwf

/-- Exact port of HOL `decs_stcnames_lemma` (`pan_to_crepProofScript.sml:4963-4969`):
a declaration list containing only function or exception declarations leaves the
structure context unchanged. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "decs_stcnames_lemma"]
theorem decsStcnamesHOLExact_of_functions_or_exnDecls {width : Nat} [NeZero width]
    (context : StructContextExact) (code : List (DeclHOL width))
    (h : code.all (fun declaration =>
      isFunctionHOL declaration || isExnDeclHOL declaration) = true) :
    decsStcnamesHOLExact (width := width) context code = some context := by
  induction code generalizing context with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;>
        simp_all [decsStcnamesHOLExact, isFunctionHOL, isExnDeclHOL]

end Flapjack
