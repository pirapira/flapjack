import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.ValueHOL
import Flapjack.Pancake.Semantics.PanSem.IsValidValueExact
import Flapjack.Pancake.PanLang.Decl

/-!
Source-state conversion and evaluator support for porting HOL
`pan_structsProofScript.sml` `compile_correct`. The full theorem's premises
and invariant postconditions are not yet proved here.
-/

namespace Flapjack

/-- Private lookup bridge from the production string lookup to the
    HOL-style association-list lookup. -/
private theorem lookupInfoStringDefault_eq_panPropsALookupEq
    {β : Type} (key : String) (entries : List (String × β)) :
    @lookupInfo String β instBEqOfDecidableEq key entries =
      panPropsALookupEq key entries := by
  letI : LawfulBEq String := instLawfulBEqString
  exact lookupInfo_eq_panPropsALookupEq key entries

mutual
  /-- Source-shaped executable counterpart (Flapjack-specific; NOT an exact HOL port) of HOL `convert_v_def`. The HOL datatype
      cases are `Val (Word w)`, `RStruct xs`, and `NStruct nm flds`; these
      correspond respectively to `.word`, `.rStruct`, and `.nStruct` in
      `PanValue`. The first case is unchanged, the second maps recursively in
      order, and the third drops both record and field names while recursively
      mapping field values in order. The direct HOL-EVAL regression is recorded
      in the adjacent probe fixture. -/
  -- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is over the
  -- production PanValue α carrier, whose word payload is the generic α and whose
  -- nStruct record/field names are StructName/FieldName = String, while HOL
  -- pan_structsProofScript.sml is over panSem$v with a word-labelled payload and
  -- stcname/fldname = mlstring. The exact HOL definition is `convertV` over the
  -- exact `ValueHOL` carrier (tagged with this HOL name above); the kernel-checked
  -- production bridge is `convertV_toPanValue`. This executable counterpart stays
  -- untagged until the executable path itself runs over the exact carriers,
  -- tracked by flapjack-pxn.18.3.5.8 (parent flapjack-pxn.18.3.5.7.2).
  def panStructConvertValue : PanValue α → PanValue α
    | .word value => .word value
    | .rStruct fields => .rStruct (panStructConvertValues fields)
    | .nStruct _ fields => .rStruct (panStructConvertFieldValues fields)
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructConvertValues : List (PanValue α) → List (PanValue α)
    | [] => []
    | value :: values => panStructConvertValue value :: panStructConvertValues values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructConvertFieldValues : List (FieldName × PanValue α) → List (PanValue α)
    | [] => []
    | (_, value) :: fields =>
        panStructConvertValue value :: panStructConvertFieldValues fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Exact port of HOL `convert_v_def`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:31-37`):
    `convert_v (Val x) = Val x`,
    `convert_v (RStruct xs) = RStruct (MAP convert_v xs)`, and
    `convert_v (NStruct nm flds) = RStruct (MAP (\(nm,v). convert_v v) flds)`,
    over the exact `panSem$v` carrier `ValueHOL` (MlString names and an indexed
    word payload). The `NStruct` branch drops the record and field names, so the
    exact `mlstring` name carrier is carried but never inspected. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_v_def"]
def convertV {width : Nat} [NeZero width] : ValueHOL width → ValueHOL width
  | .val value => .val value
  | .rStruct fields => .rStruct (fields.map convertV)
  | .nStruct _ fields => .rStruct (fields.map (fun pair => convertV pair.2))
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
    | (rename_i hmem
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)
    | (rename_i hmem
       have hsnd : sizeOf pair.snd < sizeOf pair := by cases pair; simp +arith
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)

/-! Structural Bool equality for the translated Shape datatype. It performs
    the HOL constructor equality cases recursively and avoids a BEq instance
    for Shape or String. -/
mutual
  def panStructShapeEqBool : Shape → Shape → Bool
    | .one, .one => true
    | .comb left, .comb right => panStructShapeListEqBool left right
    | .named left, .named right => decide (left = right)
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructShapeListEqBool : List Shape → List Shape → Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        panStructShapeEqBool left right && panStructShapeListEqBool lefts rights
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Source-shaped executable port (Flapjack-specific; NOT an exact HOL port) of HOL `pan_structsProof$v_flds_ok`
      (`cakeml/pancake/proofs/pan_structsProofScript.sml:39`). The HOL clauses
      are reproduced literally: a scalar is `T`; `RStruct vs` is
      `EVERY (v_flds_ok ctxt) vs`; `NStruct nm flds` is the conjunction of the
      per-field predicate `EVERY (\(nm,v). v_flds_ok ctxt v) flds` with the
      `ALOOKUP ctxt nm` case, where `NONE` gives `F` and `SOME info` requires
      both `MAP FST flds = MAP FST info.fields` and
      `MAP (shape_of o SND) flds = MAP SND info.fields`.

      `lookupInfo` is the first-match association-list lookup, i.e. the exact
      `alist$ALOOKUP` counterpart, and under `[LawfulBEq String]` its `==`
      reflects HOL's `=`. The context is the HOL-shaped `StructContextHOL`
      (fields and size only). `panSemShapeOf` is the source-shaped (currently untagged) counterpart of HOL
      `shape_of` (`panSemScript.sml:80`), and `panStructShapeListEqBool`
      computes HOL's `=` on `shape` lists constructor-by-constructor, since
      Lean `Shape` intentionally has no `BEq`/`DecidableEq` instance. The
      direct original-HOL rows are pinned in
      `scripts/hol-probes/pan_structs_value_validity_probe.out`. -/
  -- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is over the
  -- production PanValue carrier whose nStruct record/field names are
  -- StructName/FieldName = String and over StructContextHOL (String-keyed), while
  -- HOL pan_structsProofScript.sml is over panSem$v with stcname/fldname = mlstring.
  -- The exact MlString identifier carrier is tracked by flapjack-pxn.18.3.5.8
  -- (parent flapjack-pxn.18.3.5.7.2).
  def panValueFldsOk [LawfulBEq String] (context : StructContextHOL) :
      PanValue α → Bool
    | .word _ => true
    | .rStruct values => panValuesFldsOk context values
    | .nStruct name fields =>
        panFieldsFldsOk context fields &&
          match lookupInfo name context with
          | none => false
          | some info =>
              (fields.map Prod.fst == info.fields.map Prod.fst) &&
                panStructShapeListEqBool
                  (fields.map (panSemShapeOf ∘ Prod.snd))
                  (info.fields.map Prod.snd)
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panValuesFldsOk [LawfulBEq String] (context : StructContextHOL) :
      List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panValueFldsOk context value && panValuesFldsOk context values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panFieldsFldsOk [LawfulBEq String] (context : StructContextHOL) :
      List (FieldName × PanValue α) → Bool
    | [] => true
    | (_, value) :: fields =>
        panValueFldsOk context value && panFieldsFldsOk context fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

private theorem lookupInfo_mem_of_some [BEq κ] [LawfulBEq κ]
    (key : κ) (entries : List (κ × β)) (value : β)
    (hlookup : lookupInfo key entries = some value) :
    key ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [lookupInfo] at hlookup
  | cons entry entries ih =>
      obtain ⟨candidate, candidateValue⟩ := entry
      by_cases hmatch : candidate == key
      · have heq : candidate = key := LawfulBEq.eq_of_beq hmatch
        simp [heq]
      · simp only [lookupInfo, hmatch] at hlookup
        have htail := ih hlookup
        simp [htail]

private theorem lookupInfo_append_eq_of_some [LawfulBEq String]
    (pfx context : StructContextHOL) (key : String) (value : StructInfoHOL)
    (hdisjoint : (pfx.map Prod.fst ++ context.map Prod.fst).Nodup)
    (hlookup : lookupInfo key context = some value) :
    lookupInfo key (pfx ++ context) = some value := by
  induction pfx with
  | nil => exact hlookup
  | cons entry pfx ih =>
      obtain ⟨candidate, info⟩ := entry
      rcases List.nodup_cons.mp hdisjoint with ⟨hnot, htailNodup⟩
      have hkeyMem := lookupInfo_mem_of_some key context value hlookup
      have hcandidateNe : candidate ≠ key := by
        intro heq
        subst candidate
        exact hnot (List.mem_append_right _ hkeyMem)
      have hmatch : (candidate == key) = false := by
        cases hbeq : candidate == key with
        | false => rfl
        | true => exact False.elim (hcandidateNe (LawfulBEq.eq_of_beq hbeq))
      simp only [List.map_cons] at hdisjoint
      have hresult := ih htailNodup
      simpa [lookupInfo, hmatch] using hresult

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL `v_flds_ok_append` (`pan_structsProofScript.sml:522`): extending
    the HOL-shaped structure context preserves Bool field validity when the
    prefix keys are distinct from the original context keys. This is the
    invariant-preservation prerequisite used by `compile_correct`. The direct
    original-HOL EVAL row and a named-value Lean regression with nonempty
    prefix are recorded in `pan_structs_value_validity_probe.out`. -/
  -- FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag). The three
  -- constructor equations match HOL `convert_v_def`
  -- (cakeml/pancake/proofs/pan_structsProofScript.sml:31-37), but the carrier
  -- differs: HOL is over `panSem$v` (`panSemScript.sml:22`) with
  -- `stcname`/`fldname` = `mlstring` and `Val ('a word_lab)`, while this is over
  -- production `PanValue α`, whose `nStruct` names are
  -- `StructName`/`FieldName = String` and whose first constructor stores `α`
  -- directly rather than a `word_lab` wrapper. That constructor field-type
  -- difference is beyond name representation, so `(names_as_string := ...)` does
  -- not apply. The exact `HolValue`/`HolWordLab` carriers now exist
  -- (`PanSem.lean`, bead `flapjack-pxn.18.3.6.8`), but no HOL-shaped `convert_v`
  -- over `HolValue` with a production bridge is defined yet; tracked by
  -- `flapjack-pxn.18.3.5.8.19` (parent `flapjack-pxn.18.3.5.8`). Direct HOL
  -- oracle row `convert_named_record=RStruct [ValWord 3w; ValWord 5w]` in
  -- `scripts/hol-probes/pan_structs_compile_correct_probe.out:1`; paired Lean
  -- regression `Flapjack.Test.PanStructsCompileCorrect` (:13-17).
theorem panValueFldsOk_append [LawfulBEq String]
    (pfx context : StructContextHOL) (value : PanValue α)
    (hvalue : panValueFldsOk context value = true)
    (hkeys : (pfx.map Prod.fst ++ context.map Prod.fst).Nodup) :
    panValueFldsOk (pfx ++ context) value = true := by
  revert hvalue hkeys pfx
  apply panValueFldsOk.induct (α := α)
    (motive1 := fun value =>
      ∀ pfx, panValueFldsOk context value = true →
        (pfx.map Prod.fst ++ context.map Prod.fst).Nodup →
          panValueFldsOk (pfx ++ context) value = true)
    (motive2 := fun fields =>
      ∀ pfx, panFieldsFldsOk context fields = true →
        (pfx.map Prod.fst ++ context.map Prod.fst).Nodup →
          panFieldsFldsOk (pfx ++ context) fields = true)
    (motive3 := fun values =>
      ∀ pfx, panValuesFldsOk context values = true →
        (pfx.map Prod.fst ++ context.map Prod.fst).Nodup →
          panValuesFldsOk (pfx ++ context) values = true)
  · intro word pfx hvalue hkeys
    simp [panValueFldsOk]
  · intro values ih pfx hvalue hkeys
    simpa [panValueFldsOk] using ih pfx
      (by simpa [panValueFldsOk] using hvalue) hkeys
  · intro name fields ih pfx hvalue hkeys
    simp only [panValueFldsOk, Bool.and_eq_true] at hvalue ⊢
    cases hlookup : lookupInfo name context with
    | none => simp [hlookup] at hvalue
    | some info =>
        simp only [hlookup, Bool.and_eq_true] at hvalue
        obtain ⟨hfields, hnames, hshapes⟩ := hvalue
        have hlookupExtended := lookupInfo_append_eq_of_some
          pfx context name info hkeys hlookup
        simp only [hlookupExtended, Bool.and_eq_true]
        exact ⟨ih pfx hfields hkeys, hnames, hshapes⟩
  · intro pfx hvalue hkeys
    simp [panFieldsFldsOk]
  · intro name value fields ihValue ihFields pfx hvalue hkeys
    simp only [panFieldsFldsOk, Bool.and_eq_true] at hvalue ⊢
    exact ⟨ihValue pfx hvalue.1 hkeys, ihFields pfx hvalue.2 hkeys⟩
  · intro pfx hvalue hkeys
    simp [panValuesFldsOk]
  · intro value values ihValue ihValues pfx hvalue hkeys
    simp only [panValuesFldsOk, Bool.and_eq_true] at hvalue ⊢
    exact ⟨ihValue pfx hvalue.1 hkeys, ihValues pfx hvalue.2 hkeys⟩

/-! ## Exact HOL `v_flds_ok` carrier and append theorem

The preceding source-shaped Bool predicate remains useful to production
PanValue code, but it cannot state the HOL theorem: HOL `v` carries mlstring
names and `word_lab` words. The declarations in this section use `ValueHOL`,
`ShapeHOL`, and `StructContextExact` directly. -/

open Flapjack.Pancake.PanLang (MlS ShapeHOL StructInfoHOLExact StructContextExact)

mutual
  /-- Exact Bool rendering of HOL `v_flds_ok_def` over the faithful HOL value,
      shape, and struct-context carriers. Field-name and shape-list equality
      implement HOL datatype equality. -/
  @[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "v_flds_ok_def"]
  def valueFldsOkHOLExact {width : Nat} [NeZero width]
      (context : StructContextExact) : ValueHOL width → Bool
    | .val _ => true
    | .rStruct values => valuesFldsOkHOLExact context values
    | .nStruct name fields =>
        fieldsFldsOkHOLExact context fields &&
          match Flapjack.Pancake.PanLang.structContextLookupHOL name context with
          | none => false
          | some info =>
              (fields.map Prod.fst == info.fields.map Prod.fst) &&
                shapeEqHOL.shapeEqListHOL
                  (fields.map (fun field => shapeOfHOLExact field.2))
                  (info.fields.map Prod.snd)
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def valuesFldsOkHOLExact {width : Nat} [NeZero width]
      (context : StructContextExact) : List (ValueHOL width) → Bool
    | [] => true
    | value :: values =>
        valueFldsOkHOLExact context value && valuesFldsOkHOLExact context values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def fieldsFldsOkHOLExact {width : Nat} [NeZero width]
      (context : StructContextExact) : List (MlS × ValueHOL width) → Bool
    | [] => true
    | (_, value) :: fields =>
        valueFldsOkHOLExact context value && fieldsFldsOkHOLExact context fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

private theorem structContextLookupHOL_mem_of_some
    (name : MlS) (entries : StructContextExact) (info : StructInfoHOLExact)
    (hlookup : Flapjack.Pancake.PanLang.structContextLookupHOL name entries = some info) :
    name ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [Flapjack.Pancake.PanLang.structContextLookupHOL] at hlookup
  | cons entry entries ih =>
      obtain ⟨candidate, candidateInfo⟩ := entry
      by_cases hmatch : name = candidate
      · subst name
        simp
      · simp only [Flapjack.Pancake.PanLang.structContextLookupHOL, if_neg hmatch] at hlookup
        have htail := ih hlookup
        simp [hmatch, htail]

private theorem structContextLookupHOL_append_eq_of_some
    (pfx context : StructContextExact) (name : MlS) (info : StructInfoHOLExact)
    (hdisjoint : (pfx.map Prod.fst ++ context.map Prod.fst).Nodup)
    (hlookup : Flapjack.Pancake.PanLang.structContextLookupHOL name context = some info) :
    Flapjack.Pancake.PanLang.structContextLookupHOL name (pfx ++ context) = some info := by
  induction pfx with
  | nil => exact hlookup
  | cons entry pfx ih =>
      obtain ⟨candidate, candidateInfo⟩ := entry
      rcases List.nodup_cons.mp hdisjoint with ⟨hnot, htailNodup⟩
      have hnameMem := structContextLookupHOL_mem_of_some name context info hlookup
      have hne : name ≠ candidate := by
        intro heq
        subst name
        exact hnot (List.mem_append_right _ hnameMem)
      have hlookupTail := ih htailNodup
      simp [hne, hlookupTail]

/-- For a distinct-name context, a successful lookup after a prefix drop is
    unchanged by the drop. -/
private theorem structContextLookupHOL_drop_eq_of_some
    (n : Nat) (context : StructContextExact) (name : MlS) (info : StructInfoHOLExact)
    (hlookup : Flapjack.Pancake.PanLang.structContextLookupHOL name (context.drop n) = some info)
    (hnodup : (context.map Prod.fst).Nodup) :
    Flapjack.Pancake.PanLang.structContextLookupHOL name context = some info := by
  induction n generalizing context with
  | zero => simpa using hlookup
  | succ n ih =>
      cases context with
      | nil => simp at hlookup
      | cons entry rest =>
          obtain ⟨candidate, candidateInfo⟩ := entry
          have hnames : (candidate :: rest.map Prod.fst).Nodup := by
            simpa using hnodup
          obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hnames
          have htail : Flapjack.Pancake.PanLang.structContextLookupHOL name
              (rest.drop n) = some info := by
            simpa using hlookup
          have hmemTail := structContextLookupHOL_mem_of_some name (rest.drop n) info htail
          have hmemRest : name ∈ rest.map Prod.fst := by
            rw [List.map_drop] at hmemTail
            exact List.mem_of_mem_drop hmemTail
          have hne : name ≠ candidate := by
            intro heq
            apply hnot
            rw [← heq]
            exact hmemRest
          have hctx := ih rest htail hrest
          simpa [Flapjack.Pancake.PanLang.structContextLookupHOL, hne] using hctx

/-- Exact port of HOL `size_of_sh_with_ctxt_drop`
    (`pan_structsProofScript.sml:99`). This keeps HOL's well-formedness and
    distinct-name premises over `ShapeHOL` and `StructContextExact`. The
    production String-carrier analogue remains untagged in `PanStructs.lean`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "size_of_sh_with_ctxt_drop"]
theorem sizeOfShapeWithContextHOL_drop (context : StructContextExact)
    (shape : ShapeHOL) (n : Nat)
    (hwf : Flapjack.Pancake.PanLang.isWfShapeExactHOL (context.drop n) shape = true)
    (hnodup : (context.map Prod.fst).Nodup) :
    Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL (context.drop n) shape =
      Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context shape := by
  let contextDrop := context.drop n
  have hrec := Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL.induct
    (context := contextDrop)
    (motive_1 := fun sh =>
      Flapjack.Pancake.PanLang.isWfShapeExactHOL contextDrop sh = true →
        Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL contextDrop sh =
          Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context sh)
    (motive_2 := fun shapes =>
      Flapjack.Pancake.PanLang.isWfShapesExactHOL contextDrop shapes = true →
        Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL contextDrop shapes =
          Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL context shapes)
    (case1 := by
      intro _
      rfl)
    (case2 := by
      intro shapes ih hwfShapes
      simpa [Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL_comb] using ih hwfShapes)
    (case3 := by
      intro name info hlookup _
      have hctx := structContextLookupHOL_drop_eq_of_some n context name info hlookup hnodup
      simp [Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL, hlookup, hctx])
    (case4 := by
      intro name hlookup hwfName
      simp [Flapjack.Pancake.PanLang.isWfShapeExactHOL, hlookup] at hwfName)
    (case5 := by
      intro _
      rfl)
    (case6 := by
      intro child rest ihChild ihRest hwfRest
      simp only [Flapjack.Pancake.PanLang.isWfShapesExactHOL, Bool.and_eq_true] at hwfRest
      obtain ⟨hwfChild, hwfTail⟩ := hwfRest
      simp only [Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL]
      rw [ihChild hwfChild, ihRest hwfTail])
    shape
  exact hrec hwf

/-- Exact port of HOL `v_flds_ok_append` (`pan_structsProofScript.sml:522`).
    Its value, context keys, field keys, and shape keys are the faithful HOL
    carriers: `ValueHOL`, `MlString`, `ShapeHOL`, and `StructContextExact`.
    The premises and conclusion match HOL: validity in `ctxt`, distinct keys
    across `pfx ++ ctxt`, then validity in the appended context. The direct
    HOL EVAL fixture is `v_flds_ok_append_nonempty_prefix_named` in
    `pan_structs_value_validity_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "v_flds_ok_append"]
theorem valueFldsOkHOLExact_append {width : Nat} [NeZero width]
    (ctxt pfx : StructContextExact) (value : ValueHOL width)
    (hvalue : valueFldsOkHOLExact ctxt value = true)
    (hkeys : (pfx.map Prod.fst ++ ctxt.map Prod.fst).Nodup) :
    valueFldsOkHOLExact (pfx ++ ctxt) value = true := by
  revert hvalue hkeys pfx
  apply valueFldsOkHOLExact.induct
    (motive1 := fun value =>
      ∀ pfx, valueFldsOkHOLExact ctxt value = true →
        (pfx.map Prod.fst ++ ctxt.map Prod.fst).Nodup →
          valueFldsOkHOLExact (pfx ++ ctxt) value = true)
    (motive2 := fun fields =>
      ∀ pfx, fieldsFldsOkHOLExact ctxt fields = true →
        (pfx.map Prod.fst ++ ctxt.map Prod.fst).Nodup →
          fieldsFldsOkHOLExact (pfx ++ ctxt) fields = true)
    (motive3 := fun values =>
      ∀ pfx, valuesFldsOkHOLExact ctxt values = true →
        (pfx.map Prod.fst ++ ctxt.map Prod.fst).Nodup →
          valuesFldsOkHOLExact (pfx ++ ctxt) values = true)
  · intro word pfx hvalue hkeys
    simp [valueFldsOkHOLExact]
  · intro values ih pfx hvalue hkeys
    simpa [valueFldsOkHOLExact] using ih pfx
      (by simpa [valueFldsOkHOLExact] using hvalue) hkeys
  · intro name fields ih pfx hvalue hkeys
    simp only [valueFldsOkHOLExact, Bool.and_eq_true] at hvalue ⊢
    cases hlookup : Flapjack.Pancake.PanLang.structContextLookupHOL name ctxt with
    | none => simp [hlookup] at hvalue
    | some info =>
        simp only [hlookup, Bool.and_eq_true] at hvalue
        obtain ⟨hfields, hnames, hshapes⟩ := hvalue
        have hlookupExtended := structContextLookupHOL_append_eq_of_some
          pfx ctxt name info hkeys hlookup
        simp only [hlookupExtended, Bool.and_eq_true]
        exact ⟨ih pfx hfields hkeys, hnames, hshapes⟩
  · intro pfx hvalue hkeys
    simp [fieldsFldsOkHOLExact]
  · intro name value fields ihValue ihFields pfx hvalue hkeys
    simp only [fieldsFldsOkHOLExact, Bool.and_eq_true] at hvalue ⊢
    exact ⟨ihValue pfx hvalue.1 hkeys, ihFields pfx hvalue.2 hkeys⟩
  · intro pfx hvalue hkeys
    simp [valuesFldsOkHOLExact]
  · intro value values ihValue ihValues pfx hvalue hkeys
    simp only [valuesFldsOkHOLExact, Bool.and_eq_true] at hvalue ⊢
    exact ⟨ihValue pfx hvalue.1 hkeys, ihValues pfx hvalue.2 hkeys⟩

mutual
  /-- Bool-valued comparison for HOL `v_flds_ok_def`, using production
      `lookupInfo`. This is not currently tagged as an exact port: the HOL
      predicate uses HOL equality in `ALOOKUP`, while this declaration calls
      `lookupInfo` at the canonical String equality instance. An exact
      clause-by-clause comparison of the recursive shape and field checks
      against HOL is still required before claiming the tag. Lean `StructInfo`
      also has an additional `shapedFields` cache absent from HOL.
      This Bool declaration is distinct from the Prop-valued convenience
      predicate below. -/
  def panStructValueFieldsOkBool (structs : StructContext) :
      PanValue α → Bool
    | .word _ => true
    | .rStruct values => panStructValuesFieldsOkBool structs values
    | .nStruct name fields =>
        panStructFieldValuesFieldsOkBool structs fields &&
          match lookupInfo name structs with
          | none => false
          | some info => panValueFieldsHaveShapes structs info.fields fields
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructValuesFieldsOkBool (structs : StructContext) :
      List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panStructValueFieldsOkBool structs value &&
          panStructValuesFieldsOkBool structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructFieldValuesFieldsOkBool (structs : StructContext) :
      List (FieldName × PanValue α) → Bool
    | [] => true
    | (_, value) :: fields =>
        panStructValueFieldsOkBool structs value &&
          panStructFieldValuesFieldsOkBool structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end


mutual
  /-- Prop-valued Flapjack convenience predicate mirroring the equations of
      HOL `v_flds_ok_def`. It is not an exact port: HOL returns Bool, while
      this declaration returns Prop and uses `[BEq String]` lookup. -/
  def panStructValueFieldsOk [BEq String] (structs : StructContext) :
      PanValue α → Prop
    | .word _ => True
    | .rStruct values => panStructValuesFieldsOk structs values
    | .nStruct name fields =>
        panStructFieldValuesFieldsOk structs fields ∧
          match lookupInfo name structs with
          | none => False
          | some info =>
              fields.map Prod.fst = info.fields.map Prod.fst ∧
                fields.map (panSemShapeOf ∘ Prod.snd) = info.fields.map Prod.snd
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructValuesFieldsOk [BEq String] (structs : StructContext) :
      List (PanValue α) → Prop
    | [] => True
    | value :: values =>
        panStructValueFieldsOk structs value ∧ panStructValuesFieldsOk structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructFieldValuesFieldsOk [BEq String] (structs : StructContext) :
      List (FieldName × PanValue α) → Prop
    | [] => True
    | (_, value) :: fields =>
        panStructValueFieldsOk structs value ∧ panStructFieldValuesFieldsOk structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Prop-valued Flapjack convenience predicate mirroring the equations of
      HOL `is_wf_shape_v_def`. It is not an exact port: HOL returns Bool, while
      this declaration returns Prop and uses `[BEq String]` lookup. -/
  def panStructValueShapeWf [BEq String] (structs : StructContext) :
      PanValue α → Prop
    | .word _ => True
    | .rStruct values => panStructValuesShapeWf structs values
    | .nStruct name fields =>
        (lookupInfo name structs ≠ none) ∧ panStructFieldValuesShapeWf structs fields
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructValuesShapeWf [BEq String] (structs : StructContext) :
      List (PanValue α) → Prop
    | [] => True
    | value :: values =>
        panStructValueShapeWf structs value ∧ panStructValuesShapeWf structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructFieldValuesShapeWf [BEq String] (structs : StructContext) :
      List (FieldName × PanValue α) → Prop
    | [] => True
    | (_, value) :: fields =>
        panStructValueShapeWf structs value ∧ panStructFieldValuesShapeWf structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- FEVERY adapters for PanSemState's total lookup functions. The shape-map
    premise below supplies finite support, so these universal clauses are the
    function-view translation of the HOL finite-map predicates. -/
def panStructEveryValueFieldsOk [BEq String] (structs : StructContext)
    (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value → panStructValueFieldsOk structs value

def panStructEveryValueShapeWf [BEq String] (structs : StructContext)
    (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value → panStructValueShapeWf structs value

/-- Function-view adapters of HOL's `FEVERY` premises for the Bool-valued
    PanStruct predicates. A `PanStructFiniteState` supplies the exact finite
    support and lookup relation for these production lookup functions. -/
def panStructEveryValueFieldsOkBool [BEq String]
    (structs : StructContext) (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value →
    panStructValueFieldsOkBool structs value = true

def panStructEveryValueShapeWfBool [BEq String]
    (structs : StructContext) (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value →
    panIsWfShapeValueBool structs value = true

/-- Pointwise view of the HOL equation
    `alist_to_fmap ctxt = FMAP_MAP2 (shape_of o SND) values`. This equality
    checks both lookup values and finite support. -/
def panStructShapeMapEq [BEq String] (shapes : InfoMap Shape)
    (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name, lookupInfo name shapes = (values name).map panSemShapeOf

def panStructContextShapeView (structs : StructContext) :
    List (StructName × InfoMap Shape) :=
  structs.map fun (name, info) => (name, info.fields)

private theorem lookupInfoWithRest_context_shape_view
    (left right : StructContext)
    (hview : panStructContextShapeView left = panStructContextShapeView right)
    (name : String) (info : StructInfo) (suffix : StructContext)
    (hlookup : lookupInfoWithRest name left = some (info, suffix)) :
    ∃ info' suffix', lookupInfoWithRest name right = some (info', suffix') ∧
      info'.fields = info.fields ∧
      panStructContextShapeView suffix = panStructContextShapeView suffix' := by
  induction left generalizing right info suffix with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry leftTail ih =>
      obtain ⟨leftName, leftInfo⟩ := entry
      cases right with
      | nil => simp [panStructContextShapeView] at hview
      | cons rightEntry rightTail =>
          obtain ⟨rightName, rightInfo⟩ := rightEntry
          rcases List.cons.inj (by
            simpa only [panStructContextShapeView, List.map_cons] using hview) with
            ⟨hhead, hviewTail⟩
          rcases Prod.mk.inj hhead with ⟨hname, hfields⟩
          subst rightName
          cases hmatch : leftName == name with
          | true =>
              have hpair : (leftInfo, leftTail) = (info, suffix) := by
                simpa [lookupInfoWithRest, hmatch] using hlookup
              rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
              exact ⟨rightInfo, rightTail, by simp [lookupInfoWithRest, hmatch],
                hfields.symm, hviewTail⟩
          | false =>
              simp only [lookupInfoWithRest, hmatch] at hlookup
              obtain ⟨info', suffix', hrestLookup, hfields', hviewSuffix⟩ :=
                ih rightTail hviewTail info suffix hlookup
              exact ⟨info', suffix', by
                simpa [lookupInfoWithRest, hmatch] using hrestLookup,
                hfields', hviewSuffix⟩

private theorem structCompileShapeWF_context_shape_view
    (left right : StructContext)
    (hview : panStructContextShapeView left = panStructContextShapeView right) :
    (∀ shape, structCompileShapeWF left shape = structCompileShapeWF right shape) ∧
    (∀ shapes, structCompileShapeWF.structCompileShapesWF left shapes =
      structCompileShapeWF.structCompileShapesWF right shapes) := by
  have hshape : ∀ context shape, ∀ other,
      panStructContextShapeView context = panStructContextShapeView other →
      structCompileShapeWF context shape = structCompileShapeWF other shape := by
    intro context shape
    apply structCompileShapeWF.induct
      (motive1 := fun context shapes => ∀ other,
        panStructContextShapeView context = panStructContextShapeView other →
        structCompileShapeWF.structCompileShapesWF context shapes =
          structCompileShapeWF.structCompileShapesWF other shapes)
      (motive2 := fun context shape => ∀ other,
        panStructContextShapeView context = panStructContextShapeView other →
        structCompileShapeWF context shape = structCompileShapeWF other shape)
    · intro context other hview
      simp [structCompileShapeWF.structCompileShapesWF]
    · intro context shape shapes ihShape ihShapes other hview
      simp only [structCompileShapeWF.structCompileShapesWF]
      rw [ihShape other hview, ihShapes other hview]
    · intro context other hview
      simp [structCompileShapeWF]
    · intro context shapes ih other hview
      simp only [structCompileShapeWF]
      rw [ih other hview]
    · intro context name info suffix hlookup ih other hview
      obtain ⟨info', suffix', hlookup', hfields, hviewSuffix⟩ :=
        lookupInfoWithRest_context_shape_view context other hview name info suffix hlookup
      have hcompiledLeft : structCompileShapeWF context (.named name) =
          .comb (structCompileShapeWF.structCompileShapesWF suffix
            (info.fields.map Prod.snd)) := by
        rw [structCompileShapeWF.eq_def]
        dsimp only
        rw [hlookup]
      have hcompiledRight : structCompileShapeWF other (.named name) =
          .comb (structCompileShapeWF.structCompileShapesWF suffix'
            (info'.fields.map Prod.snd)) := by
        rw [structCompileShapeWF.eq_def]
        dsimp only
        rw [hlookup']
      rw [hcompiledLeft, hcompiledRight]
      rw [hfields]
      congr 1
      exact ih suffix' hviewSuffix
    · intro context name hlookup other hview
      cases hright : lookupInfoWithRest name other with
      | none =>
          have hleftCompiled : structCompileShapeWF context (.named name) = .one := by
            rw [structCompileShapeWF.eq_def]
            dsimp only
            rw [hlookup]
          have hrightCompiled : structCompileShapeWF other (.named name) = .one := by
            rw [structCompileShapeWF.eq_def]
            dsimp only
            rw [hright]
          rw [hleftCompiled, hrightCompiled]
      | some entry =>
          obtain ⟨info, suffix⟩ := entry
          obtain ⟨_, _, hleft, _, _⟩ :=
            lookupInfoWithRest_context_shape_view other context hview.symm
              name info suffix hright
          rw [hlookup] at hleft
          cases hleft
  exact ⟨(fun shape => hshape left shape right hview),
    fun shapes => by
      rw [structCompileShapes_eq_map left, structCompileShapes_eq_map right]
      apply List.map_congr_left
      intro shape hmem
      exact hshape left shape right hview⟩

/-- Executable list-map counterpart of HOL `convert_code_def`. It converts
    each source-owned code entry and uses the original parameter shapes while
    compiling the body, as HOL does with `ctxt with locals := params`.
    This is intentionally untagged: HOL maps a finite map with unique keys,
    while `PanSemCodeMap` is an `InfoMap` list which may contain duplicate
    keys; this definition maps every list entry and cannot express HOL's
    finite-map domain invariant. -/
def panStructConvertCode [BEq String] (context : StructPassContext)
    (code : PanSemCodeMap α) : PanSemCodeMap α :=
  code.map fun (name, (parameters, body, returnShape)) =>
    (name,
      (parameters.map fun (parameter, shape) =>
          (parameter, structCompileShape context.structs shape),
        structCompileProg { context with locals := parameters } body,
        structCompileShape context.structs returnShape))

/-- Executable projection of HOL `convert_s_def` over `PanSemState`.
    The `structs` update and value conversion follow HOL; `code` is projected
    through the list-map helper above, and exception shapes through a total
    lookup function. This is intentionally untagged: `locals`, `globals`, and
    exception shapes are total lookup functions rather than finite maps, while
    code is an `InfoMap` list that may have duplicate keys. These interfaces
    cannot express HOL finite-map support or its exact `FMAP_MAP2` equations.
    The faithful finite-map state conversion remains open. -/
def panStructConvertState [BEq String] (context : StructPassContext)
    (state : PanSemState α ffi) : PanSemState α ffi where
  locals := fun name => (state.locals name).map panStructConvertValue
  globals := fun name => (state.globals name).map panStructConvertValue
  structs := []
  code := panStructConvertCode context state.code
  exceptionShapes := fun exception =>
    (state.exceptionShapes exception).map (structCompileShape context.structs)
  memory := state.memory
  memaddrs := state.memaddrs
  sharedMemaddrs := state.sharedMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddress := state.baseAddress
  topAddress := state.topAddress

/-- Production-evaluator API translation of the local HOL helper
    `compile_exp_correct_mmap_helper` (`pan_structsProofScript.sml:206`):
    successful evaluation of a source expression list and pointwise
    source-to-compiled-expression correctness imply successful evaluation of
    the compiled list with each value converted by `panStructConvertValue`.
    It is deliberately untagged: the HOL result is a local theorem over HOL's
    finite-map state and fixed-width `eval`, while this Lean theorem uses
    total lookup functions in `PanSemState` and an explicit `bytesInWord`
    evaluator argument. The list traversal, production compiler, pointwise
    hypothesis, and mapped conversion conclusion mirror the helper's proof
    contract; this declaration does not claim an exact statement port. -/
theorem panStructCompileExpsEvalOfPointwiseCorrect
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (expressions : List (Exp α))
    (values : List (PanValue α))
    (hsource : evalPanValueExps state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord expressions =
        some values)
    (hpointwise : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanValueExp state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression = some value →
      evalPanValueExp (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression) = some (panStructConvertValue value)) :
    evalPanValueExps (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp.structCompileExps context expressions) =
        some (values.map panStructConvertValue) := by
  induction expressions generalizing values with
  | nil =>
      simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
        structCompileExp.structCompileExps] at hsource ⊢
      cases values with
      | nil => rfl
      | cons value values => simp at hsource
  | cons expression expressions ih =>
      simp only [evalPanValueExps,
        evalPanValueExp.evalPanValueExps] at hsource
      cases hhead : evalPanValueExp state.structs state.locals state.globals
          state.memory state.baseAddress state.topAddress bytesInWord expression with
      | none => simp [hhead] at hsource
      | some value =>
          cases htail : evalPanValueExp.evalPanValueExps state.structs
              state.locals state.globals state.memory state.baseAddress state.topAddress
              bytesInWord expressions with
          | none => simp [hhead, htail] at hsource
          | some tailValues =>
              have hsourceEq : value :: tailValues = values := by
                simpa [hhead, htail] using hsource
              have hpointwiseTail : ∀ tailExpression,
                  tailExpression ∈ expressions → ∀ tailValue,
                    evalPanValueExp state.structs state.locals state.globals
                        state.memory state.baseAddress state.topAddress bytesInWord
                        tailExpression = some tailValue →
                    evalPanValueExp (panStructConvertState context state).structs
                        (panStructConvertState context state).locals
                        (panStructConvertState context state).globals
                        (panStructConvertState context state).memory
                        (panStructConvertState context state).baseAddress
                        (panStructConvertState context state).topAddress bytesInWord
                        (structCompileExp context tailExpression) =
                      some (panStructConvertValue tailValue) := by
                intro tailExpression hmem tailValue htailEval
                exact hpointwise tailExpression (by simp [hmem]) tailValue htailEval
              have htargetHead := hpointwise expression (by simp) value hhead
              have htargetTail := ih tailValues htail hpointwiseTail
              change evalPanValueExp.evalPanValueExps
                (panStructConvertState context state).structs
                (panStructConvertState context state).locals
                (panStructConvertState context state).globals
                (panStructConvertState context state).memory
                (panStructConvertState context state).baseAddress
                (panStructConvertState context state).topAddress bytesInWord
                (structCompileExp.structCompileExps context expressions) =
                  some (List.map panStructConvertValue tailValues) at htargetTail
              subst values
              simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
                structCompileExp.structCompileExps, htargetHead, htargetTail]

/-- Full-evaluator version of the pointwise `OPT_MMAP` support used by the
    Op constructor case. It carries one explicit memory adapter through every
    operand and the compiled operand list. This remains an untagged Lean
    helper: HOL's helper uses finite-map state and the fixed-width evaluator. -/
theorem panStructCompileExpsFullEvalOfPointwiseCorrect
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (expressions : List (Exp α)) (values : List (PanValue α))
    (hsource : evalPanValueExpsFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord expressions
      (memoryAccess := some memoryAccess) = some values)
    (hpointwise : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := some memoryAccess) = some value →
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression)
        (memoryAccess := some memoryAccess) = some (panStructConvertValue value)) :
    evalPanValueExpsFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp.structCompileExps context expressions)
      (memoryAccess := some memoryAccess) = some (values.map panStructConvertValue) := by
  induction expressions generalizing values with
  | nil =>
      cases values <;> simp_all [evalPanValueExpsFull, structCompileExp.structCompileExps]
  | cons expression expressions ih =>
      simp only [evalPanValueExpsFull] at hsource
      cases hhead : evalPanValueExpFull state.structs state.locals state.globals
          state.memory state.baseAddress state.topAddress bytesInWord expression
          (memoryAccess := some memoryAccess) with
      | none => simp [hhead] at hsource
      | some value =>
          cases htail : evalPanValueExpsFull state.structs state.locals state.globals
              state.memory state.baseAddress state.topAddress bytesInWord expressions
              (memoryAccess := some memoryAccess) with
          | none => simp [hhead, htail] at hsource
          | some tailValues =>
              have hvalues : value :: tailValues = values := by
                simpa [hhead, htail] using hsource
              have hpointwiseTail : ∀ tailExpression,
                  tailExpression ∈ expressions → ∀ tailValue,
                    evalPanValueExpFull state.structs state.locals state.globals
                        state.memory state.baseAddress state.topAddress bytesInWord
                        tailExpression (memoryAccess := some memoryAccess) = some tailValue →
                    evalPanValueExpFull (panStructConvertState context state).structs
                        (panStructConvertState context state).locals
                        (panStructConvertState context state).globals
                        (panStructConvertState context state).memory
                        (panStructConvertState context state).baseAddress
                        (panStructConvertState context state).topAddress bytesInWord
                        (structCompileExp context tailExpression)
                        (memoryAccess := some memoryAccess) =
                      some (panStructConvertValue tailValue) := by
                intro tailExpression hmem tailValue htailEval
                exact hpointwise tailExpression (by simp [hmem]) tailValue htailEval
              have htargetHead := hpointwise expression (by simp) value hhead
              have htargetTail := ih tailValues htail hpointwiseTail
              subst values
              simp [evalPanValueExpsFull,
                structCompileExp.structCompileExps, htargetHead, htargetTail]

inductive PanStructAll {α : Type} (predicate : α → Prop) : List α → Prop
  | nil : PanStructAll predicate []
  | cons {head tail} : predicate head → PanStructAll predicate tail →
      PanStructAll predicate (head :: tail)

private theorem panStructAll_mem {α : Type} {predicate : α → Prop}
    {values : List α} (hvalues : PanStructAll predicate values) :
    ∀ value, value ∈ values → predicate value := by
  induction hvalues with
  | nil => intro value hmem; simp at hmem
  | @cons head tail hhead htail ih =>
      intro value hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · subst value
        exact hhead
      · exact ih value hmem

private theorem panStructAll_map {α : Type} {source target : α → Prop}
    (transform : ∀ value, source value → target value) {values : List α}
    (hvalues : PanStructAll source values) : PanStructAll target values := by
  induction hvalues with
  | nil => exact .nil
  | @cons value values hhead htail ih =>
      exact .cons (transform value hhead) ih

private theorem panStructConvertValues_eq_map (values : List (PanValue α)) :
    panStructConvertValues values = values.map panStructConvertValue := by
  induction values with
  | nil => simp [panStructConvertValues]
  | cons value values ih => simp [panStructConvertValues, ih]

private theorem panStructConvertFieldValues_eq_map
    (fields : List (FieldName × PanValue α)) :
    panStructConvertFieldValues fields = fields.map (panStructConvertValue ∘ Prod.snd) := by
  induction fields with
  | nil => simp [panStructConvertFieldValues]
  | cons field fields ih =>
      cases field with
      | mk name value => simp [panStructConvertFieldValues, ih]

/-- Flapjack-specific name-forgetful map from the exact `panSem$v` carrier to the
    executable `PanValue`, decoding `mlstring` records/fields by their bytes. It
    states the production bridge for the exact `convert_v` port and has no HOL
    counterpart. -/
def ValueHOL.toPanValue {width : Nat} [NeZero width] :
    ValueHOL width → PanValue (BitVec width)
  | .val (.word bits) => .word bits
  | .rStruct fields => .rStruct (fields.map ValueHOL.toPanValue)
  | .nStruct name fields =>
      .nStruct (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
        (fields.map (fun pair =>
          (Flapjack.Basis.Pure.MlString.toStringOfBytes pair.1,
            ValueHOL.toPanValue pair.2)))
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
    | (rename_i hmem
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)
    | (rename_i hmem
       have hsnd : sizeOf pair.snd < sizeOf pair := by cases pair; simp +arith
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)

theorem convertV_toPanValue {width : Nat} [NeZero width] (value : ValueHOL width) :
    (convertV value).toPanValue = panStructConvertValue value.toPanValue := by
  induction value using convertV.induct with
  | case1 value => cases value with
      | word bits => simp only [convertV, ValueHOL.toPanValue, panStructConvertValue]
  | case2 fields ih =>
      simp only [convertV, ValueHOL.toPanValue, panStructConvertValue,
        panStructConvertValues_eq_map, List.map_map]
      apply congrArg PanValue.rStruct
      apply List.map_congr_left
      intro x hx
      exact ih x hx
  | case3 name fields ih =>
      simp only [convertV, ValueHOL.toPanValue, panStructConvertValue,
        panStructConvertFieldValues_eq_map, List.map_map]
      apply congrArg PanValue.rStruct
      apply List.map_congr_left
      intro pair hpair
      exact ih pair hpair

private theorem panValueFlatContextFuel_lookup_ge
    (name : String) (context : StructContext) (info : StructInfo)
    (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix)) :
    panValueFlatContextFuel suffix + panValueFlatFieldsFuel info.fields ≤
      panValueFlatContextFuel context := by
  induction context generalizing name info suffix with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      by_cases hmatch : candidate == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
        rcases hlookup with ⟨rfl, rfl⟩
        simp only [panValueFlatContextFuel]
        omega
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        have htail := ih name info suffix hlookup
        simp only [panValueFlatContextFuel]
        omega

mutual
  def panShapeHasNoNamed : Shape → Bool
    | .one => true
    | .comb shapes => panShapeListHasNoNamed shapes
    | .named _ => false

  def panShapeListHasNoNamed : List Shape → Bool
    | [] => true
    | shape :: shapes => panShapeHasNoNamed shape && panShapeListHasNoNamed shapes
end

/-! One/Comb branch of HOL `mem_load_conversion` at
    `pan_structsProofScript.sml:609`. This support theorem relates the
    production fuel-indexed loader across `structCompileShapeWF`; it is
    intentionally untagged because HOL's `mem_load` uses a finite address
    domain and word-labelled state memory, while this helper is stated over
    the production `readWord` callback. The no-named-shape premise isolates
    precisely the One/Comb induction branches. `structCompileShapeWF_size`
    supplies the address-step equality used by recursive Comb loads. -/
mutual
  theorem panValueFlatLoadFuel_convert_one_comb [BEq α] [Add α]
      (context : StructContext) (hok : structInfosOk context)
      (readWord : α → Option α) (bytesInWord : α) (shape : Shape) :
      panShapeHasNoNamed shape = true →
      isWfShape context shape = true →
      ∀ (fuel : Nat) (address : α) (value : PanValue α),
        panValueFlatLoadFuel context readWord bytesInWord fuel shape address = some value →
        panValueFlatLoadFuel [] readWord bytesInWord fuel
          (structCompileShapeWF context shape) address =
          some (panStructConvertValue value) := by
    intro hflat hwf fuel address value hload
    cases shape with
    | one =>
        cases fuel with
        | zero => simp [panValueFlatLoadFuel] at hload
        | succ fuel =>
            simp only [panValueFlatLoadFuel] at hload
            cases hread : readWord address with
            | none => simp [hread] at hload
            | some word =>
                have hvalue : .word word = value := by simpa [hread] using hload
                cases hvalue
                simp [panValueFlatLoadFuel, structCompileShapeWF, hread,
                  panStructConvertValue]
    | comb shapes =>
        simp only [panShapeHasNoNamed] at hflat
        simp only [isWfShape] at hwf
        cases fuel with
        | zero => simp [panValueFlatLoadFuel] at hload
        | succ fuel =>
            simp only [panValueFlatLoadFuel] at hload
            cases hvalues : panValueFlatLoadListFuel context readWord bytesInWord fuel
                shapes address with
            | none => simp [hvalues] at hload
            | some values =>
                have hvalue : .rStruct values = value := by
                  simpa [hvalues] using hload
                cases hvalue
                have hconverted := panValueFlatLoadListFuel_convert_one_comb
                  context hok readWord bytesInWord shapes hflat hwf fuel address values hvalues
                have hconverted' :
                    panValueFlatLoadListFuel [] readWord bytesInWord fuel
                      (structCompileShapeWF.structCompileShapesWF context shapes) address =
                    some (panStructConvertValues values) := by
                  simpa [panStructConvertValues_eq_map] using hconverted
                simpa [panValueFlatLoadFuel, structCompileShapeWF.eq_def,
                  structCompileShapes_eq_map, panStructConvertValue] using
                  congrArg (Option.map PanValue.rStruct) hconverted'
    | named name => simp [panShapeHasNoNamed] at hflat

  theorem panValueFlatLoadListFuel_convert_one_comb [BEq α] [Add α]
      (context : StructContext) (hok : structInfosOk context)
      (readWord : α → Option α) (bytesInWord : α) (shapes : List Shape) :
      panShapeListHasNoNamed shapes = true →
      isWfShape.isWfShapeList context shapes = true →
      ∀ (fuel : Nat) (address : α) (values : List (PanValue α)),
        panValueFlatLoadListFuel context readWord bytesInWord fuel shapes address = some values →
        panValueFlatLoadListFuel [] readWord bytesInWord fuel
          (structCompileShapeWF.structCompileShapesWF context shapes) address =
          some (values.map panStructConvertValue) := by
    intro hflat hwf fuel address values hload
    cases shapes with
    | nil =>
        simp only [panValueFlatLoadListFuel] at hload
        cases hload
        simp [panValueFlatLoadListFuel, structCompileShapeWF.structCompileShapesWF]
    | cons shape shapes =>
        cases fuel with
        | zero => simp [panValueFlatLoadListFuel] at hload
        | succ fuel =>
            simp only [panShapeListHasNoNamed, Bool.and_eq_true] at hflat
            simp only [isWfShape.isWfShapeList, Bool.and_eq_true] at hwf
            simp only [panValueFlatLoadListFuel] at hload
            cases hhead : panValueFlatLoadFuel context readWord bytesInWord fuel shape address with
            | none => simp [hhead] at hload
            | some head =>
                let nextAddress := panValueFlatOffset bytesInWord address
                  (shapeSizeWithContext context shape)
                cases htail : panValueFlatLoadListFuel context readWord bytesInWord fuel shapes
                    nextAddress with
                | none =>
                    dsimp [nextAddress] at htail
                    simp [hhead, htail] at hload
                | some tail =>
                    dsimp [nextAddress] at htail
                    have hheadConverted := panValueFlatLoadFuel_convert_one_comb
                      context hok readWord bytesInWord shape hflat.1 hwf.1 fuel address head hhead
                    have htailConverted := panValueFlatLoadListFuel_convert_one_comb
                      context hok readWord bytesInWord shapes hflat.2 hwf.2 fuel nextAddress tail htail
                    have hsize := structCompileShapeWF_size context shape hwf.1 hok
                    have hoffset : panValueFlatOffset bytesInWord address
                        (shapeSizeWithContext [] (structCompileShapeWF context shape)) =
                        nextAddress := by
                      simp [nextAddress, hsize]
                    have hvalues : values = head :: tail := by
                      simp [Option.bind, hhead, htail] at hload
                      exact hload.symm
                    subst values
                    have htailConverted' :
                        panValueFlatLoadListFuel [] readWord bytesInWord fuel
                          (List.map (structCompileShapeWF context) shapes) nextAddress =
                        some (List.map panStructConvertValue tail) := by
                      simpa only [structCompileShapes_eq_map] using htailConverted
                    simp only [structCompileShapes_eq_map, List.map_cons,
                      panValueFlatLoadListFuel]
                    rw [hheadConverted, hoffset, htailConverted']
                    simp
end

private theorem lookupInfoWithRest_suffix_drop_for_load
    (name : String) (context : StructContext) (info : StructInfo)
    (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix)) :
    ∃ n, context.drop n = suffix := by
  induction context with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      by_cases hmatch : candidate == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
        rcases hlookup with ⟨rfl, rfl⟩
        exact ⟨1, by simp⟩
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        obtain ⟨n, hn⟩ := ih hlookup
        refine ⟨n + 1, ?_⟩
        simpa [List.drop_succ_cons, Nat.succ_eq_add_one] using hn

private theorem structInfosOk_suffix_for_load
    (name : String) (context : StructContext) (info : StructInfo)
    (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix))
    (hok : structInfosOk context) :
    structInfosOk suffix := by
  obtain ⟨n, hdrop⟩ := lookupInfoWithRest_suffix_drop_for_load
    name context info suffix hlookup
  rw [← hdrop]
  exact structInfosOk_drop n context hok

private theorem lookupInfoWithRest_fields_wf_for_load
    (name : String) (context : StructContext) (info : StructInfo)
    (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix))
    (hok : structInfosOk context) :
    isWfShape.isWfShapeList suffix (info.fields.map Prod.snd) = true := by
  induction context with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      by_cases hmatch : candidate == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
        rcases hlookup with ⟨rfl, rfl⟩
        obtain ⟨_, _, hfields, _⟩ := hok
        have hhead := hfields 0 candidate entryInfo (by simp)
        have htail : ((candidate, entryInfo) :: context).drop 1 = context := rfl
        rw [htail] at hhead
        exact isWfShapeList_of_all (fun shape hshape => hhead shape hshape)
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        exact ih hlookup (structInfosOk_drop 1 ((candidate, entryInfo) :: context) hok)

private theorem panValueFlatFieldsFuel_eq_shapeListFuel
    (fields : List (FieldName × Shape)) :
    panValueFlatFieldsFuel fields =
      panValueFlatShapeFuel.panValueFlatShapeListFuel (fields.map Prod.snd) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      cases field
      simp [panValueFlatFieldsFuel, panValueFlatShapeFuel.panValueFlatShapeListFuel, ih]

/-! General `Named` load conversion used by the HOL `mem_load_conversion`
    step. This theorem is untagged: production loading is `Option`-valued with
    explicit `bytesInWord` and a `readWord` callback, whereas HOL uses a finite
    address domain and word-labelled memory. -/
theorem panValueFlatLoadFuel_convert_all [BEq α] [Add α]
    (bytesInWord : α) (readWord : α → Option α) :
    ∀ (context : StructContext) (fuelSource : Nat) (shape : Shape) (address : α)
      (fuelTarget : Nat) (value : PanValue α),
      structInfosOk context →
      isWfShape context shape = true →
      panValueFlatContextFuel context + panValueFlatShapeFuel shape + 1 ≤ fuelSource →
      panValueFlatShapeFuel (structCompileShapeWF context shape) + 1 ≤ fuelTarget →
      panValueFlatLoadFuel context readWord bytesInWord fuelSource shape address =
        some value →
      panValueFlatLoadFuel [] readWord bytesInWord fuelTarget
        (structCompileShapeWF context shape) address =
          some (panStructConvertValue value) := by
  apply panValueFlatLoadFuel.induct (α := α) bytesInWord
    (motive1 := fun context fuel shape address =>
      ∀ fuelTarget value, structInfosOk context →
        isWfShape context shape = true →
        panValueFlatContextFuel context + panValueFlatShapeFuel shape + 1 ≤ fuel →
        panValueFlatShapeFuel (structCompileShapeWF context shape) + 1 ≤ fuelTarget →
        panValueFlatLoadFuel context readWord bytesInWord fuel shape address =
          some value →
        panValueFlatLoadFuel [] readWord bytesInWord fuelTarget
          (structCompileShapeWF context shape) address =
            some (panStructConvertValue value))
    (motive2 := fun context fuel fields address =>
      ∀ fuelTarget values, structInfosOk context →
        isWfShape.isWfShapeList context (fields.map Prod.snd) = true →
        panValueFlatContextFuel context + panValueFlatFieldsFuel fields + 1 ≤ fuel →
        panValueFlatShapeFuel.panValueFlatShapeListFuel
          (structCompileShapeWF.structCompileShapesWF context (fields.map Prod.snd)) +
            1 ≤ fuelTarget →
        panValueFlatLoadFieldsFuel context readWord bytesInWord fuel fields address =
          some values →
        panValueFlatLoadListFuel [] readWord bytesInWord fuelTarget
          (structCompileShapeWF.structCompileShapesWF context (fields.map Prod.snd)) address =
            some (values.map (panStructConvertValue ∘ Prod.snd)))
    (motive3 := fun context fuel shapes address =>
      ∀ fuelTarget values, structInfosOk context →
        isWfShape.isWfShapeList context shapes = true →
        panValueFlatContextFuel context +
          panValueFlatShapeFuel.panValueFlatShapeListFuel shapes + 1 ≤ fuel →
        panValueFlatShapeFuel.panValueFlatShapeListFuel
          (structCompileShapeWF.structCompileShapesWF context shapes) +
            1 ≤ fuelTarget →
        panValueFlatLoadListFuel context readWord bytesInWord fuel shapes address =
          some values →
        panValueFlatLoadListFuel [] readWord bytesInWord fuelTarget
          (structCompileShapeWF.structCompileShapesWF context shapes) address =
            some (values.map panStructConvertValue))
  · intro context shape address fuelTarget value hok hwf hsource htarget hload
    have hshapeFuel := panValueFlatShapeFuel_pos shape
    omega
  · intro context fuel address fuelTarget value hok hwf hsource htarget hload
    cases fuelTarget with
    | zero => omega
    | succ fuelTarget =>
        simp only [panValueFlatLoadFuel] at hload
        cases hread : readWord address with
        | none => simp [hread] at hload
        | some word =>
            have hvalue : PanValue.word word = value := by
              simpa [hread] using hload
            cases hvalue
            simp [structCompileShapeWF, panValueFlatLoadFuel,
              panStructConvertValue, hread]
  · intro context fuel shapes address ih fuelTarget value hok hwf hsource htarget hload
    have hwfList : isWfShape.isWfShapeList context shapes = true := by
      simpa [isWfShape] using hwf
    simp only [panValueFlatLoadFuel] at hload
    cases hvalues : panValueFlatLoadListFuel context readWord bytesInWord fuel
        shapes address with
    | none => simp [hvalues] at hload
    | some values =>
        have hvalue : PanValue.rStruct values = value := by
          simpa [hvalues] using hload
        cases hvalue
        have hsourceList :
            panValueFlatContextFuel context +
                panValueFlatShapeFuel.panValueFlatShapeListFuel shapes + 1 ≤ fuel := by
          simp only [panValueFlatShapeFuel] at hsource
          omega
        cases fuelTarget with
        | zero => omega
        | succ fuelTarget =>
            have htargetList :
                panValueFlatShapeFuel.panValueFlatShapeListFuel
                    (structCompileShapeWF.structCompileShapesWF context shapes) + 1 ≤
                  fuelTarget := by
              simp only [structCompileShapeWF.eq_def,
                panValueFlatShapeFuel] at htarget
              omega
            have hconverted := ih fuelTarget values hok hwfList hsourceList
              htargetList hvalues
            simpa [structCompileShapeWF.eq_def, structCompileShapes_eq_map,
              panValueFlatLoadFuel, panStructConvertValue,
              panStructConvertValues_eq_map] using
              congrArg (Option.map PanValue.rStruct) hconverted
  · intro context fuel name address ih fuelTarget value hok hwf hsource htarget hload
    cases hlookup : lookupInfoWithRest name context with
    | none => simp [panValueFlatLoadFuel, hlookup] at hload
    | some entry =>
        obtain ⟨info, suffix⟩ := entry
        have hokSuffix := structInfosOk_suffix_for_load
          name context info suffix hlookup hok
        have hfieldsWf := lookupInfoWithRest_fields_wf_for_load
          name context info suffix hlookup hok
        have hcontextFuel := panValueFlatContextFuel_lookup_ge
          name context info suffix hlookup
        simp only [panValueFlatLoadFuel] at hload
        cases hfields : panValueFlatLoadFieldsFuel suffix readWord bytesInWord fuel
            info.fields address with
        | none => simp [hlookup, hfields] at hload
        | some fields =>
            have hvalue : PanValue.nStruct name fields = value := by
              simpa [panValueFlatLoadFuel, hlookup, hfields] using hload
            cases hvalue
            have hsourceFields :
                panValueFlatContextFuel suffix + panValueFlatFieldsFuel info.fields + 1 ≤
                  fuel := by
              simp only [panValueFlatShapeFuel] at hsource
              omega
            have hcompileEq :
              structCompileShapeWF context (.named name) =
                  .comb (structCompileShapeWF.structCompileShapesWF suffix
                    (info.fields.map Prod.snd)) := by
              rw [structCompileShapeWF.eq_def]
              split
              · simp_all
              · simp_all
              · split <;> simp_all
            cases fuelTarget with
            | zero => omega
            | succ fuelTarget =>
                have htargetFields :
                    panValueFlatShapeFuel.panValueFlatShapeListFuel
                        (structCompileShapeWF.structCompileShapesWF suffix
                          (info.fields.map Prod.snd)) + 1 ≤ fuelTarget := by
                  rw [hcompileEq] at htarget
                  simp only [panValueFlatShapeFuel] at htarget
                  omega
                have hconverted := ih info suffix fuelTarget fields hokSuffix hfieldsWf
                  hsourceFields htargetFields hfields
                rw [hcompileEq]
                simpa [panValueFlatLoadFuel, panStructConvertValue,
                  panStructConvertFieldValues_eq_map, List.map_map,
                  Function.comp_def] using
                  congrArg (Option.map PanValue.rStruct) hconverted
  · intro context fuel address fuelTarget values hok hwf hsource htarget hload
    simp [panValueFlatLoadFieldsFuel] at hload
    subst values
    simp [structCompileShapeWF.structCompileShapesWF, panValueFlatLoadListFuel]
  · intro context head tail address fuelTarget values hok hwf hsource htarget hload
    simp_all
  · intro context fuel field shape fields address ihHead ihTail fuelTarget values
      hok hwf hsource htarget hload
    simp only [List.map_cons, isWfShape.isWfShapeList, Bool.and_eq_true] at hwf
    cases hhead : panValueFlatLoadFuel context readWord bytesInWord fuel shape address with
    | none => simp_all [panValueFlatLoadFieldsFuel]
    | some value =>
        let nextAddress := panValueFlatOffset bytesInWord address
          (shapeSizeWithContext context shape)
        cases htail : panValueFlatLoadFieldsFuel context readWord bytesInWord fuel fields
            nextAddress with
        | none => simp_all [panValueFlatLoadFieldsFuel, nextAddress]
        | some tailValues =>
            have hsourceHead :
                panValueFlatContextFuel context + panValueFlatShapeFuel shape + 1 ≤ fuel := by
              simp only [panValueFlatFieldsFuel] at hsource
              omega
            have hsourceTail :
                panValueFlatContextFuel context + panValueFlatFieldsFuel fields + 1 ≤ fuel := by
              simp only [panValueFlatFieldsFuel] at hsource
              omega
            cases fuelTarget with
            | zero => omega
            | succ fuelTarget =>
                have htargetParts :
                    panValueFlatShapeFuel (structCompileShapeWF context shape) + 1 ≤ fuelTarget ∧
                    panValueFlatShapeFuel.panValueFlatShapeListFuel
                        (structCompileShapeWF.structCompileShapesWF context
                          (fields.map Prod.snd)) + 1 ≤ fuelTarget := by
                  simp only [List.map_cons, structCompileShapeWF.structCompileShapesWF,
                    panValueFlatShapeFuel.panValueFlatShapeListFuel] at htarget
                  omega
                have hheadConverted := ihHead fuelTarget value hok hwf.1
                  hsourceHead htargetParts.1 hhead
                have htailConverted := ihTail fuelTarget tailValues hok hwf.2
                  hsourceTail htargetParts.2 htail
                have hsize := structCompileShapeWF_size context shape hwf.1 hok
                have hoffset :
                    panValueFlatOffset bytesInWord address
                        (shapeSizeWithContext [] (structCompileShapeWF context shape)) =
                      nextAddress := by
                  simp [nextAddress, hsize]
                have hvalues : values = (field, value) :: tailValues := by
                  simpa [panValueFlatLoadFieldsFuel, hhead, htail, nextAddress] using hload.symm
                subst values
                simp only [List.map_cons, structCompileShapeWF.structCompileShapesWF,
                  panValueFlatLoadListFuel]
                rw [hheadConverted, hoffset, htailConverted]
                simp [Function.comp_def]
  · intro context fuel address fuelTarget values hok hwf hsource htarget hload
    simp [panValueFlatLoadListFuel] at hload
    subst values
    simp [structCompileShapeWF.structCompileShapesWF, panValueFlatLoadListFuel]
  · intro context head tail address fuelTarget values hok hwf hsource htarget hload
    simp [panValueFlatLoadListFuel] at hload
  · intro context fuel shape shapes address ihHead ihTail fuelTarget values
      hok hwf hsource htarget hload
    simp only [isWfShape.isWfShapeList, Bool.and_eq_true] at hwf
    cases hhead : panValueFlatLoadFuel context readWord bytesInWord fuel shape address with
    | none => simp [panValueFlatLoadListFuel, hhead] at hload
    | some value =>
        let nextAddress := panValueFlatOffset bytesInWord address
          (shapeSizeWithContext context shape)
        cases htail : panValueFlatLoadListFuel context readWord bytesInWord fuel shapes
            nextAddress with
        | none => simp [panValueFlatLoadListFuel, hhead, htail, nextAddress] at hload
        | some tailValues =>
            have hsourceHead :
                panValueFlatContextFuel context + panValueFlatShapeFuel shape + 1 ≤ fuel := by
              simp only [panValueFlatShapeFuel.panValueFlatShapeListFuel] at hsource
              omega
            have hsourceTail :
                panValueFlatContextFuel context +
                    panValueFlatShapeFuel.panValueFlatShapeListFuel shapes + 1 ≤ fuel := by
              simp only [panValueFlatShapeFuel.panValueFlatShapeListFuel] at hsource
              omega
            cases fuelTarget with
            | zero => omega
            | succ fuelTarget =>
                have htargetParts :
                    panValueFlatShapeFuel (structCompileShapeWF context shape) + 1 ≤ fuelTarget ∧
                    panValueFlatShapeFuel.panValueFlatShapeListFuel
                        (structCompileShapeWF.structCompileShapesWF context shapes) + 1 ≤
                          fuelTarget := by
                  simp only [structCompileShapeWF.structCompileShapesWF,
                    panValueFlatShapeFuel.panValueFlatShapeListFuel] at htarget
                  omega
                have hheadConverted := ihHead fuelTarget value hok hwf.1
                  hsourceHead htargetParts.1 hhead
                have htailConverted := ihTail fuelTarget tailValues hok hwf.2
                  hsourceTail htargetParts.2 htail
                have hsize := structCompileShapeWF_size context shape hwf.1 hok
                have hoffset :
                    panValueFlatOffset bytesInWord address
                        (shapeSizeWithContext [] (structCompileShapeWF context shape)) =
                      nextAddress := by
                  simp [nextAddress, hsize]
                have hvalues : values = value :: tailValues := by
                  simpa [panValueFlatLoadListFuel, hhead, htail, nextAddress] using hload.symm
                subst values
                simp only [structCompileShapeWF.structCompileShapesWF,
                  panValueFlatLoadListFuel]
                rw [hheadConverted, hoffset, htailConverted]
                simp

/-! Two-context form used by the HOL `compile_exp_correct` Load case. The
    source loader uses the runtime struct context, while production compiles
    the requested shape against the context view. Projected name/field-view
    equality suffices; full `StructInfo` and cached-size equality are not
    assumed. The helper is untagged because its explicit fuel, readWord
    callback, and Bool shape premise differ from HOL `mem_load_conversion`. -/
theorem panValueFlatLoadFuel_convert_all_context_shape_view [BEq α] [Add α]
    (bytesInWord : α) (readWord : α → Option α)
    (sourceContext compileContext : StructContext)
    (hview : panStructContextShapeView compileContext =
      panStructContextShapeView sourceContext)
    (fuelSource : Nat) (shape : Shape) (address : α)
    (fuelTarget : Nat) (value : PanValue α)
    (hstructInfos : structInfosOk sourceContext)
    (hwf : isWfShape sourceContext shape = true)
    (hsourceFuel : panValueFlatContextFuel sourceContext +
      panValueFlatShapeFuel shape + 1 ≤ fuelSource)
    (htargetFuel : panValueFlatShapeFuel
      (structCompileShapeWF compileContext shape) + 1 ≤ fuelTarget)
    (hload : panValueFlatLoadFuel sourceContext readWord bytesInWord fuelSource
      shape address = some value) :
    panValueFlatLoadFuel [] readWord bytesInWord fuelTarget
      (structCompileShapeWF compileContext shape) address =
        some (panStructConvertValue value) := by
  have hcompiledShape : structCompileShapeWF compileContext shape =
      structCompileShapeWF sourceContext shape :=
    (structCompileShapeWF_context_shape_view compileContext sourceContext hview).1 shape
  have htargetFuelSource : panValueFlatShapeFuel
      (structCompileShapeWF sourceContext shape) + 1 ≤ fuelTarget := by
    rw [← hcompiledShape]
    exact htargetFuel
  rw [hcompiledShape]
  exact panValueFlatLoadFuel_convert_all bytesInWord readWord sourceContext
    fuelSource shape address fuelTarget value hstructInfos hwf hsourceFuel
    htargetFuelSource hload

private theorem panValueFieldsHaveShapesNames [BEq String] [LawfulBEq String]
    (context : StructContext) (expected : List (FieldName × Shape))
    (actual : List (FieldName × PanValue α))
    (h : panValueFieldsHaveShapes context expected actual = true) :
    expected.map Prod.fst = actual.map Prod.fst := by
  induction expected generalizing actual with
  | nil =>
      cases actual with
      | nil => rfl
      | cons field actual => simp [panValueFieldsHaveShapes] at h
  | cons field expected ih =>
      cases actual with
      | nil => simp [panValueFieldsHaveShapes] at h
      | cons value actual =>
          have hparts :
              ((@BEq.beq FieldName instBEqOfDecidableEq field.1 value.1) = true ∧
                panShapeMatches (panValueShape context value.2) field.2 = true) ∧
              panValueFieldsHaveShapes context expected actual = true := by
            simpa only [panValueFieldsHaveShapes, Bool.and_eq_true] using h
          rcases hparts with ⟨⟨hname, _hshape⟩, htail⟩
          have hnameEq : field.1 = value.1 := instLawfulBEqString.eq_of_beq hname
          have htailNames := ih actual htail
          simp [hnameEq, htailNames]

mutual
  private theorem panValueShape_matches_eq [LawfulBEq String]
      (context : StructContext) (value : PanValue α) (shape : Shape)
      (hmatch : panShapeMatches (panValueShape context value) shape = true) :
      panValueShape context value = shape := by
    cases value with
    | word word => cases shape <;> simp [panValueShape, panShapeMatches] at hmatch ⊢
    | nStruct name fields =>
        cases shape with
        | named shapeName =>
            simp only [panValueShape, panShapeMatches] at hmatch
            have hname : name = shapeName := instLawfulBEqString.eq_of_beq hmatch
            subst shapeName
            simp [panValueShape]
        | one => simp [panValueShape, panShapeMatches] at hmatch
        | comb shapes => simp [panValueShape, panShapeMatches] at hmatch
    | rStruct values =>
        cases shape with
        | comb shapes =>
            have hshapes :
                panShapeMatches.panShapeListMatches
                  (values.map (panValueShape context)) shapes = true := by
              simpa only [panValueShape, panShapeMatches] using hmatch
            have hshapeList := panValueShapeList_matches_eq context values shapes hshapes
            simp only [panValueShape, hshapeList]
        | one => simp [panValueShape, panShapeMatches] at hmatch
        | named name => simp [panValueShape, panShapeMatches] at hmatch

  private theorem panValueShapeList_matches_eq [LawfulBEq String]
      (context : StructContext) (values : List (PanValue α)) (shapes : List Shape)
      (hmatch : panShapeMatches.panShapeListMatches
        (values.map (panValueShape context)) shapes = true) :
      values.map (panValueShape context) = shapes := by
    cases values with
    | nil => cases shapes <;> simp [panShapeMatches.panShapeListMatches] at hmatch ⊢
    | cons value values =>
        cases shapes with
        | nil => simp [panShapeMatches.panShapeListMatches] at hmatch
        | cons shape shapes =>
            simp only [List.map_cons, panShapeMatches.panShapeListMatches,
              Bool.and_eq_true] at hmatch
            rcases hmatch with ⟨hhead, htail⟩
            simp [panValueShape_matches_eq context value shape hhead,
              panValueShapeList_matches_eq context values shapes htail]
end

private theorem lookupPanValueField_eq_lookupInfo [BEq String] [LawfulBEq String]
    (name : FieldName) (fields : List (FieldName × PanValue α)) :
    lookupPanValueField name fields = lookupInfo name fields := by
  induction fields with
  | nil => rfl
  | cons entry fields ih =>
      rcases entry with ⟨field, value⟩
      by_cases h : field = name
      · simp [lookupPanValueField, lookupInfo, h]
      · simp [lookupPanValueField, lookupInfo, h, ih]

private theorem panValueFieldsHaveShapes_lookup [BEq String] [LawfulBEq String]
    (context : StructContext) (expected : List (FieldName × Shape))
    (actual : List (FieldName × PanValue α)) (name : FieldName) (value : PanValue α)
    (hshape : panValueFieldsHaveShapes context expected actual = true)
    (hlookup : lookupInfo name actual = some value) :
    ∃ shape, lookupInfo name expected = some shape ∧
      shape = panValueShape context value := by
  induction expected generalizing actual with
  | nil =>
      cases actual with
      | nil => simp [lookupInfo] at hlookup
      | cons entry actual => simp [panValueFieldsHaveShapes] at hshape
  | cons entry expected ih =>
      obtain ⟨expectedName, expectedShape⟩ := entry
      cases actual with
      | nil => simp [lookupInfo] at hlookup
      | cons actualEntry actual =>
          obtain ⟨actualName, actualValue⟩ := actualEntry
          have hparts :
              (((@BEq.beq FieldName instBEqOfDecidableEq expectedName actualName) = true) ∧
                panShapeMatches (panValueShape context actualValue) expectedShape = true) ∧
              panValueFieldsHaveShapes context expected actual = true := by
            simpa only [panValueFieldsHaveShapes, Bool.and_eq_true] using hshape
          have hnames : expectedName = actualName :=
            instLawfulBEqString.eq_of_beq hparts.1.1
          cases hhead : (@BEq.beq FieldName instBEqOfDecidableEq name actualName) with
          | true =>
              have hname : name = actualName := instLawfulBEqString.eq_of_beq hhead
              have hvalue : value = actualValue := by
                have hsome : some actualValue = some value := by
                  simpa [lookupInfo, hname.symm] using hlookup
                exact (Option.some.inj hsome).symm
              subst name
              subst expectedName
              subst value
              exact ⟨expectedShape, by simp [lookupInfo],
                (panValueShape_matches_eq context actualValue expectedShape hparts.1.2).symm⟩
          | false =>
              have hnameNe : actualName ≠ name := by
                intro hEq
                subst name
                simp at hhead
              have htail : lookupInfo name actual = some value := by
                simpa [lookupInfo, hnameNe] using hlookup
              obtain ⟨shape, hshapeLookup, hshapeEq⟩ := ih actual hparts.2 htail
              have hnameExpectedNe : expectedName ≠ name := by
                intro hEq
                apply hnameNe
                rw [← hnames]
                exact hEq
              refine ⟨shape, ?_, hshapeEq⟩
              simpa [lookupInfo, hnameExpectedNe] using hshapeLookup

private theorem structFindFieldIndex_lookupAligned [BEq String] [LawfulBEq String]
    (expected : List (FieldName × Shape)) (actual : List (FieldName × PanValue α))
    (field : FieldName) (value : PanValue α)
    (hnames : expected.map Prod.fst = actual.map Prod.fst)
    (hlookup : lookupInfo field actual = some value) :
    ∃ index, structFindFieldIndex field expected = some index ∧
      (actual[index]?).map Prod.snd = some value := by
  induction expected generalizing actual with
  | nil =>
      cases actual with
      | nil => simp [lookupInfo] at hlookup
      | cons entry actual => simp at hnames
  | cons entry expected ih =>
      obtain ⟨expectedName, expectedShape⟩ := entry
      cases actual with
      | nil => simp at hnames
      | cons actualEntry actual =>
          obtain ⟨actualName, actualValue⟩ := actualEntry
          simp only [List.map_cons, List.cons.injEq] at hnames
          rcases hnames with ⟨hname, htailNames⟩
          subst actualName
          cases hmatch : (expectedName == field) with
          | true =>
              have hfield : expectedName = field := LawfulBEq.eq_of_beq hmatch
              have hvalue : actualValue = value := by
                have hsome : some actualValue = some value := by
                  simpa [lookupInfo, hfield] using hlookup
                exact Option.some.inj hsome
              subst value
              refine ⟨0, ?_, ?_⟩
              · simp [structFindFieldIndex, hmatch]
              · simp
          | false =>
              have hfieldNe : field ≠ expectedName := by
                intro heq
                subst field
                simp at hmatch
              have htail : lookupInfo field actual = some value := by
                have hneq : ¬ expectedName = field := fun heq => hfieldNe heq.symm
                simpa [lookupInfo, hneq] using hlookup
              obtain ⟨index, hindex, hvalue⟩ := ih actual htailNames htail
              refine ⟨index + 1, ?_, ?_⟩
              · simp [structFindFieldIndex, hmatch, hindex]
              · simpa using hvalue

private theorem panStructFieldValuesFieldsOkBool_lookup [BEq String] [LawfulBEq String]
    (structs : StructContext) (fields : List (FieldName × PanValue α))
    (name : FieldName) (value : PanValue α)
    (hok : panStructFieldValuesFieldsOkBool structs fields = true)
    (hlookup : lookupPanValueField name fields = some value) :
    panStructValueFieldsOkBool structs value = true := by
  induction fields with
  | nil => simp [lookupPanValueField] at hlookup
  | cons entry fields ih =>
      rcases entry with ⟨field, fieldValue⟩
      have hparts : panStructValueFieldsOkBool structs fieldValue = true ∧
          panStructFieldValuesFieldsOkBool structs fields = true := by
        simpa only [panStructFieldValuesFieldsOkBool, Bool.and_eq_true] using hok
      by_cases hname : field = name
      · have hvalue : value = fieldValue := by
          have hsome : some fieldValue = some value := by
            simpa [lookupPanValueField, hname] using hlookup
          exact (Option.some.inj hsome).symm
        subst value
        exact hparts.1
      · apply ih hparts.2
        simpa [lookupPanValueField, hname] using hlookup

mutual
  private theorem panValueShape_eq_panSemShapeOf (context : StructContext)
      (value : PanValue α) :
      panValueShape context value = panSemShapeOf value := by
    cases value with
    | word value => rw [panValueShape.eq_1, panSemShapeOf.eq_1]
    | nStruct name fields => rw [panValueShape.eq_3, panSemShapeOf.eq_3]
    | rStruct values =>
        rw [panValueShape.eq_2, panSemShapeOf.eq_2]
        exact congrArg Shape.comb
          (panValueShapeList_eq_panSemShapeOf context values)

  private theorem panValueShapeList_eq_panSemShapeOf (context : StructContext)
      (values : List (PanValue α)) :
      values.map (panValueShape context) = values.map panSemShapeOf := by
    cases values with
    | nil => rfl
    | cons value values =>
        simp only [List.map_cons]
        rw [panValueShape_eq_panSemShapeOf, panValueShapeList_eq_panSemShapeOf]
end

mutual
private theorem panShapeMatches_self : ∀ shape, panShapeMatches shape shape = true
    | .one => by simp [panShapeMatches]
    | .named _ => by simp [panShapeMatches]
    | .comb shapes => by
        simp only [panShapeMatches]
        exact panShapeListMatches_self shapes

  private theorem panShapeListMatches_self :
      ∀ shapes, panShapeMatches.panShapeListMatches shapes shapes = true
    | [] => by simp [panShapeMatches.panShapeListMatches]
    | shape :: shapes => by
        simp [panShapeMatches.panShapeListMatches, panShapeMatches_self shape,
          panShapeListMatches_self shapes]
end

private theorem panValueFieldsHaveShapes_context_irrel
    (left right : StructContext) (expected : List (FieldName × Shape))
    (actual : List (FieldName × PanValue α)) :
    panValueFieldsHaveShapes left expected actual =
      panValueFieldsHaveShapes right expected actual := by
  induction expected generalizing actual with
  | nil => cases actual <;> rfl
  | cons expected expectedTail ih =>
      cases actual with
      | nil => rfl
      | cons actual actualTail =>
          simp only [panValueFieldsHaveShapes,
            panValueShape_eq_panSemShapeOf left actual.2,
            panValueShape_eq_panSemShapeOf right actual.2]
          exact congrArg _ (ih actualTail)

private theorem lookupInfo_append_eq_of_some_context
    (pfx context : StructContext) (key : String) (value : StructInfo)
    (hdisjoint : (pfx.map Prod.fst ++ context.map Prod.fst).Nodup)
    (hlookup : lookupInfo key context = some value) :
    lookupInfo key (pfx ++ context) = some value := by
  letI : LawfulBEq String := instLawfulBEqString
  letI : BEq String := instBEqOfDecidableEq
  induction pfx with
  | nil => exact hlookup
  | cons entry pfx ih =>
      obtain ⟨candidate, info⟩ := entry
      rcases List.nodup_cons.mp hdisjoint with ⟨hnot, htailNodup⟩
      have hkeyMem := lookupInfo_mem_of_some key context value hlookup
      have hcandidateNe : candidate ≠ key := by
        intro heq
        subst candidate
        exact hnot (List.mem_append_right _ hkeyMem)
      have hmatch : (candidate == key) = false := by
        cases hbeq : candidate == key with
        | false => rfl
        | true => exact False.elim (hcandidateNe (LawfulBEq.eq_of_beq hbeq))
      simp only [List.map_cons] at hdisjoint
      have hresult := ih htailNodup
      simpa [lookupInfo, hmatch] using hresult

private theorem panStructValueFieldsOkBool_append
    (pfx context : StructContext) (value : PanValue α)
    (hvalue : panStructValueFieldsOkBool context value = true)
    (hkeys : (pfx.map Prod.fst ++ context.map Prod.fst).Nodup) :
    panStructValueFieldsOkBool (pfx ++ context) value = true := by
  letI : LawfulBEq String := instLawfulBEqString
  letI : BEq String := instBEqOfDecidableEq
  revert hvalue hkeys pfx
  apply panStructValueFieldsOkBool.induct (α := α)
    (motive1 := fun value =>
      ∀ pfx, panStructValueFieldsOkBool context value = true →
        (pfx.map Prod.fst ++ context.map Prod.fst).Nodup →
          panStructValueFieldsOkBool (pfx ++ context) value = true)
    (motive2 := fun fields =>
      ∀ pfx, panStructFieldValuesFieldsOkBool context fields = true →
        (pfx.map Prod.fst ++ context.map Prod.fst).Nodup →
          panStructFieldValuesFieldsOkBool (pfx ++ context) fields = true)
    (motive3 := fun values =>
      ∀ pfx, panStructValuesFieldsOkBool context values = true →
        (pfx.map Prod.fst ++ context.map Prod.fst).Nodup →
          panStructValuesFieldsOkBool (pfx ++ context) values = true)
  · intro word pfx hvalue hkeys
    simp [panStructValueFieldsOkBool]
  · intro values ih pfx hvalue hkeys
    simpa [panStructValueFieldsOkBool] using ih pfx
      (by simpa [panStructValueFieldsOkBool] using hvalue) hkeys
  · intro name fields ih pfx hvalue hkeys
    simp only [panStructValueFieldsOkBool, Bool.and_eq_true] at hvalue ⊢
    cases hlookup : lookupInfo name context with
    | none => simp [hlookup] at hvalue
    | some info =>
        have hlookupExtended := lookupInfo_append_eq_of_some_context
          pfx context name info hkeys hlookup
        have hfields := ih pfx hvalue.1 hkeys
        have hshapeSame := panValueFieldsHaveShapes_context_irrel
          (pfx ++ context) context info.fields fields
        have hshape : panValueFieldsHaveShapes (pfx ++ context)
            info.fields fields = true := by
          rw [hshapeSame]
          simpa [hlookup] using hvalue.2
        simp only [hlookupExtended, hfields, hshape]
        constructor <;> trivial
  · intro pfx hvalue hkeys
    simp [panStructFieldValuesFieldsOkBool]
  · intro name value fields ihValue ihFields pfx hvalue hkeys
    simp only [panStructFieldValuesFieldsOkBool, Bool.and_eq_true] at hvalue ⊢
    exact ⟨ihValue pfx hvalue.1 hkeys, ihFields pfx hvalue.2 hkeys⟩
  · intro pfx hvalue hkeys
    simp [panStructValuesFieldsOkBool]
  · intro value values ihValue ihValues pfx hvalue hkeys
    simp only [panStructValuesFieldsOkBool, Bool.and_eq_true] at hvalue ⊢
    exact ⟨ihValue pfx hvalue.1 hkeys, ihValues pfx hvalue.2 hkeys⟩

private theorem lookupInfoWithRest_lookupInfo_for_load
    (name : String) (context : StructContext) (info : StructInfo)
    (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix)) :
    lookupInfo name context = some info := by
  letI : LawfulBEq String := instLawfulBEqString
  letI : BEq String := instBEqOfDecidableEq
  induction context with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      by_cases hmatch : candidate == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
        rcases hlookup with ⟨rfl, rfl⟩
        simp [lookupInfo, hmatch]
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        simpa [lookupInfo, hmatch] using ih hlookup

private theorem panValueFieldsHaveShapes_of_maps
    (context : StructContext) (expected : List (FieldName × Shape))
    (actual : List (FieldName × PanValue α))
    (hnames : expected.map Prod.fst = actual.map Prod.fst)
    (hshapes : actual.map (fun field => panSemShapeOf field.2) =
      expected.map Prod.snd) :
    panValueFieldsHaveShapes context expected actual = true := by
  induction expected generalizing actual with
  | nil =>
      cases actual with
      | nil => rfl
      | cons field actual => simp at hnames
  | cons expected expectedTail ih =>
      cases actual with
      | nil => simp at hnames
      | cons actual actualTail =>
          obtain ⟨expectedName, expectedShape⟩ := expected
          obtain ⟨actualName, actualValue⟩ := actual
          have hnames' :
              expectedName :: expectedTail.map Prod.fst =
                actualName :: actualTail.map Prod.fst := by
            simpa only [List.map_cons] using hnames
          rcases List.cons.inj hnames' with ⟨hname, htailNames⟩
          have hshapes' :
              panSemShapeOf actualValue ::
                  actualTail.map (fun field => panSemShapeOf field.2) =
                expectedShape :: expectedTail.map Prod.snd := by
            simpa only [List.map_cons] using hshapes
          rcases List.cons.inj hshapes' with ⟨hshape, htailShapes⟩
          have htail := ih actualTail htailNames htailShapes
          subst actualName
          simp only [panValueFieldsHaveShapes, Bool.and_eq_true]
          rw [panValueShape_eq_panSemShapeOf context actualValue, hshape]
          exact ⟨⟨by simp, panShapeMatches_self expectedShape⟩, htail⟩

private theorem panStructFieldValuesFieldsOkBool_append
    (pfx context : StructContext) (fields : List (FieldName × PanValue α))
    (hfields : panStructFieldValuesFieldsOkBool context fields = true)
    (hkeys : (pfx.map Prod.fst ++ context.map Prod.fst).Nodup) :
    panStructFieldValuesFieldsOkBool (pfx ++ context) fields = true := by
  induction fields with
  | nil => simp [panStructFieldValuesFieldsOkBool]
  | cons field fields ih =>
      cases field with
      | mk fieldName value =>
          simp only [panStructFieldValuesFieldsOkBool, Bool.and_eq_true] at hfields ⊢
          exact ⟨panStructValueFieldsOkBool_append pfx context value
            hfields.1 hkeys, ih hfields.2⟩

/-- A successful production load preserves the requested HOL shape and the
    field layout checked by `v_flds_ok`. This is an untagged production support
    theorem, not a HOL theorem port: its premise names the fuel-indexed Option
    loader and an arbitrary `readWord`, whereas HOL `mem_load` uses a
    finite-domain word-memory relation. It requires no extra in-bounds or
    value-validity premise; the successful load, well-formed shape, and
    `structInfosOk` context suffice. -/
theorem panValueFlatLoadFuel_shape_fields [BEq α] [Add α]
    (bytesInWord : α) (readWord : α → Option α) :
    ∀ (context : StructContext) (fuel : Nat) (shape : Shape) (address : α)
      (value : PanValue α),
      structInfosOk context →
      isWfShape context shape = true →
      panValueFlatLoadFuel context readWord bytesInWord fuel shape address = some value →
      panSemShapeOf value = shape ∧
        panStructValueFieldsOkBool context value = true := by
  letI : LawfulBEq String := instLawfulBEqString
  letI : BEq String := instBEqOfDecidableEq
  apply panValueFlatLoadFuel.induct (α := α) bytesInWord
    (motive1 := fun context fuel shape address =>
      ∀ value, structInfosOk context → isWfShape context shape = true →
        panValueFlatLoadFuel context readWord bytesInWord fuel shape address =
          some value →
        panSemShapeOf value = shape ∧ panStructValueFieldsOkBool context value = true)
    (motive2 := fun context fuel fields address =>
      ∀ values, structInfosOk context →
        isWfShape.isWfShapeList context (fields.map Prod.snd) = true →
        panValueFlatLoadFieldsFuel context readWord bytesInWord fuel fields address =
          some values →
        fields.map Prod.fst = values.map Prod.fst ∧
          values.map (fun field => panSemShapeOf field.2) = fields.map Prod.snd ∧
          panStructFieldValuesFieldsOkBool context values = true)
    (motive3 := fun context fuel shapes address =>
      ∀ values, structInfosOk context →
        isWfShape.isWfShapeList context shapes = true →
        panValueFlatLoadListFuel context readWord bytesInWord fuel shapes address =
          some values →
        values.map panSemShapeOf = shapes ∧
          panStructValuesFieldsOkBool context values = true)
  · intro context shape address value hok hwf hload
    simp only [panValueFlatLoadFuel] at hload
    cases hload
  · intro context fuel address value hok hwf hload
    cases hread : readWord address with
    | none => simp [panValueFlatLoadFuel, hread] at hload
    | some word =>
        have hvalue : PanValue.word word = value := by
          simpa [panValueFlatLoadFuel, hread] using hload
        cases hvalue
        simp [panSemShapeOf, panStructValueFieldsOkBool]
  · intro context fuel shapes address ih value hok hwf hload
    have hwfList : isWfShape.isWfShapeList context shapes = true := by
      simpa [isWfShape] using hwf
    cases hvalues : panValueFlatLoadListFuel context readWord bytesInWord fuel
        shapes address with
    | none => simp [panValueFlatLoadFuel, hvalues] at hload
    | some values =>
        have hvalue : PanValue.rStruct values = value := by
          simpa [panValueFlatLoadFuel, hvalues] using hload
        cases hvalue
        obtain ⟨hshapes, hfields⟩ := ih values hok hwfList hvalues
        constructor
        · simpa [panSemShapeOf] using congrArg Shape.comb hshapes
        · simpa [panStructValueFieldsOkBool] using hfields
  · intro context fuel name address ih value hok hwf hload
    cases hlookup : lookupInfoWithRest name context with
    | none =>
        simp [panValueFlatLoadFuel, hlookup] at hload
    | some entry =>
        obtain ⟨info, suffix⟩ := entry
        have hokSuffix := structInfosOk_suffix_for_load name context info suffix
          hlookup hok
        have hfieldsWf := lookupInfoWithRest_fields_wf_for_load
          name context info suffix hlookup hok
        cases hfields : panValueFlatLoadFieldsFuel suffix readWord bytesInWord fuel
            info.fields address with
        | none =>
            simp [panValueFlatLoadFuel, hlookup, hfields] at hload
        | some fields =>
            have hvalue : PanValue.nStruct name fields = value := by
              simpa [panValueFlatLoadFuel, hlookup, hfields] using hload
            cases hvalue
            obtain ⟨hnames, hshapes, hfieldsValid⟩ :=
              ih info suffix fields hokSuffix hfieldsWf hfields
            have hlookupInfo := lookupInfoWithRest_lookupInfo_for_load
              name context info suffix hlookup
            have hfieldShapes := panValueFieldsHaveShapes_of_maps context
              info.fields fields hnames hshapes
            obtain ⟨n, hdrop⟩ := lookupInfoWithRest_suffix_drop_for_load
              name context info suffix hlookup
            have hcontext : context = context.take n ++ suffix := by
              calc
                context = context.take n ++ context.drop n :=
                  (List.take_append_drop n context).symm
                _ = context.take n ++ suffix := by rw [hdrop]
            have hkeys :
                ((context.take n).map Prod.fst ++ suffix.map Prod.fst).Nodup := by
              have hkeysAll := hok.2.1
              rw [hcontext] at hkeysAll
              simpa only [List.map_append] using hkeysAll
            have hfieldsValidFull :
                panStructFieldValuesFieldsOkBool context fields = true := by
              have hvalid := panStructFieldValuesFieldsOkBool_append
                (context.take n) suffix fields hfieldsValid hkeys
              rw [hcontext]
              exact hvalid
            constructor
            · simp [panSemShapeOf]
            · simp [panStructValueFieldsOkBool, hlookupInfo, hfieldsValidFull,
                hfieldShapes]
  · intro context fuel address values hok hwf hload
    simp [panValueFlatLoadFieldsFuel] at hload
    subst values
    simp [panStructFieldValuesFieldsOkBool]
  · intro context head tail address values hok hwf hload
    simp [panValueFlatLoadFieldsFuel] at hload
  · intro context fuel field shape fields address ihHead ihTail values
      hok hwf hload
    simp only [List.map_cons, isWfShape.isWfShapeList, Bool.and_eq_true] at hwf
    cases hhead : panValueFlatLoadFuel context readWord bytesInWord fuel shape address with
    | none => simp [panValueFlatLoadFieldsFuel, hhead] at hload
    | some headValue =>
        let nextAddress := panValueFlatOffset bytesInWord address
          (shapeSizeWithContext context shape)
        cases htail : panValueFlatLoadFieldsFuel context readWord bytesInWord fuel
            fields nextAddress with
        | none => simp [panValueFlatLoadFieldsFuel, hhead, htail, nextAddress] at hload
        | some tailValues =>
            have hheadResult := ihHead headValue hok hwf.1 hhead
            have htailResult := ihTail tailValues hok hwf.2 htail
            have hvalues : values = (field, headValue) :: tailValues := by
              have hsome : some ((field, headValue) :: tailValues) = some values := by
                simpa [panValueFlatLoadFieldsFuel, hhead, htail, nextAddress] using hload
              exact (Option.some.inj hsome).symm
            subst values
            refine ⟨?_, ?_, ?_⟩
            · simp [htailResult.1]
            · simp [hheadResult.1, htailResult.2.1]
            · simp [panStructFieldValuesFieldsOkBool, hheadResult.2,
                htailResult.2.2]
  · intro context fuel address values hok hwf hload
    simp [panValueFlatLoadListFuel] at hload
    subst values
    simp [panStructValuesFieldsOkBool]
  · intro context head tail address values hok hwf hload
    simp [panValueFlatLoadListFuel] at hload
  · intro context fuel shape shapes address ihHead ihTail values hok hwf hload
    simp only [isWfShape.isWfShapeList, Bool.and_eq_true] at hwf
    cases hhead : panValueFlatLoadFuel context readWord bytesInWord fuel shape address with
    | none => simp [panValueFlatLoadListFuel, hhead] at hload
    | some headValue =>
        let nextAddress := panValueFlatOffset bytesInWord address
          (shapeSizeWithContext context shape)
        cases htail : panValueFlatLoadListFuel context readWord bytesInWord fuel
            shapes nextAddress with
        | none => simp [panValueFlatLoadListFuel, hhead, htail, nextAddress] at hload
        | some tailValues =>
            have hheadResult := ihHead headValue hok hwf.1 hhead
            have htailResult := ihTail tailValues hok hwf.2 htail
            have hvalues : values = headValue :: tailValues := by
              have hsome : some (headValue :: tailValues) = some values := by
                simpa [panValueFlatLoadListFuel, hhead, htail, nextAddress] using hload
              exact (Option.some.inj hsome).symm
            subst values
            constructor
            · simp [hheadResult.1, htailResult.1]
            · simp [panStructValuesFieldsOkBool, hheadResult.2, htailResult.2]

/-! ## Adapter between the HOL-shaped predicates and production struct contexts

These lemmas relate the exact HOL-shaped predicates over `StructContextHOL`
(`panValueFldsOk`, `panIsWfShapeValueHOL`, in their counterpart files) to the
production predicates over the cache-augmented `StructContext`
(`panStructValueFieldsOkBool`, `panIsWfShapeValueBool`). The context adapter is
the projection `StructContext.toHOL`, which drops the production-only
`shapedFields` cache and preserves first-match lookup shadowing. -/

/-- Boolean rearrangement used when comparing the pairwise production field
    check with the whole-list HOL shape/name equalities. -/
theorem boolAndRearr (left shape names shapes : Bool) :
    (left && shape && (names && shapes)) = ((left && names) && (shape && shapes)) := by
  cases left <;> cases shape <;> cases names <;> cases shapes <;> rfl

/-- String `==` is symmetric, used to reorient the pairwise field-name check
    against the HOL whole-list `MAP FST` equality. -/
theorem string_beq_comm (left right : String) :
    (left == right) = (right == left) := by
  by_cases h : left = right
  · rw [beq_iff_eq.mpr h, beq_iff_eq.mpr h.symm]
  · have h' : ¬ right = left := fun hba => h hba.symm
    rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

/- The production `panShapeMatches` agrees with the constructor-recursive
    `panStructShapeEqBool` under lawful String equality. -/
mutual
  theorem panShapeMatches_eq_panStructShapeEqBool [LawfulBEq String]
      (left right : Shape) :
      panShapeMatches left right = panStructShapeEqBool left right := by
    cases left with
    | one => cases right <;> simp [panShapeMatches, panStructShapeEqBool]
    | named leftName =>
        cases right with
        | one => simp [panShapeMatches, panStructShapeEqBool]
        | named rightName =>
            simp only [panShapeMatches, panStructShapeEqBool]
            by_cases h : leftName = rightName
            · rw [beq_iff_eq.mpr h, decide_eq_true h]
            · rw [beq_eq_false_iff_ne.mpr h, decide_eq_false h]
        | comb _ => simp [panShapeMatches, panStructShapeEqBool]
    | comb leftFields =>
        cases right with
        | one => simp [panShapeMatches, panStructShapeEqBool]
        | named _ => simp [panShapeMatches, panStructShapeEqBool]
        | comb rightFields =>
            simp only [panShapeMatches, panStructShapeEqBool]
            exact panShapeListMatches_eq_panStructShapeListEqBool leftFields rightFields

  theorem panShapeListMatches_eq_panStructShapeListEqBool [LawfulBEq String]
      (left right : List Shape) :
      panShapeMatches.panShapeListMatches left right = panStructShapeListEqBool left right := by
    cases left with
    | nil => cases right <;> simp [panShapeMatches.panShapeListMatches, panStructShapeListEqBool]
    | cons head tail =>
        cases right with
        | nil => simp [panShapeMatches.panShapeListMatches, panStructShapeListEqBool]
        | cons head' tail' =>
            simp only [panShapeMatches.panShapeListMatches, panStructShapeListEqBool]
            rw [panShapeMatches_eq_panStructShapeEqBool head head']
            exact congrArg (fun rest => panStructShapeEqBool head head' && rest)
              (panShapeListMatches_eq_panStructShapeListEqBool tail tail')
end

/-- The production pairwise `panValueFieldsHaveShapes` check is exactly HOL's
    whole-list `MAP FST flds = MAP FST info.fields /\
    MAP (shape_of o SND) flds = MAP SND info.fields` conjunction. -/
theorem panValueFieldsHaveShapes_eq [LawfulBEq String] (context : StructContext)
    (expected : List (FieldName × Shape)) (actual : List (FieldName × PanValue α)) :
    panValueFieldsHaveShapes context expected actual =
      ((actual.map Prod.fst == expected.map Prod.fst) &&
        panStructShapeListEqBool
          (actual.map (panSemShapeOf ∘ Prod.snd))
          (expected.map Prod.snd)) := by
  induction expected generalizing actual with
  | nil =>
      cases actual with
      | nil => simp [panValueFieldsHaveShapes, panStructShapeListEqBool]
      | cons head tail => simp [panValueFieldsHaveShapes]
  | cons expectedHead expectedTail ih =>
      obtain ⟨expectedName, expectedShape⟩ := expectedHead
      cases actual with
      | nil => simp [panValueFieldsHaveShapes]
      | cons actualHead actualTail =>
          obtain ⟨actualName, actualValue⟩ := actualHead
          simp only [panValueFieldsHaveShapes, List.map_cons,
            panStructShapeListEqBool, Function.comp_apply]
          rw [ih actualTail, panShapeMatches_eq_panStructShapeEqBool,
            panValueShape_eq_panSemShapeOf, string_beq_comm expectedName actualName]
          exact boolAndRearr (actualName == expectedName)
            (panStructShapeEqBool (panSemShapeOf actualValue) expectedShape)
            (actualTail.map Prod.fst == expectedTail.map Prod.fst)
            (panStructShapeListEqBool (actualTail.map (panSemShapeOf ∘ Prod.snd))
              (expectedTail.map Prod.snd))

/- Full clause-by-clause adapter for HOL `v_flds_ok_def`: the exact
    HOL-shaped `panValueFldsOk` over the projected context equals the
    production `panStructValueFieldsOkBool` over the cache-augmented context. -/
mutual
  theorem panValueFldsOk_toHOL [LawfulBEq String] (context : StructContext)
      (value : PanValue α) :
      panValueFldsOk context.toHOL value = panStructValueFieldsOkBool context value := by
    cases value with
    | word word => simp [panValueFldsOk, panStructValueFieldsOkBool]
    | rStruct values =>
        simp only [panValueFldsOk, panStructValueFieldsOkBool]
        exact panValuesFldsOk_toHOL context values
    | nStruct name fields =>
        simp only [panValueFldsOk, panStructValueFieldsOkBool, lookupInfo_toHOL]
        rw [panFieldsFldsOk_toHOL context fields]
        cases hlookup : lookupInfo name context with
        | none => simp
        | some info =>
            simp only [Option.map_some]
            rw [panValueFieldsHaveShapes_eq]

  theorem panValuesFldsOk_toHOL [LawfulBEq String] (context : StructContext)
      (values : List (PanValue α)) :
      panValuesFldsOk context.toHOL values = panStructValuesFieldsOkBool context values := by
    cases values with
    | nil => simp [panValuesFldsOk, panStructValuesFieldsOkBool]
    | cons value values =>
        simp only [panValuesFldsOk, panStructValuesFieldsOkBool]
        rw [panValueFldsOk_toHOL context value, panValuesFldsOk_toHOL context values]

  theorem panFieldsFldsOk_toHOL [LawfulBEq String] (context : StructContext)
      (fields : List (FieldName × PanValue α)) :
      panFieldsFldsOk context.toHOL fields = panStructFieldValuesFieldsOkBool context fields := by
    cases fields with
    | nil => simp [panFieldsFldsOk, panStructFieldValuesFieldsOkBool]
    | cons field fields =>
        obtain ⟨fieldName, value⟩ := field
        simp only [panFieldsFldsOk, panStructFieldValuesFieldsOkBool]
        rw [panValueFldsOk_toHOL context value, panFieldsFldsOk_toHOL context fields]
end


private theorem panStructRStructListShapeFields
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Sub α]
    [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α))
    (hinduction : PanStructAll (fun expression => ∀ subvalue,
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        expression = some subvalue →
      structOldExpShape context expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool structs subvalue = true) expressions)
    (values : List (PanValue α))
    (hvalues : evalPanValueExps structs locals globals memory baseAddress topAddress
      bytesInWord expressions = some values) :
    structOldExpShape.structOldExpShapes context expressions = values.map panSemShapeOf ∧
    panStructValuesFieldsOkBool structs values = true := by
  revert hinduction values hvalues
  induction expressions with
  | nil =>
      intro hinduction values hvalues
      cases hinduction
      simp [evalPanValueExps, evalPanValueExp.evalPanValueExps] at hvalues
      subst values
      exact ⟨by simp [structOldExpShape.structOldExpShapes],
        by simp [panStructValuesFieldsOkBool]⟩
  | cons expression expressions ih =>
      intro hinduction values hvalues
      cases hinduction with
      | cons ihHead ihTail =>
          simp only [evalPanValueExps, evalPanValueExp.evalPanValueExps] at hvalues
          cases hhead : evalPanValueExp structs locals globals memory
              baseAddress topAddress bytesInWord expression with
          | none => simp [hhead] at hvalues
          | some head =>
              cases htail : evalPanValueExp.evalPanValueExps structs locals globals memory
                  baseAddress topAddress bytesInWord expressions with
              | none => simp [hhead, htail] at hvalues
              | some tail =>
                  have hvaluesEq : head :: tail = values := by
                    simpa [hhead, htail] using hvalues
                  subst values
                  have hheadFacts := ihHead head hhead
                  have htailFacts := ih ihTail tail
                    (by simpa [evalPanValueExps] using htail)
                  exact ⟨by simp [structOldExpShape.structOldExpShapes,
                    hheadFacts.1, htailFacts.1], by
                    simp [panStructValuesFieldsOkBool, hheadFacts.2, htailFacts.2]⟩

private theorem panStructRStructListShapeFieldsFull
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Sub α]
    [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (memoryAccess : PanValueMemoryAccess α) (expressions : List (Exp α))
    (hinduction : PanStructAll (fun expression => ∀ subvalue,
      evalPanValueExpFull structs locals globals memory baseAddress topAddress
        bytesInWord expression (memoryAccess := some memoryAccess) = some subvalue →
      structOldExpShape context expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool structs subvalue = true) expressions)
    (values : List (PanValue α))
    (hvalues : evalPanValueExpsFull structs locals globals memory baseAddress topAddress
      bytesInWord expressions (memoryAccess := some memoryAccess) = some values) :
    structOldExpShape.structOldExpShapes context expressions = values.map panSemShapeOf ∧
    panStructValuesFieldsOkBool structs values = true := by
  revert hinduction values hvalues
  induction expressions with
  | nil =>
      intro hinduction values hvalues
      cases hinduction
      simp [evalPanValueExpsFull] at hvalues
      subst values
      exact ⟨by simp [structOldExpShape.structOldExpShapes],
        by simp [panStructValuesFieldsOkBool]⟩
  | cons expression expressions ih =>
      intro hinduction values hvalues
      cases hinduction with
      | cons ihHead ihTail =>
          simp only [evalPanValueExpsFull] at hvalues
          cases hhead : evalPanValueExpFull structs locals globals memory
              baseAddress topAddress bytesInWord expression
              (memoryAccess := some memoryAccess) with
          | none => simp [hhead] at hvalues
          | some head =>
              cases htail : evalPanValueExpsFull structs locals globals memory
                  baseAddress topAddress bytesInWord expressions
                  (memoryAccess := some memoryAccess) with
              | none => simp [hhead, htail] at hvalues
              | some tail =>
                  have hvaluesEq : head :: tail = values := by
                    simpa [hhead, htail] using hvalues
                  subst values
                  have hheadFacts := ihHead head hhead
                  have htailFacts := ih ihTail tail htail
                  exact ⟨by simp [structOldExpShape.structOldExpShapes,
                    hheadFacts.1, htailFacts.1], by
                    simp [panStructValuesFieldsOkBool, hheadFacts.2, htailFacts.2]⟩

/-- Derived RStruct induction case for HOL `compile_exp_correct`.
    The input contains one recursive hypothesis per field, matching the HOL
    induction step, and retains its context, finite-map, field-validity, and
    struct-info premises. Source evaluation, recursive IHs, and converted
    execution share one explicit state-derived memory adapter through the full
    evaluator. This remains untagged: HOL has only the universal theorem and
    Lean uses total-lookup/Bool adapters plus explicit bytesInWord, memory, and
    full-evaluator operation dictionaries. -/
theorem panStructCompileExpCorrectRStructCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (expressions : List (Exp α)) (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord
      (.rStruct expressions) (memoryAccess := some memoryAccess) = some value)
    (hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (hstructInfos : structInfosOk state.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinduction : PanStructAll (fun expression => ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := some memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue subvalue))
      expressions) :
    structOldExpShape context (.rStruct expressions) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.rStruct expressions))
      (memoryAccess := some memoryAccess) =
        some (panStructConvertValue value) := by
  have hfieldsIH : PanStructAll (fun expression => ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := some memoryAccess) = some subvalue →
      structOldExpShape context expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true) expressions := by
    exact panStructAll_map (fun expression hind => fun subvalue hevalSub =>
      let hcase := hind subvalue hevalSub hstructs hlocalsFields hglobalsFields
        hstructInfos hlocalsMap hglobalsMap
      ⟨hcase.1, hcase.2.1⟩) hinduction
  have hinductionAt : ∀ expression, expression ∈ expressions → ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := some memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue subvalue) := by
    intro expression hmem
    exact panStructAll_mem hinduction expression hmem
  cases hvalues : evalPanValueExpsFull state.structs state.locals
      state.globals state.memory state.baseAddress state.topAddress bytesInWord expressions
      (memoryAccess := some memoryAccess) with
  | none => simp [evalPanValueExpFull, hvalues] at heval
  | some values =>
      have hvalue : PanValue.rStruct values = value := by
        simpa [evalPanValueExpFull, hvalues] using heval
      cases hvalue
      have hsourceValues : evalPanValueExpsFull state.structs state.locals state.globals
          state.memory state.baseAddress state.topAddress bytesInWord expressions
          (memoryAccess := some memoryAccess) = some values := hvalues
      have hshapeFields := panStructRStructListShapeFieldsFull context state.structs
        state.locals state.globals state.memory state.baseAddress state.topAddress
        bytesInWord memoryAccess expressions hfieldsIH values hsourceValues
      have hpointwise : ∀ expression, expression ∈ expressions → ∀ subvalue,
          evalPanValueExpFull state.structs state.locals state.globals state.memory
            state.baseAddress state.topAddress bytesInWord expression
            (memoryAccess := some memoryAccess) = some subvalue →
          evalPanValueExpFull (panStructConvertState context state).structs
            (panStructConvertState context state).locals
            (panStructConvertState context state).globals
            (panStructConvertState context state).memory
            (panStructConvertState context state).baseAddress
            (panStructConvertState context state).topAddress bytesInWord
            (structCompileExp context expression) (memoryAccess := some memoryAccess) =
              some (panStructConvertValue subvalue) := by
        intro expression hmem subvalue hevalSub
        exact (hinductionAt expression hmem subvalue hevalSub
          hstructs hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap).2.2
      have htargetList := panStructCompileExpsFullEvalOfPointwiseCorrect
        context state bytesInWord memoryAccess expressions values hsourceValues hpointwise
      have hconvertValues := panStructConvertValues_eq_map values
      refine ⟨?_, ?_, ?_⟩
      · have hshapeMap : expressions.map (structOldExpShape context) =
            values.map panSemShapeOf := by
          simpa only [structOldExpShapes_eq_map] using hshapeFields.1
        simpa only [structOldExpShape, panSemShapeOf,
          structOldExpShapes_eq_map] using congrArg Shape.comb hshapeMap
      · simpa [panStructValueFieldsOkBool] using hshapeFields.2
      · simpa [evalPanValueExpFull, structCompileExp, panStructConvertState,
          panStructConvertValue, hconvertValues, htargetList]

private theorem lookupInfo_mapValuesNStruct [BEq String] (entries : InfoMap α)
    (name : String) (convert : α → β) :
    lookupInfo name (entries.map fun (key, value) => (key, convert value)) =
      (lookupInfo name entries).map convert := by
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      by_cases hkey : key == name
      · simp [lookupInfo, hkey]
      · simp [lookupInfo, hkey, ih]

private theorem lookupInfoDefaultPanPropsNStruct
    {β : Type} (key : String) (entries : List (String × β)) :
    @lookupInfo String β instBEqOfDecidableEq key entries =
      panPropsALookupEq key entries := by
  letI : LawfulBEq String := instLawfulBEqString
  exact lookupInfo_eq_panPropsALookupEq key entries

private theorem evalPanValueFieldsFull_projection
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (memoryAccess : PanValueMemoryAccess α)
    (fields : List (FieldName × Exp α)) (values : List (FieldName × PanValue α))
    (heval : evalPanValueFieldsFull structs locals globals memory baseAddress topAddress
      bytesInWord fields (memoryAccess := some memoryAccess) = some values) :
    evalPanValueExpsFull structs locals globals memory baseAddress topAddress bytesInWord
      (fields.map Prod.snd) (memoryAccess := some memoryAccess) =
        some (values.map Prod.snd) := by
  induction fields generalizing values with
  | nil =>
      simp [evalPanValueFieldsFull] at heval
      subst values
      simp [evalPanValueExpsFull]
  | cons field fields ih =>
      rcases field with ⟨fieldName, expression⟩
      simp only [evalPanValueFieldsFull] at heval
      cases hhead : evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord expression
          (memoryAccess := some memoryAccess) with
      | none => simp [hhead] at heval
      | some head =>
          cases htail : evalPanValueFieldsFull structs locals globals memory
              baseAddress topAddress bytesInWord fields
              (memoryAccess := some memoryAccess) with
          | none => simp [hhead, htail] at heval
          | some tail =>
              have hvalues : (fieldName, head) :: tail = values := by
                simpa [hhead, htail] using heval
              subst values
              simp only [List.map_cons, evalPanValueExpsFull, hhead]
              rw [ih tail htail]
              simp

private theorem evalPanValueFieldsFull_names
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (memoryAccess : PanValueMemoryAccess α)
    (fields : List (FieldName × Exp α)) (values : List (FieldName × PanValue α))
    (heval : evalPanValueFieldsFull structs locals globals memory baseAddress topAddress
      bytesInWord fields (memoryAccess := some memoryAccess) = some values) :
    values.map Prod.fst = fields.map Prod.fst := by
  induction fields generalizing values with
  | nil =>
      simp [evalPanValueFieldsFull] at heval
      subst values
      simp
  | cons field fields ih =>
      rcases field with ⟨fieldName, expression⟩
      simp only [evalPanValueFieldsFull] at heval
      cases hhead : evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord expression
          (memoryAccess := some memoryAccess) with
      | none => simp [hhead] at heval
      | some head =>
          cases htail : evalPanValueFieldsFull structs locals globals memory
              baseAddress topAddress bytesInWord fields
              (memoryAccess := some memoryAccess) with
          | none => simp [hhead, htail] at heval
          | some tail =>
              have hvalues : (fieldName, head) :: tail = values := by
                simpa [hhead, htail] using heval
              subst values
              simp only [List.map_cons]
              rw [ih (values := tail) htail]

/-- Derived NStruct-constructor case of HOL `compile_exp_correct`, with all
    three case conclusions and a recursive hypothesis for every field
    expression. Source, recursive field IHs, and converted execution use the
    full evaluator with one explicit memory adapter. It remains untagged:
    HOL has one universally quantified theorem, not a separate NStruct
    declaration, and this Lean statement is translated rather than exact.
    Lean replaces direct context equality with projected shape-view equality,
    HOL finite-map FEVERY validity with pointwise Bool predicates over total
    lookups, and FMAP_MAP2 equations with pointwise shape-map adapters.
    `structInfosOk` is retained and used to establish declared-field
    uniqueness. HOL also uses a fixed-width evaluator and state-owned finite
    maps, while Lean takes explicit `bytesInWord`, `PanValueMemoryAccess`, and
    full-evaluator operation dictionaries. -/
theorem panStructCompileExpCorrectNStructCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (name : StructName) (fields : List (FieldName × Exp α))
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord (.nStruct name fields)
      (memoryAccess := some memoryAccess) = some value)
    (hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (hstructInfos : structInfosOk state.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinduction : PanStructAll (fun expression => ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := some memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue subvalue))
      (fields.map Prod.snd)) :
    structOldExpShape context (.nStruct name fields) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.nStruct name fields))
      (memoryAccess := some memoryAccess) =
        some (panStructConvertValue value) := by
  cases hlookup : @lookupInfo String StructInfo instBEqOfDecidableEq
      name state.structs with
  | none =>
      simp [evalPanValueExpFull, hlookup] at heval
  | some info =>
      cases hfieldEval : evalPanValueFieldsFull state.structs
          state.locals state.globals state.memory state.baseAddress state.topAddress
          bytesInWord fields (memoryAccess := some memoryAccess) with
      | none =>
          simp [evalPanValueExpFull, hlookup, hfieldEval] at heval
      | some fieldValues =>
          by_cases hshapesExact : panValueFieldsExactHOL state.structs info.fields
              fieldValues = true
          · have hshapes : panValueFieldsHaveShapes state.structs info.fields
                fieldValues = true := by
              simpa [panValueFieldsExactHOL_eq_haveShapes] using hshapesExact
            have hvalue : value = .nStruct name fieldValues := by
              simp [evalPanValueExpFull, hlookup, hfieldEval, hshapesExact] at heval
              exact heval.symm
            subst value
            have hlookupLocal : lookupInfo name state.structs = some info := by
              rw [lookupInfo_eq_panPropsALookupEq]
              rw [← lookupInfoDefaultPanPropsNStruct, hlookup]
            have hcontextFieldsMap :
                (lookupInfo name context.structs).map (fun info => info.fields) =
                  some info.fields := by
              calc
                (lookupInfo name context.structs).map (fun info => info.fields) =
                    lookupInfo name (panStructContextShapeView context.structs) := by
                  symm
                  simpa only [panStructContextShapeView] using
                    (lookupInfo_mapValuesNStruct context.structs name fun info => info.fields)
                _ = lookupInfo name (panStructContextShapeView state.structs) := by
                  rw [hstructs]
                _ = (lookupInfo name state.structs).map (fun info => info.fields) := by
                  simpa only [panStructContextShapeView] using
                    (lookupInfo_mapValuesNStruct state.structs name fun info => info.fields)
                _ = some info.fields := by simp [hlookupLocal]
            have hcontextInfoExists : ∃ contextInfo,
                lookupInfo name context.structs = some contextInfo ∧
                contextInfo.fields = info.fields := by
              cases hcontextInfo : lookupInfo name context.structs with
              | none => simp [hcontextInfo] at hcontextFieldsMap
              | some contextInfo =>
                  exact ⟨contextInfo, rfl,
                    by simpa [hcontextInfo] using hcontextFieldsMap⟩
            obtain ⟨contextInfo, hcontextInfo, hcontextInfoFields⟩ := hcontextInfoExists
            have hsourceValues : evalPanValueExpsFull state.structs state.locals
                state.globals state.memory state.baseAddress state.topAddress bytesInWord
                (fields.map Prod.snd) (memoryAccess := some memoryAccess) =
                some (fieldValues.map Prod.snd) :=
              evalPanValueFieldsFull_projection state.structs state.locals state.globals
                state.memory state.baseAddress state.topAddress bytesInWord memoryAccess
                fields fieldValues hfieldEval
            have hfieldIH : PanStructAll (fun expression => ∀ subvalue,
                evalPanValueExpFull state.structs state.locals state.globals state.memory
                  state.baseAddress state.topAddress bytesInWord expression
                  (memoryAccess := some memoryAccess) = some subvalue →
                structOldExpShape context expression = panSemShapeOf subvalue ∧
                panStructValueFieldsOkBool state.structs subvalue = true)
                (fields.map Prod.snd) := by
              exact panStructAll_map (fun expression ih => fun subvalue hevalSub =>
                let hcase := ih subvalue hevalSub hstructs hlocalsFields hglobalsFields
                  hstructInfos hlocalsMap hglobalsMap
                ⟨hcase.1, hcase.2.1⟩) hinduction
            have hfieldFacts := panStructRStructListShapeFieldsFull context state.structs
              state.locals state.globals state.memory state.baseAddress state.topAddress
              bytesInWord memoryAccess (fields.map Prod.snd) hfieldIH
              (fieldValues.map Prod.snd)
              hsourceValues
            have hrecursive : panStructFieldValuesFieldsOkBool state.structs fieldValues = true := by
              have hrec : ∀ values : List (FieldName × PanValue α),
                  panStructValuesFieldsOkBool state.structs (values.map Prod.snd) = true →
                  panStructFieldValuesFieldsOkBool state.structs values = true := by
                intro values
                induction values with
                | nil => intro _; simp [panStructFieldValuesFieldsOkBool]
                | cons field values ih =>
                    cases field with
                    | mk fname fvalue =>
                        intro hvalues
                        simp only [List.map_cons, panStructValuesFieldsOkBool,
                          Bool.and_eq_true] at hvalues
                        simp only [panStructFieldValuesFieldsOkBool, Bool.and_eq_true]
                        exact ⟨hvalues.1, ih hvalues.2⟩
              exact hrec fieldValues hfieldFacts.2
            have hfieldsValid : panStructValueFieldsOkBool state.structs
                (.nStruct name fieldValues) = true := by
              have hlookupDefault :
                  @lookupInfo String StructInfo instBEqOfDecidableEq name state.structs =
                    some info := hlookup
              simp [panStructValueFieldsOkBool, hlookupDefault, hrecursive, hshapes]
            have hfieldNames := panValueFieldsHaveShapesNames state.structs
              info.fields fieldValues hshapes
            have hfieldNamesExprs : info.fields.map Prod.fst = fields.map Prod.fst := by
              calc
                info.fields.map Prod.fst = fieldValues.map Prod.fst := hfieldNames
                _ = fields.map Prod.fst := evalPanValueFieldsFull_names
                  state.structs state.locals state.globals state.memory
                  state.baseAddress state.topAddress bytesInWord memoryAccess
                  fields fieldValues hfieldEval
            have hfieldsNodup := lookupInfo_fields_nodup name state.structs info
              hlookupLocal hstructInfos
            have hcontextNodup : (contextInfo.fields.map Prod.fst).Nodup := by
              simpa [hcontextInfoFields] using hfieldsNodup
            have hcompiledFields := fieldsInOrderReorderNoop context fields
              contextInfo.fields (by simpa [hcontextInfoFields] using hfieldNamesExprs)
              hcontextNodup
            have hcompiledFields' := hcompiledFields
            rw [hcontextInfoFields] at hcompiledFields'
            have hpointwise : ∀ expression, expression ∈ fields.map Prod.snd → ∀ subvalue,
                evalPanValueExpFull state.structs state.locals state.globals state.memory
                  state.baseAddress state.topAddress bytesInWord expression
                  (memoryAccess := some memoryAccess) = some subvalue →
                evalPanValueExpFull (panStructConvertState context state).structs
                  (panStructConvertState context state).locals
                  (panStructConvertState context state).globals
                  (panStructConvertState context state).memory
                  (panStructConvertState context state).baseAddress
                  (panStructConvertState context state).topAddress bytesInWord
                  (structCompileExp context expression)
                  (memoryAccess := some memoryAccess) =
                    some (panStructConvertValue subvalue) := by
              intro expression hmem subvalue hevalSub
              exact (panStructAll_mem hinduction expression hmem subvalue hevalSub
                hstructs hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap).2.2
            have htargetList := panStructCompileExpsFullEvalOfPointwiseCorrect
              context state bytesInWord memoryAccess
              (fields.map Prod.snd) (fieldValues.map Prod.snd)
              hsourceValues hpointwise
            have hconvertFields := panStructConvertFieldValues_eq_map fieldValues
            have htargetListLocal :
                evalPanValueExpsFull
                  (panStructConvertState context state).structs
                  (panStructConvertState context state).locals
                  (panStructConvertState context state).globals
                  (panStructConvertState context state).memory
                  (panStructConvertState context state).baseAddress
                  (panStructConvertState context state).topAddress bytesInWord
                  (structCompileExp.structCompileExps context (fields.map Prod.snd))
                  (memoryAccess := some memoryAccess) =
                some ((fieldValues.map Prod.snd).map panStructConvertValue) := by
              exact htargetList
            have hcompileMap : structCompileExp.structCompileExps context
                (fields.map Prod.snd) =
                fields.map (fun field => structCompileExp context field.2) := by
              rw [structCompileExps_eq_map]
              simp [List.map_map]
            rw [hcompileMap] at htargetListLocal
            refine ⟨?_, hfieldsValid, ?_⟩
            · simp [structOldExpShape, panSemShapeOf]
            · simp only [structCompileExp, hcontextInfo, hcontextInfoFields,
                evalPanValueExpFull, panStructConvertState]
              rw [hcompiledFields']
              simpa [panStructConvertState, panStructConvertValue,
                panStructConvertFieldValues_eq_map, structCompileExp.structCompileExps]
                using htargetListLocal
          · simp [evalPanValueExpFull, hlookup, hfieldEval, hshapesExact] at heval

/-- Derived NField-constructor case of HOL `compile_exp_correct`. The
    recursive hypothesis for the receiver carries the translated context,
    finite-map, field-validity, and struct-info premises and all three
    conclusions. Source and converted execution use `evalPanValueExpFull` with
    the same memory-access model. Field lookup is connected to the production
    compiler's `structFindFieldIndex` by preserving the declared and runtime
    field order. This specialization is intentionally untagged: HOL has one
    universal theorem, while Lean uses projected struct-shape equality, Bool
    validity over total lookups, and explicit `bytesInWord` and optional
    `PanValueMemoryAccess` parameters. The full evaluator's shift-semantics
    dictionaries are Lean runtime parameters, not HOL logical premises. The
    `structInfosOk` premise is retained but unused in this case. -/
theorem panStructCompileExpCorrectNFieldCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : Option (PanValueMemoryAccess α))
    (field : FieldName) (expression : Exp α)
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord (.nField field expression)
      (memoryAccess := memoryAccess) = some value)
    (hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (hstructInfos : structInfosOk state.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinduction : ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression) (memoryAccess := memoryAccess) =
          some (panStructConvertValue subvalue)) :
    structOldExpShape context (.nField field expression) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.nField field expression))
      (memoryAccess := memoryAccess) =
        some (panStructConvertValue value) := by
  cases hchild : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord expression
      (memoryAccess := memoryAccess) with
  | none => simp [evalPanValueExpFull, hchild] at heval
  | some childValue =>
      cases childValue with
      | word word => simp [evalPanValueExpFull, hchild] at heval
      | rStruct values => simp [evalPanValueExpFull, hchild] at heval
      | nStruct structName fields =>
          cases hlookupStruct : @lookupInfo String StructInfo instBEqOfDecidableEq
              structName state.structs with
          | none => simp [evalPanValueExpFull, hchild, hlookupStruct] at heval
          | some info =>
              cases hfield : lookupPanValueField field fields with
              | none => simp [evalPanValueExpFull, hchild, hlookupStruct, hfield] at heval
              | some fieldValue =>
                  have hvalue : value = fieldValue := by
                    have hval : fieldValue = value := by
                      simp [evalPanValueExpFull, hchild, hlookupStruct, hfield] at heval
                      exact heval
                    exact hval.symm
                  subst value
                  have hchildIH := hinduction (.nStruct structName fields) hchild
                    hstructs hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap
                  have hvalidParts :
                      panStructFieldValuesFieldsOkBool state.structs fields = true ∧
                      panValueFieldsHaveShapes state.structs info.fields fields = true := by
                    have hvalid := hchildIH.2.1
                    simp only [panStructValueFieldsOkBool] at hvalid
                    rw [hlookupStruct] at hvalid
                    simp only [Bool.and_eq_true] at hvalid
                    exact hvalid
                  have hfieldValid := panStructFieldValuesFieldsOkBool_lookup
                    state.structs fields field fieldValue hvalidParts.1 hfield
                  have hfieldLookup : lookupInfo field fields = some fieldValue := by
                    rw [← lookupPanValueField_eq_lookupInfo field fields]
                    exact hfield
                  obtain ⟨fieldShape, hfieldShapeLookup, hfieldShapeEq⟩ :=
                    panValueFieldsHaveShapes_lookup state.structs info.fields fields
                      field fieldValue hvalidParts.2 hfieldLookup
                  have hfieldNames := panValueFieldsHaveShapesNames state.structs
                    info.fields fields hvalidParts.2
                  have hindexData := structFindFieldIndex_lookupAligned
                    info.fields fields field fieldValue hfieldNames hfieldLookup
                  have hlookupLocal : lookupInfo structName state.structs = some info := by
                    rw [lookupInfo_eq_panPropsALookupEq]
                    rw [← lookupInfoDefaultPanPropsNStruct, hlookupStruct]
                  have hcontextFieldsMap :
                      (lookupInfo structName context.structs).map (fun entry => entry.fields) =
                        some info.fields := by
                    calc
                      (lookupInfo structName context.structs).map (fun entry => entry.fields) =
                          lookupInfo structName (panStructContextShapeView context.structs) := by
                        symm
                        simpa only [panStructContextShapeView] using
                          (lookupInfo_mapValuesNStruct context.structs structName
                            fun entry => entry.fields)
                      _ = lookupInfo structName (panStructContextShapeView state.structs) := by
                        rw [hstructs]
                      _ = (lookupInfo structName state.structs).map (fun entry => entry.fields) := by
                        simpa only [panStructContextShapeView] using
                          (lookupInfo_mapValuesNStruct state.structs structName
                            fun entry => entry.fields)
                      _ = some info.fields := by simp [hlookupLocal]
                  have hcontextInfoExists : ∃ contextInfo,
                      lookupInfo structName context.structs = some contextInfo ∧
                      contextInfo.fields = info.fields := by
                    cases hcontextInfo : lookupInfo structName context.structs with
                    | none => simp [hcontextInfo] at hcontextFieldsMap
                    | some contextInfo =>
                        exact ⟨contextInfo, rfl,
                          by simpa [hcontextInfo] using hcontextFieldsMap⟩
                  obtain ⟨contextInfo, hcontextInfo, hcontextInfoFields⟩ :=
                    hcontextInfoExists
                  have hcontextInfoDefault :
                      @lookupInfo String StructInfo instBEqOfDecidableEq
                        structName context.structs = some contextInfo := by
                    rw [lookupInfoDefaultPanPropsNStruct]
                    rw [lookupInfo_eq_panPropsALookupEq] at hcontextInfo
                    exact hcontextInfo
                  have hfieldShapeContext :
                      lookupInfo field contextInfo.fields = some fieldShape := by
                    simpa [hcontextInfoFields] using hfieldShapeLookup
                  have hfieldShapeContextDefault :
                      @lookupInfo FieldName Shape instBEqOfDecidableEq
                        field contextInfo.fields = some fieldShape := by
                    rw [lookupInfoDefaultPanPropsNStruct]
                    rw [lookupInfo_eq_panPropsALookupEq] at hfieldShapeContext
                    exact hfieldShapeContext
                  have hfieldShapeSem : fieldShape = panSemShapeOf fieldValue := by
                    calc
                      fieldShape = panValueShape state.structs fieldValue := hfieldShapeEq
                      _ = panSemShapeOf fieldValue :=
                        panValueShape_eq_panSemShapeOf state.structs fieldValue
                  have hchildShape :
                      structOldExpShape context expression = .named structName := by
                    simpa [panSemShapeOf] using hchildIH.1
                  have hshape :
                    structOldExpShape context (.nField field expression) =
                        panSemShapeOf fieldValue := by
                    simpa only [structOldExpShape, hchildShape, hcontextInfoDefault,
                      hfieldShapeContextDefault] using hfieldShapeSem
                  have hcompiledChild :
                      evalPanValueExpFull (panStructConvertState context state).structs
                        (panStructConvertState context state).locals
                        (panStructConvertState context state).globals
                        (panStructConvertState context state).memory
                        (panStructConvertState context state).baseAddress
                        (panStructConvertState context state).topAddress bytesInWord
                        (structCompileExp context expression)
                        (memoryAccess := memoryAccess) =
                        some (.rStruct
                          (fields.map (panStructConvertValue ∘ Prod.snd))) := by
                    simpa [panStructConvertValue, panStructConvertFieldValues_eq_map] using
                      hchildIH.2.2
                  obtain ⟨index, hindex, hselected⟩ := hindexData
                  have hselectedConverted :
                      (fields.map (panStructConvertValue ∘ Prod.snd))[index]? =
                        some (panStructConvertValue fieldValue) := by
                    have hmap := congrArg (Option.map panStructConvertValue) hselected
                    simpa [List.getElem?_map] using hmap
                  have hcontextIndex :
                      structFindFieldIndex field contextInfo.fields = some index := by
                    simpa [hcontextInfoFields] using hindex
                  have hcompile :
                      structCompileExp context (.nField field expression) =
                        .rField index (structCompileExp context expression) := by
                    simp [structCompileExp, hchildShape, hcontextInfo, hcontextIndex]
                  have htarget :
                      evalPanValueExpFull (panStructConvertState context state).structs
                        (panStructConvertState context state).locals
                        (panStructConvertState context state).globals
                        (panStructConvertState context state).memory
                        (panStructConvertState context state).baseAddress
                        (panStructConvertState context state).topAddress bytesInWord
                        (structCompileExp context (.nField field expression))
                        (memoryAccess := memoryAccess) =
                        some (panStructConvertValue fieldValue) := by
                    rw [hcompile]
                    simp only [evalPanValueExpFull, hcompiledChild]
                    exact hselectedConverted
                  exact ⟨hshape, hfieldValid, htarget⟩

private theorem panStructValuesFieldsOkBool_getElem?
    (structs : StructContext) (values : List (PanValue α)) (index : Nat)
    (value : PanValue α)
    (hok : panStructValuesFieldsOkBool structs values = true)
    (hget : values[index]? = some value) :
    panStructValueFieldsOkBool structs value = true := by
  induction values generalizing index with
  | nil => simp at hget
  | cons head tail ih =>
      cases index with
      | zero =>
          have hparts : panStructValueFieldsOkBool structs head = true ∧
              panStructValuesFieldsOkBool structs tail = true := by
            simpa only [panStructValuesFieldsOkBool, Bool.and_eq_true] using hok
          have hhead : panStructValueFieldsOkBool structs head = true := by
            exact hparts.1
          have hvalue : value = head := by
            simpa using hget.symm
          subst value
          exact hhead
      | succ index =>
          have htail : panStructValueFieldsOkBool structs head = true ∧
              panStructValuesFieldsOkBool structs tail = true := by
            simpa only [panStructValuesFieldsOkBool, Bool.and_eq_true] using hok
          apply ih index htail.2
          simpa using hget

/-- Derived RField-constructor case of HOL `compile_exp_correct`. The
    recursive hypothesis for the receiver carries the translated context,
    finite-map, field-validity, and struct-info premises and all three
    conclusions. Successful source evaluation provides the index lookup needed
    both for the result shape and validity; no separate in-bounds premise is
    added. Source and converted evaluation use `evalPanValueExpFull` with the
    same explicit memory-access model. This specialization is intentionally
    untagged: HOL has only the universal theorem, while Lean uses projected
    struct-shape equality, Bool validity over total lookups, and explicit
    `bytesInWord` and optional `PanValueMemoryAccess` parameters. The full
    evaluator also requires shift-semantics dictionaries as Lean runtime
    parameters rather than logical HOL premises. The
    `structInfosOk` premise is retained but unused in this case. -/
theorem panStructCompileExpCorrectRFieldCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : Option (PanValueMemoryAccess α))
    (index : Nat) (expression : Exp α)
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord (.rField index expression)
      (memoryAccess := memoryAccess) = some value)
    (hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (hstructInfos : structInfosOk state.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinduction : ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression) (memoryAccess := memoryAccess) =
          some (panStructConvertValue subvalue)) :
    structOldExpShape context (.rField index expression) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.rField index expression))
      (memoryAccess := memoryAccess) =
        some (panStructConvertValue value) := by
  cases hchild : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord expression
      (memoryAccess := memoryAccess) with
  | none => simp [evalPanValueExpFull, hchild] at heval
  | some childValue =>
      cases childValue with
      | word word => simp [evalPanValueExpFull, hchild] at heval
      | nStruct name fields => simp [evalPanValueExpFull, hchild] at heval
      | rStruct values =>
          cases hselected : values[index]? with
          | none => simp [evalPanValueExpFull, hchild, hselected] at heval
          | some selected =>
              have hvalue : value = selected := by
                have hval : selected = value := by
                  simp [evalPanValueExpFull, hchild, hselected] at heval
                  exact heval
                exact hval.symm
              subst value
              have hchildIH := hinduction (.rStruct values) hchild
                hstructs hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap
              have hvaluesValid : panStructValuesFieldsOkBool state.structs values = true := by
                simpa only [panStructValueFieldsOkBool] using hchildIH.2.1
              have hselectedValid := panStructValuesFieldsOkBool_getElem?
                state.structs values index selected hvaluesValid hselected
              have hselectedShape :
                  (values.map panSemShapeOf)[index]? = some (panSemShapeOf selected) := by
                simpa [List.getElem?_map] using
                  congrArg (Option.map panSemShapeOf) hselected
              have hshape :
                  structOldExpShape context (.rField index expression) =
                    panSemShapeOf selected := by
                simp [structOldExpShape, hchildIH.1, panSemShapeOf,
                  hselectedShape]
              have hselectedConverted :
                  (values.map panStructConvertValue)[index]? =
                    some (panStructConvertValue selected) := by
                simpa [List.getElem?_map] using
                  congrArg (Option.map panStructConvertValue) hselected
              have hcompiledChild :
                  evalPanValueExpFull (panStructConvertState context state).structs
                    (panStructConvertState context state).locals
                    (panStructConvertState context state).globals
                    (panStructConvertState context state).memory
                    (panStructConvertState context state).baseAddress
                    (panStructConvertState context state).topAddress bytesInWord
                    (structCompileExp context expression)
                    (memoryAccess := memoryAccess) =
                    some (.rStruct (values.map panStructConvertValue)) := by
                simpa [panStructConvertValue, panStructConvertValues_eq_map] using
                  hchildIH.2.2
              have htarget :
                  evalPanValueExpFull (panStructConvertState context state).structs
                    (panStructConvertState context state).locals
                    (panStructConvertState context state).globals
                    (panStructConvertState context state).memory
                    (panStructConvertState context state).baseAddress
                    (panStructConvertState context state).topAddress bytesInWord
                    (structCompileExp context (.rField index expression))
                    (memoryAccess := memoryAccess) =
                    some (panStructConvertValue selected) := by
                simp only [structCompileExp]
                simp only [evalPanValueExpFull, hcompiledChild]
                exact hselectedConverted
              exact ⟨hshape, hselectedValid, htarget⟩

/-- Lookup in HOL's `FMAP_MAP2`-shaped `InfoMap` representation commutes with
    mapping values. Keeping this finite list, rather than only its total lookup
    function, preserves the exact support needed by `compile_correct`. -/
theorem lookupInfo_mapValues [BEq String] (entries : InfoMap α)
    (name : String) (convert : α → β) :
    lookupInfo name (entries.map fun (key, value) => (key, convert value)) =
      (lookupInfo name entries).map convert := by
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      by_cases hkey : key == name
      · simp [lookupInfo, hkey]
      · simp [lookupInfo, hkey, ih]

theorem panStruct_mapKeys_preserved (entries : InfoMap α)
    (transform : String × α → String × β)
    (htransform : ∀ entry, (transform entry).1 = entry.1) :
    (entries.map transform).map Prod.fst = entries.map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      simp [ih, htransform]

/-- A finite-map representation of the map-valued fields in HOL's
    `panSem$state`, together with its exact lookup view in the production
    `PanSemState` evaluator. `entries` are authoritative; the agreement fields
    make locals, globals, and exception-shape lookup use HOL equality directly.
    The `LawfulBEq String` parameter ensures production code-map lookup agrees
    with equality-based HOL `FLOOKUP`. `Nodup` records the key uniqueness
    inherent in HOL finite maps. -/
structure PanStructFiniteState [BEq String] [LawfulBEq String]
    (α : Type u) (ffi : Type v) where
  runtime : PanSemState α ffi
  locals : InfoMap (PanValue α)
  globals : InfoMap (PanValue α)
  exceptionShapes : InfoMap Shape
  locals_nodup : (locals.map Prod.fst).Nodup
  globals_nodup : (globals.map Prod.fst).Nodup
  exceptionShapes_nodup : (exceptionShapes.map Prod.fst).Nodup
  code_nodup : (runtime.code.map Prod.fst).Nodup
  locals_lookup : ∀ name, runtime.locals name = panPropsALookupEq name locals
  globals_lookup : ∀ name, runtime.globals name = panPropsALookupEq name globals
  exceptionShapes_lookup :
    ∀ name, runtime.exceptionShapes name = panPropsALookupEq name exceptionShapes

/-- Build the production evaluator view from explicit HOL-shaped finite maps.
    The only side conditions are the key uniqueness conditions that are part
    of the finite-map representation itself; lookup agreement is constructed
    definitionally instead of being added as a theorem premise. -/
def panStructFiniteStateFromMaps [BEq String] [LawfulBEq String]
    (runtime : PanSemState α ffi)
    (locals globals : InfoMap (PanValue α)) (exceptionShapes : InfoMap Shape)
    (code : PanSemCodeMap α)
    (locals_nodup : (locals.map Prod.fst).Nodup)
    (globals_nodup : (globals.map Prod.fst).Nodup)
    (exceptionShapes_nodup : (exceptionShapes.map Prod.fst).Nodup)
    (code_nodup : (code.map Prod.fst).Nodup) : PanStructFiniteState α ffi where
  runtime := { runtime with
    locals := fun name => panPropsALookupEq name locals
    globals := fun name => panPropsALookupEq name globals
    exceptionShapes := fun name => panPropsALookupEq name exceptionShapes
    code := code }
  locals := locals
  globals := globals
  exceptionShapes := exceptionShapes
  locals_nodup := locals_nodup
  globals_nodup := globals_nodup
  exceptionShapes_nodup := exceptionShapes_nodup
  code_nodup := code_nodup
  locals_lookup := by
    cases runtime
    intro name
    simp
  globals_lookup := by
    cases runtime
    intro name
    simp
  exceptionShapes_lookup := by
    cases runtime
    intro name
    simp

/-- Map all HOL finite-map fields while keeping the same finite key support.
    The result is again related to the production evaluator state by exact
    lookup equations. -/
def panStructConvertFiniteState [BEq String] [LawfulBEq String]
    (context : StructPassContext) (state : PanStructFiniteState α ffi) :
    PanStructFiniteState α ffi where
  runtime := panStructConvertState context state.runtime
  locals := state.locals.map fun (name, value) =>
    (name, panStructConvertValue value)
  globals := state.globals.map fun (name, value) =>
    (name, panStructConvertValue value)
  exceptionShapes := state.exceptionShapes.map fun (name, shape) =>
    (name, structCompileShape context.structs shape)
  locals_nodup := by
    rw [panStruct_mapKeys_preserved state.locals
      (fun (name, value) => (name, panStructConvertValue value))]
    · exact state.locals_nodup
    · intro entry
      rfl
  globals_nodup := by
    rw [panStruct_mapKeys_preserved state.globals
      (fun (name, value) => (name, panStructConvertValue value))]
    · exact state.globals_nodup
    · intro entry
      rfl
  exceptionShapes_nodup := by
    rw [panStruct_mapKeys_preserved state.exceptionShapes
      (fun (name, shape) => (name, structCompileShape context.structs shape))]
    · exact state.exceptionShapes_nodup
    · intro entry
      rfl
  code_nodup := by
    change ((panStructConvertCode context state.runtime.code).map Prod.fst).Nodup
    rw [show (panStructConvertCode context state.runtime.code).map Prod.fst =
        state.runtime.code.map Prod.fst by
          apply panStruct_mapKeys_preserved
          intro entry
          cases entry with
          | mk name value => rfl]
    exact state.code_nodup
  locals_lookup := by
    intro name
    simp [panStructConvertState, panPropsALookupEq_mapValues, state.locals_lookup]
  globals_lookup := by
    intro name
    simp [panStructConvertState, panPropsALookupEq_mapValues, state.globals_lookup]
  exceptionShapes_lookup := by
    intro name
    simp [panStructConvertState, panPropsALookupEq_mapValues,
      state.exceptionShapes_lookup]

@[simp] theorem panStructConvertFiniteState_locals_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).locals.map Prod.fst =
      state.locals.map Prod.fst := by
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

@[simp] theorem panStructConvertFiniteState_globals_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).globals.map Prod.fst =
      state.globals.map Prod.fst := by
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

@[simp] theorem panStructConvertFiniteState_exceptionShapes_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).exceptionShapes.map Prod.fst =
      state.exceptionShapes.map Prod.fst := by
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

@[simp] theorem panStructConvertFiniteState_code_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).runtime.code.map Prod.fst =
      state.runtime.code.map Prod.fst := by
  change (panStructConvertCode context state.runtime.code).map Prod.fst =
    state.runtime.code.map Prod.fst
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

def panStructConvertLocalMap (locals : VarName → Option (PanValue α)) :=
  fun name => (locals name).map panStructConvertValue

def panStructConvertControlResult : PanValueFfiControlResult α σ →
    PanValueFfiControlResult α σ
  | .normal locals globals memory ffi =>
      .normal (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .error locals globals memory ffi =>
      .error (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .returned locals globals memory ffi values =>
      .returned (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi (panStructConvertValues values)
  | .raised locals globals memory ffi exception value =>
      .raised (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi exception (panStructConvertValue value)
  | .broke locals globals memory ffi =>
      .broke (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .continued locals globals memory ffi =>
      .continued (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .finalFfi locals globals memory ffi event =>
      .finalFfi (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi event

def panStructConvertClockOutcome : PanValueFfiClockOutcome α σ →
    PanValueFfiClockOutcome α σ
  | .control result => .control (panStructConvertControlResult result)
  | .timeout locals globals memory ffi =>
      .timeout (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi

def panStructConvertClockResult (result : PanValueFfiClockResult α σ) :
    PanValueFfiClockResult α σ :=
  (panStructConvertClockOutcome result.1, result.2)

@[simp] theorem panStructConvertState_code [BEq String]
    (context : StructPassContext) (state : PanSemState α ffi) :
    (panStructConvertState context state).code =
      panStructConvertCode context state.code := rfl

@[simp] theorem panStructCompileSkip_eq_skip [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.skip : Prog α) = .skip := by
  simp [structCompileProg]

@[simp] theorem panStructCompileBreak_eq_break [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.break : Prog α) = .break := by
  simp [structCompileProg]

/-- Production source-state evaluator equation corresponding to HOL
    `evaluate (Break,s) = (SOME Break,s)`. -/
theorem panStructSourceBreakEvaluation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.break : Prog α) =
      some ((.control (.broke state.locals state.globals state.memory state.ffi),
          state.clock), state) := by
  simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

/-- Source/converted evaluator projection for production Break states. -/
theorem panStructBreakEvaluatorProjection
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertState context state)
        (structCompileProg context (.break : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.break : Prog α)).map
    (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState context postState)) := by
  rw [panStructCompileBreak_eq_break,
    panStructSourceBreakEvaluation evaluationContext primitive handler bytesInWord state,
    panStructSourceBreakEvaluation evaluationContext primitive handler bytesInWord
      (panStructConvertState context state)]
  simp [panStructConvertClockResult, panStructConvertClockOutcome,
    panStructConvertControlResult, panStructConvertState]
  constructor <;> rfl

/-- Full Break specialization of HOL `compile_correct`. Break is a continuing
    control result in HOL, so the unchanged source state preserves both field
    validity and both shape maps. This states all compile_correct
    postconditions over the finite-map wrapper and proves target evaluation
    from the source evaluator equation; it assumes no target result. It stays
    untagged because HOL has only the quantified theorem and Lean encodes
    `SOME Break` as a `.broke` clock outcome. -/
theorem panStructCompileCorrectBreakCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ))
    (hsourceBreak : panSemEvaluateCodeStateWithPostState evaluationContext
      primitive handler bytesInWord state.runtime (.break : Prog α) =
        some ((.control (.broke state.runtime.locals state.runtime.globals
          state.runtime.memory state.runtime.ffi), state.runtime.clock), state.runtime))
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hlocalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.locals)
    (_hglobalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.break : Prog α)) =
      some ((.control (.broke
        (panStructConvertFiniteState context state).runtime.locals
        (panStructConvertFiniteState context state).runtime.globals
        (panStructConvertFiniteState context state).runtime.memory
        (panStructConvertFiniteState context state).runtime.ffi),
        (panStructConvertFiniteState context state).runtime.clock),
        (panStructConvertFiniteState context state).runtime) ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.locals ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.globals ∧
    panStructShapeMapEq context.globals state.runtime.globals ∧
    panStructShapeMapEq context.locals state.runtime.locals ∧
    panStructValuesFieldsOkBool (α := α) state.runtime.structs [] = true ∧
    panIsWfShapeValuesBool (α := α) state.runtime.structs [] = true := by
  have hprojection := panStructBreakEvaluatorProjection context evaluationContext
    primitive handler bytesInWord state.runtime
  rw [hsourceBreak] at hprojection
  have htarget :
      panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
          bytesInWord (panStructConvertFiniteState context state).runtime
          (structCompileProg context (.break : Prog α)) =
        some ((.control (.broke
          (panStructConvertFiniteState context state).runtime.locals
          (panStructConvertFiniteState context state).runtime.globals
          (panStructConvertFiniteState context state).runtime.memory
          (panStructConvertFiniteState context state).runtime.ffi),
          (panStructConvertFiniteState context state).runtime.clock),
          (panStructConvertFiniteState context state).runtime) := by
    exact hprojection
  exact ⟨htarget, hlocalsFields, hglobalsFields, hglobalsMap, hlocalsMap,
    by simp [panStructValuesFieldsOkBool], by simp [panIsWfShapeValuesBool]⟩

@[simp] theorem panStructCompileContinue_eq_continue [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.continue : Prog α) = .continue := by
  simp [structCompileProg]

/-- Production source evaluator equation corresponding to HOL
    `evaluate (Continue,s) = (SOME Continue,s)`. -/
theorem panStructSourceContinueEvaluation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.continue : Prog α) =
      some ((.control (.continued state.locals state.globals state.memory state.ffi),
          state.clock), state) := by
  simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

/-- Source/converted evaluator projection for production Continue states. -/
theorem panStructContinueEvaluatorProjection
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertState context state)
        (structCompileProg context (.continue : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.continue : Prog α)).map
    (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState context postState)) := by
  rw [panStructCompileContinue_eq_continue,
    panStructSourceContinueEvaluation evaluationContext primitive handler bytesInWord state,
    panStructSourceContinueEvaluation evaluationContext primitive handler bytesInWord
      (panStructConvertState context state)]
  simp [panStructConvertClockResult, panStructConvertClockOutcome,
    panStructConvertControlResult, panStructConvertState]
  constructor <;> rfl

/-- Full Continue specialization of HOL `compile_correct` over finite-map
    state. The unchanged source state preserves both field-validity clauses
    and both shape maps, and the result-value obligations are empty. It uses
    the source evaluation equation and proves target evaluation itself. This
    stays untagged because HOL has only the quantified theorem and encodes
    `SOME Continue` as Lean's `.continued` clock outcome. -/
theorem panStructCompileCorrectContinueCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ))
    (hsourceContinue : panSemEvaluateCodeStateWithPostState evaluationContext
      primitive handler bytesInWord state.runtime (.continue : Prog α) =
        some ((.control (.continued state.runtime.locals state.runtime.globals
          state.runtime.memory state.runtime.ffi), state.runtime.clock), state.runtime))
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hlocalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.locals)
    (_hglobalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.continue : Prog α)) =
      some ((.control (.continued
        (panStructConvertFiniteState context state).runtime.locals
        (panStructConvertFiniteState context state).runtime.globals
        (panStructConvertFiniteState context state).runtime.memory
        (panStructConvertFiniteState context state).runtime.ffi),
        (panStructConvertFiniteState context state).runtime.clock),
        (panStructConvertFiniteState context state).runtime) ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.locals ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.globals ∧
    panStructShapeMapEq context.globals state.runtime.globals ∧
    panStructShapeMapEq context.locals state.runtime.locals ∧
    panStructValuesFieldsOkBool (α := α) state.runtime.structs [] = true ∧
    panIsWfShapeValuesBool (α := α) state.runtime.structs [] = true := by
  have hprojection := panStructContinueEvaluatorProjection context evaluationContext
    primitive handler bytesInWord state.runtime
  rw [hsourceContinue] at hprojection
  have htarget :
      panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
          bytesInWord (panStructConvertFiniteState context state).runtime
          (structCompileProg context (.continue : Prog α)) =
        some ((.control (.continued
          (panStructConvertFiniteState context state).runtime.locals
          (panStructConvertFiniteState context state).runtime.globals
          (panStructConvertFiniteState context state).runtime.memory
          (panStructConvertFiniteState context state).runtime.ffi),
          (panStructConvertFiniteState context state).runtime.clock),
          (panStructConvertFiniteState context state).runtime) := by
    exact hprojection
  exact ⟨htarget, hlocalsFields, hglobalsFields, hglobalsMap, hlocalsMap,
    by simp [panStructValuesFieldsOkBool], by simp [panIsWfShapeValuesBool]⟩

/-- This documentation applies only to the immediately following theorem.
    It is an untagged Local/Global Var-constructor specialization of HOL
    `compile_exp_correct`, not an exact theorem port: HOL has one universally
    quantified theorem and no separately named Var case. The source-evaluation
    premise is retained. The remaining premises differ as follows: HOL's direct
    `ctxt.structs = MAP ... s.structs` equality is replaced by equality of
    shape views, which observes names and fields but not full Lean struct-info
    records; finite-map `FEVERY` field-validity is expressed as pointwise Bool
    predicates over PanSemState's total runtime lookups; and `FMAP_MAP2` is
    expressed through pointwise shape-map adapters. Lawful `BEq String` makes
    production lookup agree with HOL equality. `structInfosOk` is carried but
    unused by this Var proof. Lean also has a `shapedFields` cache absent from
    HOL, and the premises do not inspect it. The full evaluator additionally
    accepts explicit `bytesInWord` and optional `PanValueMemoryAccess` inputs;
    neither affects Var. The three conclusions are the Var instance of HOL's
    old-shape, `v_flds_ok`, and converted-evaluation conclusions. Other
    expression constructors remain open. -/
theorem panStructCompileExpCorrectVarCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (state : PanSemState α ffi)
    (bytesInWord : α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (name : VarName) (kind : VarKind) (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals
      state.globals state.memory state.baseAddress
      state.topAddress bytesInWord (.var kind name)
      (memoryAccess := memoryAccess) = some value)
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.structs state.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.structs state.globals)
    (_hstructInfos : structInfosOk state.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.globals) :
    structOldExpShape (α := α) context (.var kind name) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress
      bytesInWord (structCompileExp (α := α) context (.var kind name))
      (memoryAccess := memoryAccess) =
        some (panStructConvertValue value) := by
  cases kind with
  | «local» =>
      have hlookup : state.locals name = some value := by
        simpa [evalPanValueExpFull] using heval
      have hshapeMap : panPropsALookupEq name context.locals = some (panSemShapeOf value) := by
        rw [← lookupInfo_eq_panPropsALookupEq, hlocalsMap name, hlookup]
        rfl
      have hshapeLookup :
          @lookupInfo String Shape instBEqOfDecidableEq name context.locals =
            some (panSemShapeOf value) := by
        rw [lookupInfoStringDefault_eq_panPropsALookupEq, hshapeMap]
      refine ⟨?_, hlocalsFields name value hlookup, ?_⟩
      · simp only [structOldExpShape]
        simpa using congrArg (fun result : Option Shape => result.getD .one) hshapeLookup
      · simp [evalPanValueExpFull, structCompileExp, panStructConvertState, hlookup]
  | «global» =>
      have hlookup : state.globals name = some value := by
        simpa [evalPanValueExpFull] using heval
      have hshapeMap : panPropsALookupEq name context.globals = some (panSemShapeOf value) := by
        rw [← lookupInfo_eq_panPropsALookupEq, hglobalsMap name, hlookup]
        rfl
      have hshapeLookup :
          @lookupInfo String Shape instBEqOfDecidableEq name context.globals =
            some (panSemShapeOf value) := by
        rw [lookupInfoStringDefault_eq_panPropsALookupEq, hshapeMap]
      refine ⟨?_, hglobalsFields name value hlookup, ?_⟩
      · simp only [structOldExpShape]
        simpa using congrArg (fun result : Option Shape => result.getD .one) hshapeLookup
      · simp [evalPanValueExpFull, structCompileExp, panStructConvertState, hlookup]

/-- Derived Const-constructor specialization of HOL `compile_exp_correct`.
    This stays untagged because HOL has only the universally quantified
    theorem, not a separately named Const-case declaration. As in the Var
    case above, the context equality uses a fields shape-view, finite-map
    FEVERY becomes pointwise Bool validity over total lookups, and FMAP_MAP2
    uses pointwise shape-map adapters. Lawful `BEq String` aligns production
    lookup with HOL equality.
    It uses the faithful full evaluator with explicit `bytesInWord` and
    optional `PanValueMemoryAccess` parameters; neither affects Const. The
    theorem carries but does not use the translated struct-info premise. -/
theorem panStructCompileExpCorrectConstCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (state : PanSemState α ffi)
    (bytesInWord : α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (constant : α) (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals
      state.globals state.memory state.baseAddress
      state.topAddress bytesInWord (.const constant)
      (memoryAccess := memoryAccess) = some value)
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (_hlocalsFields : panStructEveryValueFieldsOkBool
      state.structs state.locals)
    (_hglobalsFields : panStructEveryValueFieldsOkBool
      state.structs state.globals)
    (_hstructInfos : structInfosOk state.structs)
    (_hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (_hglobalsMap : panStructShapeMapEq context.globals state.globals) :
    structOldExpShape (α := α) context (.const constant) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress
      bytesInWord (structCompileExp (α := α) context (.const constant))
      (memoryAccess := memoryAccess) =
        some (panStructConvertValue value) := by
  cases value with
  | word wordValue =>
      have hword : constant = wordValue := by
        simpa [evalPanValueExpFull] using heval
      subst wordValue
      refine ⟨by simp [structOldExpShape, panSemShapeOf], ?_, ?_⟩
      · simp [panStructValueFieldsOkBool]
      · simp [evalPanValueExpFull, panStructConvertState, panStructConvertValue]
  | rStruct values => simp [evalPanValueExpFull] at heval
  | nStruct name fields => simp [evalPanValueExpFull] at heval

/-- Derived Load-constructor specialization of HOL `compile_exp_correct`.
    HOL has only the universally quantified theorem, so this is untagged; it
    translates the struct-context premise through `panStructContextShapeView`
    and retains all three HOL conclusion roles plus the recursive address IH.
    The local/global `FEVERY` and `FMAP_MAP2` premises are retained but unused
    by this constructor. Source, address IH, and converted evaluation share an
    explicit caller-supplied `PanValueMemoryAccess`, preserving its domain and
    endian behavior for the load; the paired RV64 test derives it from the
    source state. Lean still exposes `bytesInWord`, the memory
    adapter, and a pointwise Bool validity predicate instead of HOL's fixed
    word stride, finite-map memory, and `v_flds_ok`. -/
theorem panStructCompileExpCorrectLoadCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (shape : Shape) (addressExpression : Exp α)
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord
      (.load shape addressExpression) (memoryAccess := some memoryAccess) = some value)
    (hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (_hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (_hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (hstructInfos : structInfosOk state.structs)
    (_hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (_hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinduction : ∀ addressValue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord addressExpression
        (memoryAccess := some memoryAccess) = some addressValue →
      structOldExpShape context addressExpression = panSemShapeOf addressValue ∧
      panStructValueFieldsOkBool state.structs addressValue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context addressExpression) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue addressValue)) :
    structOldExpShape context (.load shape addressExpression) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.load shape addressExpression))
      (memoryAccess := some memoryAccess) =
        some (panStructConvertValue value) := by
  cases haddress : evalPanValueExpFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord addressExpression
      (memoryAccess := some memoryAccess) with
  | none => simp [evalPanValueExpFull, haddress] at heval
  | some addressValue =>
      cases addressValue with
      | word address =>
          have hsourceLoad :
              panValueFlatLoad state.structs state.memory bytesInWord address shape
                (some memoryAccess) =
                some value := by
            simpa [evalPanValueExpFull, haddress] using heval
          have hwf : isWfShape state.structs shape = true := by
            cases hshapeWf : isWfShape state.structs shape with
            | false => simp [panValueFlatLoad, hshapeWf] at hsourceLoad
            | true => rfl
          have hsourceFuel :
              panValueFlatLoadFuel state.structs
                (panValueFlatReadWord state.memory bytesInWord (some memoryAccess)) bytesInWord
                (panValueFlatContextFuel state.structs +
                  panValueFlatShapeFuel shape + 1) shape address = some value := by
            simpa [panValueFlatLoad, hwf] using hsourceLoad
          have hloadFacts := panValueFlatLoadFuel_shape_fields bytesInWord
            (panValueFlatReadWord state.memory bytesInWord (some memoryAccess)) state.structs
            (panValueFlatContextFuel state.structs + panValueFlatShapeFuel shape + 1)
            shape address value hstructInfos hwf hsourceFuel
          have hsourceFuelEnough :
              panValueFlatContextFuel state.structs + panValueFlatShapeFuel shape + 1 ≤
                panValueFlatContextFuel state.structs + panValueFlatShapeFuel shape + 1 :=
            Nat.le_refl _
          have hconvertedLoad := panValueFlatLoadFuel_convert_all_context_shape_view
            (bytesInWord := bytesInWord)
            (readWord := panValueFlatReadWord state.memory bytesInWord (some memoryAccess))
            state.structs context.structs hstructs
            (panValueFlatContextFuel state.structs + panValueFlatShapeFuel shape + 1)
            shape address
            (panValueFlatShapeFuel (structCompileShape context.structs shape) + 1)
            value hstructInfos hwf hsourceFuelEnough (Nat.le_refl _) hsourceFuel
          have hcompiledLoadFuel :
              panValueFlatLoadFuel []
                (panValueFlatReadWord state.memory bytesInWord (some memoryAccess)) bytesInWord
                (panValueFlatShapeFuel (structCompileShape context.structs shape) + 1)
                (structCompileShape context.structs shape) address =
                some (panStructConvertValue value) := by
            simpa [structCompileShape] using hconvertedLoad
          have hcompiledWf :
              isWfShape [] (structCompileShape context.structs shape) = true :=
            (structCompileShapeWF_isWfShape []).1 context.structs shape
          have htargetLoad :
              panValueFlatLoad [] state.memory bytesInWord address
                (structCompileShape context.structs shape) (some memoryAccess) =
                  some (panStructConvertValue value) := by
            simpa [panValueFlatLoad, panValueFlatContextFuel, hcompiledWf] using
              hcompiledLoadFuel
          have haddressFacts := hinduction (.word address) haddress
          refine ⟨?_, hloadFacts.2, ?_⟩
          · simpa [structOldExpShape, panSemShapeOf] using hloadFacts.1.symm
          · have hcompiledExp :
                structCompileExp context (.load shape addressExpression) =
                  .load (structCompileShape context.structs shape)
                    (structCompileExp context addressExpression) := by
              simp [structCompileExp]
            rw [hcompiledExp]
            simp only [evalPanValueExpFull, haddressFacts.2.2]
            simp only [panStructConvertValue]
            simpa [panStructConvertState] using htargetLoad
      | rStruct fields => simp [evalPanValueExpFull, haddress] at heval
      | nStruct name fields => simp [evalPanValueExpFull, haddress] at heval

/-- Derived LoadByte-constructor specialization of HOL `compile_exp_correct`.
    It keeps the three parent conclusion roles and translated induction
    premises, and passes the same explicit memory-access model through source,
    address IH, and converted execution. The adapter is passed unchanged, so
    successful and failed reads preserve its domain/endian policy; to match
    HOL `mem_load_byte`, callers construct it from the state's memory domain
    and endian flag. The theorem is intentionally untagged: HOL stores those
    values in the state, while Lean passes `PanValueMemoryAccess` and
    `bytesInWord` explicitly and translates context/FEVERY/FMAP_MAP2 premises
    through Lean views. Full-evaluator shift dictionaries are runtime
    parameters, not additional HOL logical premises. Local/global validity,
    shape maps and structInfosOk are unused in this constructor. -/
theorem panStructCompileExpCorrectLoadByteCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (addressExpression : Exp α) (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord (.loadByte addressExpression)
      (memoryAccess := some memoryAccess) = some value)
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (_hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (_hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (_hstructInfos : structInfosOk state.structs)
    (_hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (_hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinduction : ∀ addressValue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord addressExpression
        (memoryAccess := some memoryAccess) =
          some addressValue →
      structOldExpShape context addressExpression = panSemShapeOf addressValue ∧
      panStructValueFieldsOkBool state.structs addressValue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context addressExpression)
        (memoryAccess := some memoryAccess) =
          some (panStructConvertValue addressValue)) :
    structOldExpShape (α := α) context (.loadByte addressExpression) =
      panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.loadByte addressExpression))
      (memoryAccess := some memoryAccess) =
        some (panStructConvertValue value) := by
  cases haddress : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord addressExpression
      (memoryAccess := some memoryAccess) with
  | none => simp [evalPanValueExpFull, haddress] at heval
  | some addressValue =>
      cases addressValue with
      | word address =>
          cases hread : memoryAccess.readByte memoryAccess.domain state.memory
              bytesInWord address with
          | none => simp [evalPanValueExpFull, haddress, hread] at heval
          | some loadedWord =>
                  have hvalue : value = .word loadedWord := by
                    simpa [evalPanValueExpFull, haddress, hread] using heval.symm
                  subst value
                  have haddressFacts := hinduction (.word address) haddress
                  refine ⟨by simp [structOldExpShape, panSemShapeOf], ?_, ?_⟩
                  · simp [panStructValueFieldsOkBool]
                  · have hcompiledAddress :
                        evalPanValueExpFull []
                          (fun name => (state.locals name).map panStructConvertValue)
                          (fun name => (state.globals name).map panStructConvertValue)
                          state.memory state.baseAddress state.topAddress bytesInWord
                          (structCompileExp context addressExpression)
                          (memoryAccess := some memoryAccess) = some (.word address) := by
                      simpa [panStructConvertState, panStructConvertValue] using haddressFacts.2.2
                    have hconvertedLoad :
                        evalPanValueExpFull (panStructConvertState context state).structs
                          (panStructConvertState context state).locals
                          (panStructConvertState context state).globals
                          (panStructConvertState context state).memory
                          (panStructConvertState context state).baseAddress
                          (panStructConvertState context state).topAddress bytesInWord
                          (.loadByte (structCompileExp context addressExpression))
                          (memoryAccess := some memoryAccess) =
                            some (.word loadedWord) := by
                      simp [evalPanValueExpFull, panStructConvertState,
                        hcompiledAddress, hread]
                    simpa [structCompileExp, panStructConvertValue] using hconvertedLoad
      | rStruct fields => simp [evalPanValueExpFull, haddress] at heval
      | nStruct name fields => simp [evalPanValueExpFull, haddress] at heval

/-- Load32 constructor specialization over the full source evaluator's
    explicit memory-access interface. Passing `memoryAccess` through both
    evaluations makes this case use its aligned, domain-checked, four-byte
    `read32` operation; the default full-evaluator path is a whole-cell read
    and is not used here. This remains untagged because HOL has only the
    universal `compile_exp_correct` theorem and the context/FEVERY/FMAP_MAP2
    premises below are translated through Lean views and total-function
    adapters. -/
theorem panStructCompileExpCorrectLoad32Case
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [OfNat α 2] [OfNat α 3] [Add α] [Mul α] [Sub α]
    [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (addressExpression : Exp α) (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord (.load32 addressExpression)
      (memoryAccess := some memoryAccess) = some value)
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (_hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (_hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (_hstructInfos : structInfosOk state.structs)
    (_hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (_hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinduction : ∀ addressValue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord addressExpression
        (memoryAccess := some memoryAccess) = some addressValue →
      structOldExpShape context addressExpression = panSemShapeOf addressValue ∧
      panStructValueFieldsOkBool state.structs addressValue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context addressExpression)
        (memoryAccess := some memoryAccess) =
          some (panStructConvertValue addressValue)) :
    structOldExpShape (α := α) context (.load32 addressExpression) =
      panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.load32 addressExpression))
      (memoryAccess := some memoryAccess) =
        some (panStructConvertValue value) := by
  cases haddress : evalPanValueExpFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord addressExpression
      (memoryAccess := some memoryAccess) with
  | none => simp [evalPanValueExpFull, haddress] at heval
  | some addressValue =>
      cases addressValue with
      | word address =>
          cases hread : memoryAccess.read32 memoryAccess.domain state.memory
              bytesInWord address with
          | none => simp [evalPanValueExpFull, haddress, hread] at heval
          | some loadedWord =>
              have hvalue : value = .word loadedWord := by
                simpa [evalPanValueExpFull, haddress, hread] using heval.symm
              subst value
              have haddressFacts := hinduction (.word address) haddress
              refine ⟨by simp [structOldExpShape, panSemShapeOf], ?_, ?_⟩
              · simp [panStructValueFieldsOkBool]
              · have hcompiledAddress :
                    evalPanValueExpFull []
                      (fun name => (state.locals name).map panStructConvertValue)
                      (fun name => (state.globals name).map panStructConvertValue)
                      state.memory state.baseAddress state.topAddress bytesInWord
                      (structCompileExp context addressExpression)
                      (memoryAccess := some memoryAccess) = some (.word address) := by
                  simpa [panStructConvertState, panStructConvertValue] using
                    haddressFacts.2.2
                have hconvertedLoad :
                    evalPanValueExpFull []
                      (fun name => (state.locals name).map panStructConvertValue)
                      (fun name => (state.globals name).map panStructConvertValue)
                      state.memory state.baseAddress state.topAddress bytesInWord
                      (.load32 (structCompileExp context addressExpression))
                      (memoryAccess := some memoryAccess) = some (.word loadedWord) := by
                  simp [evalPanValueExpFull, hcompiledAddress, hread]
                simpa [structCompileExp, panStructConvertValue,
                  panStructConvertState] using hconvertedLoad
      | rStruct fields => simp [evalPanValueExpFull, haddress] at heval
      | nStruct name fields => simp [evalPanValueExpFull, haddress] at heval

/-- Derived BaseAddr-constructor specialization of HOL `compile_exp_correct`.
    HOL has only the universally quantified theorem, so this remains untagged.
    The translated context, FEVERY, FMAP_MAP2, and struct-info premises are
    retained; the literal case does not use them. The source and converted
    executions use the full evaluator shared with other migrated cases. Its
    `PanShiftWidth`, `ArithmeticShiftRight`, and `RotateRightOp` dictionaries
    are Lean runtime parameters; the BaseAddr case does not inspect them.
    Lean's context view and total-function Bool/map adapters differ from HOL's
    finite-map statements; `bytesInWord` and optional memory access are
    evaluator parameters absent from this HOL constructor case. -/
theorem panStructCompileExpCorrectBaseAddrCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : Option (PanValueMemoryAccess α))
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord .baseAddr
      (memoryAccess := memoryAccess) = some value)
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (_hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (_hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (_hstructInfos : structInfosOk state.structs)
    (_hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (_hglobalsMap : panStructShapeMapEq context.globals state.globals) :
    structOldExpShape (α := α) context .baseAddr = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context .baseAddr) (memoryAccess := memoryAccess) =
        some (panStructConvertValue value) := by
  cases value with
  | word wordValue =>
      have hword : wordValue = state.baseAddress := by
        simpa [evalPanValueExpFull] using heval.symm
      subst wordValue
      refine ⟨by simp [structOldExpShape, panSemShapeOf], ?_, ?_⟩
      · simp [panStructValueFieldsOkBool]
      · simp [evalPanValueExpFull, structCompileExp, panStructConvertState,
          panStructConvertValue]
  | rStruct values => simp [evalPanValueExpFull] at heval
  | nStruct name fields => simp [evalPanValueExpFull] at heval

/-- Derived TopAddr-constructor specialization of HOL `compile_exp_correct`.
    It carries the same translated finite-map premise adapters as the sibling
    BaseAddr case; HOL has no separately named TopAddr theorem. Source and
    converted evaluation use `evalPanValueExpFull`. Its shift-semantics
    dictionaries are Lean runtime parameters and are not inspected by this
    literal case. The projected context and total-function Bool/map adapters
    still differ from HOL's finite-map statements. -/
theorem panStructCompileExpCorrectTopAddrCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : Option (PanValueMemoryAccess α))
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord .topAddr
      (memoryAccess := memoryAccess) = some value)
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (_hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (_hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (_hstructInfos : structInfosOk state.structs)
    (_hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (_hglobalsMap : panStructShapeMapEq context.globals state.globals) :
    structOldExpShape (α := α) context .topAddr = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context .topAddr) (memoryAccess := memoryAccess) =
        some (panStructConvertValue value) := by
  cases value with
  | word wordValue =>
      have hword : wordValue = state.topAddress := by
        simpa [evalPanValueExpFull] using heval.symm
      subst wordValue
      refine ⟨by simp [structOldExpShape, panSemShapeOf], ?_, ?_⟩
      · simp [panStructValueFieldsOkBool]
      · simp [evalPanValueExpFull, structCompileExp, panStructConvertState,
          panStructConvertValue]
  | rStruct values => simp [evalPanValueExpFull] at heval
  | nStruct name fields => simp [evalPanValueExpFull] at heval

/-- Derived BytesInWord-constructor specialization of HOL `compile_exp_correct`.
    The HOL evaluator uses its fixed `bytes_in_word`; production Lean exposes
    the value as the explicit `bytesInWord` evaluator argument. Source and
    converted execution use `evalPanValueExpFull`; its shift-semantics
    dictionaries are Lean runtime parameters and are not inspected by this
    literal case. Context and map predicates also use the documented Lean
    views rather than HOL's finite maps. -/
theorem panStructCompileExpCorrectBytesInWordCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : Option (PanValueMemoryAccess α))
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord .bytesInWord
      (memoryAccess := memoryAccess) = some value)
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (_hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (_hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (_hstructInfos : structInfosOk state.structs)
    (_hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (_hglobalsMap : panStructShapeMapEq context.globals state.globals) :
    structOldExpShape (α := α) context .bytesInWord = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context .bytesInWord) (memoryAccess := memoryAccess) =
        some (panStructConvertValue value) := by
  cases value with
  | word wordValue =>
      have hword : wordValue = bytesInWord := by
        simpa [evalPanValueExpFull] using heval.symm
      subst wordValue
      refine ⟨by simp [structOldExpShape, panSemShapeOf], ?_, ?_⟩
      · simp [panStructValueFieldsOkBool]
      · simp [evalPanValueExpFull, structCompileExp, panStructConvertState,
          panStructConvertValue]
  | rStruct values => simp [evalPanValueExpFull] at heval
  | nStruct name fields => simp [evalPanValueExpFull] at heval

/-- Evaluator-equation support for a future HOL `compile_correct` Skip case:
    this proves only the two source/converted outcomes and omits the HOL
    theorem's premises and value/shape-map postconditions, so it is not an
    induction case port and intentionally has no `@[hol]` tag. -/
theorem panStructSkipEvaluatorSupport
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.skip : Prog α) =
      some ((.control (.normal state.locals state.globals state.memory state.ffi),
          state.clock), state) ∧
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertState context state)
        (structCompileProg context (.skip : Prog α)) =
      some ((.control (.normal (panStructConvertState context state).locals
          (panStructConvertState context state).globals
          (panStructConvertState context state).memory
          (panStructConvertState context state).ffi),
        (panStructConvertState context state).clock),
        panStructConvertState context state) := by
  constructor
  · exact panSemEvaluateCodeStateWithPostState_skip
      evaluationContext primitive handler bytesInWord state
  · simpa [structCompileProg] using
      (panSemEvaluateCodeStateWithPostState_skip
        evaluationContext primitive handler bytesInWord
        (panStructConvertState context state))

/-- The HOL-shaped Skip support theorem specialized to a state whose locals,
    globals, exception-shape map, and code all carry finite support and unique
    keys. This remains evaluator support: the full `compile_correct` premises
    and FEVERY/shape-map/result conclusions are not asserted here. -/
theorem panStructSkipFiniteMapEvaluatorSupport
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state.runtime (.skip : Prog α) =
      some ((.control (.normal state.runtime.locals state.runtime.globals
          state.runtime.memory state.runtime.ffi), state.runtime.clock), state.runtime) ∧
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.skip : Prog α)) =
      some ((.control (.normal (panStructConvertFiniteState context state).runtime.locals
          (panStructConvertFiniteState context state).runtime.globals
          (panStructConvertFiniteState context state).runtime.memory
          (panStructConvertFiniteState context state).runtime.ffi),
          (panStructConvertFiniteState context state).runtime.clock),
        (panStructConvertFiniteState context state).runtime) := by
  simpa [panStructConvertFiniteState] using
    (panStructSkipEvaluatorSupport context evaluationContext primitive handler
      bytesInWord state.runtime)

/-- Exact production-evaluator projection for HOL-shaped finite-map state on
    Skip. Converting the source execution's clock result and post-state yields
    the execution of the converted state and compiled program. The state
    wrapper carries finite support and lookup agreement, so the projection does
    not assume a separate finite-support premise. -/
theorem panStructFiniteMapSkipEvaluationProjection
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.skip : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state.runtime (.skip : Prog α)).map
        (fun (result, postState) =>
          (panStructConvertClockResult result, panStructConvertState context postState)) := by
  simp [panSemEvaluateCodeStateWithPostState_skip,
    panStructConvertFiniteState, panStructConvertState, panStructConvertClockResult,
    panStructConvertClockOutcome, panStructConvertControlResult]
  constructor <;> rfl

/-- Full Skip case of HOL `compile_correct`, specialized to the production
    `PanSemState` evaluator with the finite-map view carried by
    `PanStructFiniteState`. All HOL postconditions are included: converted
    evaluation/state, local and global field validity, the global shape map,
    the continuation-local shape map, and the empty result-value obligations.
    The context premise is the HOL fields projection; the state wrapper
    provides finite support without an extra premise. This case stays untagged
    because HOL has a single quantified theorem rather than a named Skip case,
    and Lean represents HOL `(NONE, state)` as a normal clock outcome. -/
theorem panStructCompileCorrectSkipCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ))
    (hsourceSkip : panSemEvaluateCodeStateWithPostState evaluationContext
      primitive handler bytesInWord state.runtime (.skip : Prog α) =
        some ((.control (.normal state.runtime.locals state.runtime.globals
          state.runtime.memory state.runtime.ffi), state.runtime.clock), state.runtime))
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hlocalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.locals)
    (_hglobalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.skip : Prog α)) =
      some ((.control (.normal
        (panStructConvertFiniteState context state).runtime.locals
        (panStructConvertFiniteState context state).runtime.globals
        (panStructConvertFiniteState context state).runtime.memory
        (panStructConvertFiniteState context state).runtime.ffi),
        (panStructConvertFiniteState context state).runtime.clock),
        (panStructConvertFiniteState context state).runtime) ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.locals ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.globals ∧
    panStructShapeMapEq context.globals state.runtime.globals ∧
    panStructShapeMapEq context.locals state.runtime.locals ∧
    panStructValuesFieldsOkBool (α := α) state.runtime.structs [] = true ∧
    panIsWfShapeValuesBool (α := α) state.runtime.structs [] = true := by
  have hprojection := panStructFiniteMapSkipEvaluationProjection context
    evaluationContext primitive handler bytesInWord state
  rw [hsourceSkip] at hprojection
  have htarget :
      panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
          bytesInWord (panStructConvertFiniteState context state).runtime
          (structCompileProg context (.skip : Prog α)) =
        some ((.control (.normal
          (panStructConvertFiniteState context state).runtime.locals
          (panStructConvertFiniteState context state).runtime.globals
          (panStructConvertFiniteState context state).runtime.memory
          (panStructConvertFiniteState context state).runtime.ffi),
          (panStructConvertFiniteState context state).runtime.clock),
          (panStructConvertFiniteState context state).runtime) := by
    exact hprojection
  exact ⟨htarget, hlocalsFields, hglobalsFields, hglobalsMap, hlocalsMap,
    by simp [panStructValuesFieldsOkBool], by simp [panIsWfShapeValuesBool]⟩

@[simp] theorem panStructCompileTick_eq_tick [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.tick : Prog α) = .tick := by
  simp [structCompileProg]

/-- Evaluator-equation support for a future HOL `compile_correct` Tick case:
    the source and compiled executions agree after the current conversion in
    both clock branches, but the HOL theorem's hypotheses and invariant
    postconditions are not included. This is not an induction case port and
    intentionally has no `@[hol]` tag. -/
theorem panStructTickEvaluatorSupport
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertState context state)
        (structCompileProg context (.tick : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.tick : Prog α)).map
        (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState context postState)) := by
  by_cases hclock : state.clock = 0
  · simp [panSemEvaluateCodeStateWithPostState_tick, panStructCompileTick_eq_tick,
      panStructConvertState, panStructConvertClockResult,
      panStructConvertClockOutcome, hclock]
    constructor <;> funext name <;> rfl
  · simp [panSemEvaluateCodeStateWithPostState_tick, panStructCompileTick_eq_tick,
      panStructConvertState, panStructConvertClockResult,
      panStructConvertClockOutcome, hclock]
    congr 1 <;> funext name <;> rfl

/-- Full Tick specialization of HOL `compile_correct` over finite-map state.
    The evaluator projection handles both HOL branches: timeout clears source
    locals at clock zero, while the continuing branch decrements the clock.
    Every compile_correct postcondition is stated: converted evaluation/state,
    field validity of post locals/globals, global shape-map preservation, the
    continuation-local shape map, and the empty result-value validity/WF
    obligations. The finite-map state wrapper supplies support and lookup
    relations; no target result is assumed. This remains untagged because HOL
    has no separate named Tick case and encodes its result/state pair with
    `TimeOut`/`NONE`, while Lean uses clock outcomes. -/
theorem panStructCompileCorrectTickCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ))
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hlocalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.locals)
    (_hglobalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.tick : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state.runtime (.tick : Prog α)).map
        (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState context postState)) ∧
    (if state.runtime.clock = 0 then
      panStructEveryValueFieldsOkBool state.runtime.structs
        (fun _ => none : VarName → Option (PanValue α))
     else
      panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.locals) ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.globals ∧
    panStructShapeMapEq context.globals state.runtime.globals ∧
    (state.runtime.clock ≠ 0 →
      panStructShapeMapEq context.locals state.runtime.locals) ∧
    panStructValuesFieldsOkBool (α := α) state.runtime.structs [] = true ∧
    panIsWfShapeValuesBool (α := α) state.runtime.structs [] = true := by
  have heval := panStructTickEvaluatorSupport context evaluationContext
    primitive handler bytesInWord state.runtime
  refine ⟨?_, ?_, hglobalsFields, hglobalsMap, ?_, ?_, ?_⟩
  · simpa [panStructConvertFiniteState] using heval
  · by_cases hzero : state.runtime.clock = 0
    · simp [hzero, panStructEveryValueFieldsOkBool]
    · simpa [hzero] using hlocalsFields
  · intro hcontinue
    exact hlocalsMap
  · simp [panStructValuesFieldsOkBool]
  · simp [panIsWfShapeValuesBool]

/-! Full-evaluator Op-constructor specialization of HOL
    `compile_exp_correct`. It stays untagged because HOL has one universal
    theorem rather than a named Op-case. One memory adapter is shared by
    source evaluation, operand induction hypotheses, and converted execution.
    Lean's shape-view/Bool premises, total lookups, and explicit word stride
    remain different from the HOL finite-map/fixed-width interface. -/
theorem panStructCompileExpCorrectOpCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α] [ArithmeticShiftRight α]
    [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (operator : BinOp) (arguments : List (Exp α)) (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord (.op operator arguments)
      (memoryAccess := some memoryAccess) = some value)
    (hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (hstructInfos : structInfosOk state.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinduction : ∀ argument, argument ∈ arguments → ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord argument
        (memoryAccess := some memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context argument = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context argument) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue subvalue)) :
    structOldExpShape context (.op operator arguments) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.op operator arguments))
      (memoryAccess := some memoryAccess) = some (panStructConvertValue value) := by
  let asWord : PanValue α → Option α := fun operand =>
    match operand with
    | .word word => some word
    | _ => none
  have hwordConvert : ∀ operand,
      asWord (panStructConvertValue operand) = asWord operand := by
    intro operand
    cases operand <;> simp [asWord, panStructConvertValue]
  have hmapWordConvert : ∀ operands : List (PanValue α),
      (operands.map panStructConvertValue).mapM asWord = operands.mapM asWord := by
    intro operands
    induction operands with
    | nil => rfl
    | cons operand operands ih => simp [List.mapM_cons, hwordConvert operand, ih]
  have hpointwise : ∀ expression, expression ∈ arguments → ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := some memoryAccess) = some subvalue →
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue subvalue) := by
    intro expression hmem subvalue hsub
    exact (hinduction expression hmem subvalue hsub hstructs hlocalsFields
      hglobalsFields hstructInfos hlocalsMap hglobalsMap).2.2
  cases harguments : evalPanValueExpsFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord arguments
      (memoryAccess := some memoryAccess) with
  | none => simp [evalPanValueExpFull, harguments] at heval
  | some operands =>
      cases hwords : operands.mapM (fun (operand : PanValue α) =>
          match operand with | .word word => some word | _ => none) with
      | none =>
          have heval' := heval
          simp only [evalPanValueExpFull] at heval'
          rw [harguments] at heval'
          change (operands.mapM (fun (operand : PanValue α) =>
            match operand with | .word word => some word | _ => none)).bind
              (fun words => Option.map PanValue.word
                (memoryAccess.wordOp operator words)) = some value at heval'
          rw [hwords] at heval'
          simp at heval'
      | some words =>
          have heval' := heval
          simp only [evalPanValueExpFull] at heval'
          rw [harguments] at heval'
          change (operands.mapM (fun (operand : PanValue α) =>
            match operand with | .word word => some word | _ => none)).bind
              (fun words => Option.map PanValue.word
                (memoryAccess.wordOp operator words)) = some value at heval'
          rw [hwords] at heval'
          cases hresult : memoryAccess.wordOp operator words with
          | none => simp [hresult] at heval'
          | some result =>
              have hvalue : value = .word result := by
                simp [hresult] at heval'
                exact heval'.symm
              have hcompiledArgs := panStructCompileExpsFullEvalOfPointwiseCorrect
                context state bytesInWord memoryAccess arguments operands harguments hpointwise
              have htargetWords :
                  (operands.map panStructConvertValue).mapM
                    (fun (operand : PanValue α) => match operand with
                      | .word word => some word
                      | _ => none) = some words := by
                simpa only [asWord] using (show
                  (operands.map panStructConvertValue).mapM asWord = some words by
                    rw [hmapWordConvert]
                    simpa only [asWord] using hwords)
              refine ⟨?_, ?_, ?_⟩
              · simp [structOldExpShape, panSemShapeOf, hvalue]
              · simp [panStructValueFieldsOkBool, hvalue]
              · have hcompiledOp : structCompileExp context (.op operator arguments) =
                    .op operator (structCompileExp.structCompileExps context arguments) := by
                  simp [structCompileExp]
                rw [hcompiledOp, hvalue]
                simp only [evalPanValueExpFull]
                change (evalPanValueExpsFull
                  (panStructConvertState context state).structs
                  (panStructConvertState context state).locals
                  (panStructConvertState context state).globals
                  (panStructConvertState context state).memory
                  (panStructConvertState context state).baseAddress
                  (panStructConvertState context state).topAddress bytesInWord
                  (structCompileExp.structCompileExps context arguments)
                  (some memoryAccess)).bind (fun convertedOperands =>
                    (convertedOperands.mapM (fun (operand : PanValue α) =>
                      match operand with | .word word => some word | _ => none)).bind
                        (fun words => Option.map PanValue.word
                          (memoryAccess.wordOp operator words))) =
                    some (panStructConvertValue (.word result))
                rw [hcompiledArgs]
                simp only [Option.bind_some]
                rw [htargetWords]
                simp [hresult, panStructConvertValue]

/-- Derived Panop-constructor specialization of HOL `compile_exp_correct`.
    HOL has only the universally quantified theorem. This untagged case keeps
    its translated context, FEVERY, FMAP_MAP2 and `struct_infos_ok` premise
    roles, with recursive argument induction hypotheses. Lean uses the
    full evaluator for source arguments, recursive IHs, and converted
    execution, sharing one explicit memory adapter. The theorem remains
    untagged because Lean uses total-function lookup/Bool adapters, explicit
    `bytesInWord` and memory access, while HOL uses finite maps and its
    fixed-width evaluator. -/
theorem panStructCompileExpCorrectPanOpCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (operator : PanOp) (arguments : List (Exp α))
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord (.panOp operator arguments)
      (memoryAccess := some memoryAccess) = some value)
    (hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (hstructInfos : structInfosOk state.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinduction : ∀ argument, argument ∈ arguments → ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord argument
        (memoryAccess := some memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context argument = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context argument) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue subvalue)) :
    structOldExpShape context (.panOp operator arguments) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.panOp operator arguments))
      (memoryAccess := some memoryAccess) =
        some (panStructConvertValue value) := by
  have hpointwise : ∀ expression, expression ∈ arguments → ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := some memoryAccess) = some subvalue →
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue subvalue) := by
    intro expression hmem subvalue heval
    exact (hinduction expression hmem subvalue heval hstructs hlocalsFields
      hglobalsFields hstructInfos hlocalsMap hglobalsMap).2.2
  cases harguments : evalPanValueExpsFull state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord arguments
      (memoryAccess := some memoryAccess) with
  | none =>
      simp [evalPanValueExpFull, harguments] at heval
  | some operands =>
      cases operands with
      | nil => simp [evalPanValueExpFull, harguments] at heval
      | cons first rest =>
          cases rest with
          | nil => simp [evalPanValueExpFull, harguments] at heval
          | cons second rest =>
              cases rest with
              | cons third rest => simp [evalPanValueExpFull, harguments] at heval
              | nil =>
                cases first with
                  | rStruct fields => simp [evalPanValueExpFull, harguments] at heval
                  | nStruct name fields => simp [evalPanValueExpFull, harguments] at heval
                  | word left =>
                    cases second with
                      | rStruct fields => simp [evalPanValueExpFull, harguments] at heval
                      | nStruct name fields => simp [evalPanValueExpFull, harguments] at heval
                      | word right =>
                        cases hoperation : evalPanOp operator [left, right] with
                        | none => simp [evalPanValueExpFull, harguments, hoperation] at heval
                        | some result =>
                            have hvalue : value = .word result := by
                              simpa [evalPanValueExpFull, harguments, hoperation] using heval.symm
                            have hcompiledArgs := panStructCompileExpsFullEvalOfPointwiseCorrect
                              context state bytesInWord
                              memoryAccess arguments
                              (.word left :: .word right :: [])
                              (by simpa using harguments) hpointwise
                            have hcompiledArgs' :
                                evalPanValueExpsFull
                                  (panStructConvertState context state).structs
                                    (panStructConvertState context state).locals
                                    (panStructConvertState context state).globals
                                    (panStructConvertState context state).memory
                                    (panStructConvertState context state).baseAddress
                                  (panStructConvertState context state).topAddress
                                    bytesInWord
                                  (structCompileExp.structCompileExps context arguments)
                                  (memoryAccess := some memoryAccess) =
                                    some [.word left, .word right] := by
                              simpa [panStructConvertValue] using hcompiledArgs
                            refine ⟨?_, ?_, ?_⟩
                            · simp [structOldExpShape, panSemShapeOf, hvalue]
                            · simp [panStructValueFieldsOkBool, hvalue]
                            · have hcompiledPanOp :
                                  structCompileExp context (.panOp operator arguments) =
                                    .panOp operator
                                      (structCompileExp.structCompileExps context arguments) := by
                                simp [structCompileExp]
                              rw [hcompiledPanOp, hvalue]
                              simp [evalPanValueExpFull, hcompiledArgs', hoperation,
                                panStructConvertValue]

/-- Derived binary Cmp-constructor specialization of HOL
    `compile_exp_correct`. The left and right recursive hypotheses retain the
    translated context, FEVERY, FMAP_MAP2, and `struct_infos_ok` premise roles
    and all three conclusions. Successful Cmp evaluation forces both
    operands to words, and compiling preserves the same `evalPanCmp` result.
    Source, both operand IHs, and converted execution use the full evaluator
    with a shared optional memory adapter. It remains untagged: HOL has only
    the universal theorem, while this Lean interface uses projected context
    views, total lookup/Bool adapters, explicit `bytesInWord`, memory access,
    and full-evaluator operation dictionaries. -/
theorem panStructCompileExpCorrectCmpCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : Option (PanValueMemoryAccess α))
    (operator : Cmp) (left right : Exp α)
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord (.cmp operator left right)
      (memoryAccess := memoryAccess) = some value)
    (hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (hstructInfos : structInfosOk state.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinductionLeft : ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord left
        (memoryAccess := memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context left = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context left) (memoryAccess := memoryAccess) =
          some (panStructConvertValue subvalue))
    (hinductionRight : ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord right
        (memoryAccess := memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context right = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context right) (memoryAccess := memoryAccess) =
          some (panStructConvertValue subvalue)) :
    structOldExpShape context (.cmp operator left right) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.cmp operator left right))
      (memoryAccess := memoryAccess) =
        some (panStructConvertValue value) := by
  cases hleft : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord left
      (memoryAccess := memoryAccess) with
  | none => simp [evalPanValueExpFull, hleft] at heval
  | some leftValue =>
      cases leftValue with
      | rStruct fields => simp [evalPanValueExpFull, hleft] at heval
      | nStruct name fields => simp [evalPanValueExpFull, hleft] at heval
      | word leftWord =>
          cases hright : evalPanValueExpFull state.structs state.locals state.globals
              state.memory state.baseAddress state.topAddress bytesInWord right
              (memoryAccess := memoryAccess) with
          | none => simp [evalPanValueExpFull, hleft, hright] at heval
          | some rightValue =>
              cases rightValue with
              | rStruct fields => simp [evalPanValueExpFull, hleft, hright] at heval
              | nStruct name fields => simp [evalPanValueExpFull, hleft, hright] at heval
              | word rightWord =>
                  let result := match memoryAccess with
                    | none => evalPanCmp operator leftWord rightWord
                    | some access => access.compare operator leftWord rightWord
                  have hvalue : value = .word result := by
                    cases memoryAccess <;>
                      simpa [evalPanValueExpFull, hleft, hright, result] using heval.symm
                  have hleftIH := hinductionLeft (.word leftWord) hleft
                    hstructs hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap
                  have hrightIH := hinductionRight (.word rightWord) hright
                    hstructs hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap
                  refine ⟨?_, ?_, ?_⟩
                  · simp [structOldExpShape, panSemShapeOf, hvalue]
                  · simp [panStructValueFieldsOkBool, hvalue]
                  · have hcompiledCmp : structCompileExp context (.cmp operator left right) =
                        .cmp operator (structCompileExp context left)
                          (structCompileExp context right) := by
                      simp [structCompileExp]
                    rw [hcompiledCmp, hvalue]
                    simp [evalPanValueExpFull, hleftIH.2.2, hrightIH.2.2,
                      panStructConvertValue, result]
                    cases memoryAccess <;> rfl

/-- Derived binary Shift-constructor specialization of HOL
    `compile_exp_correct`. The left and right recursive hypotheses retain the
    translated context, FEVERY, FMAP_MAP2, and `struct_infos_ok` premise roles
    and all three conclusions. It is now stated over the mutually recursive
    full evaluator, whose `evalPanShiftFull` implements HOL's LSL/LSR/ASR/ROR
    operations and rejects nonzero amounts at or above its configured word
    width. The theorem remains untagged because HOL has only the universal
    theorem, while Lean translates finite-map premises through projected
    context views and total lookup/Bool adapters and passes `bytesInWord`
    explicitly. A shared `PanValueMemoryAccess` supplies the evaluator's
    shift operation; the explicit compatibility premise ties that operation
    to `evalPanShiftFull` used by HOL's `word_sh`. -/
theorem panStructCompileExpCorrectShiftCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (operator : Shift) (left right : Exp α)
    (hshiftCompatible : ∀ leftWord rightWord,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord left
        (memoryAccess := some memoryAccess) = some (.word leftWord) →
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord right
        (memoryAccess := some memoryAccess) = some (.word rightWord) →
      memoryAccess.shift operator leftWord rightWord =
        evalPanShiftFull operator leftWord rightWord)
    (value : PanValue α)
    (heval : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord (.shift operator left right)
      (memoryAccess := some memoryAccess) = some value)
    (hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool state.structs state.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool state.structs state.globals)
    (hstructInfos : structInfosOk state.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.globals)
    (hinductionLeft : ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord left
        (memoryAccess := some memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context left = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context left) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue subvalue))
    (hinductionRight : ∀ subvalue,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord right
        (memoryAccess := some memoryAccess) = some subvalue →
      panStructContextShapeView context.structs = panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context right = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool state.structs subvalue = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context right) (memoryAccess := some memoryAccess) =
          some (panStructConvertValue subvalue)) :
    structOldExpShape context (.shift operator left right) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.structs value = true ∧
    evalPanValueExpFull (panStructConvertState context state).structs
      (panStructConvertState context state).locals
      (panStructConvertState context state).globals
      (panStructConvertState context state).memory
      (panStructConvertState context state).baseAddress
      (panStructConvertState context state).topAddress bytesInWord
      (structCompileExp context (.shift operator left right))
      (memoryAccess := some memoryAccess) =
        some (panStructConvertValue value) := by
  cases hleft : evalPanValueExpFull state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord left
      (memoryAccess := some memoryAccess) with
  | none => simp [evalPanValueExpFull, hleft] at heval
  | some leftValue =>
      cases leftValue with
      | rStruct fields => simp [evalPanValueExpFull, hleft] at heval
      | nStruct name fields => simp [evalPanValueExpFull, hleft] at heval
      | word leftWord =>
          cases hright : evalPanValueExpFull state.structs state.locals state.globals
              state.memory state.baseAddress state.topAddress bytesInWord right
              (memoryAccess := some memoryAccess) with
          | none => simp [evalPanValueExpFull, hleft, hright] at heval
          | some rightValue =>
              cases rightValue with
              | rStruct fields => simp [evalPanValueExpFull, hleft, hright] at heval
              | nStruct name fields => simp [evalPanValueExpFull, hleft, hright] at heval
              | word rightWord =>
                  cases hshift : evalPanShiftFull operator leftWord rightWord with
                  | none =>
                      have haccess := hshiftCompatible leftWord rightWord hleft hright
                      simp [evalPanValueExpFull, hleft, hright,
                        haccess, hshift] at heval
                  | some result =>
                      have haccess := hshiftCompatible leftWord rightWord hleft hright
                      have hvalue : value = .word result := by
                        have hsource := heval
                        simp [evalPanValueExpFull, hleft, hright,
                          haccess, hshift] at hsource
                        exact hsource.symm
                      have hleftIH := hinductionLeft (.word leftWord) hleft
                        hstructs hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap
                      have hrightIH := hinductionRight (.word rightWord) hright
                        hstructs hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap
                      refine ⟨?_, ?_, ?_⟩
                      · simp [structOldExpShape, panSemShapeOf, hvalue]
                      · simp [panStructValueFieldsOkBool, hvalue]
                      · have hcompiledShift :
                            structCompileExp context (.shift operator left right) =
                              .shift operator (structCompileExp context left)
                                (structCompileExp context right) := by
                          simp [structCompileExp]
                        rw [hcompiledShift, hvalue]
                        simp [evalPanValueExpFull, hleftIH.2.2, hrightIH.2.2,
                          haccess, hshift, panStructConvertValue]

/-! This expression-induction theorem assembles the constructor cases above
    through Lean's nested `Exp.rec`. Its public conclusions retain the three
    roles of HOL `compile_exp_correct`. It is intentionally untagged: the
    state uses total lookups and Bool adapters for HOL finite maps/`FEVERY`/
    `FMAP_MAP2`, evaluator dictionaries and `bytesInWord` are explicit, and
    the memory adapter has a Lean-specific shift-compatibility premise. -/
theorem panStructCompileExpCorrectFull
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [OfNat α 2] [OfNat α 3] [Add α] [Mul α] [Sub α]
    [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (state : PanSemState α ffi)
    (bytesInWord : α) (memoryAccess : PanValueMemoryAccess α)
    (hshiftCompatible : ∀ operator leftWord rightWord,
      memoryAccess.shift operator leftWord rightWord =
        evalPanShiftFull operator leftWord rightWord) :
    ∀ expression value,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := some memoryAccess) = some value →
      panStructContextShapeView context.structs =
        panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context expression = panSemShapeOf value ∧
      panStructValueFieldsOkBool state.structs value = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression)
        (memoryAccess := some memoryAccess) =
          some (panStructConvertValue value) := by
  let motive : Exp α → Prop := fun expression =>
    ∀ value,
      evalPanValueExpFull state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress bytesInWord expression
        (memoryAccess := some memoryAccess) = some value →
      panStructContextShapeView context.structs =
        panStructContextShapeView state.structs →
      panStructEveryValueFieldsOkBool state.structs state.locals →
      panStructEveryValueFieldsOkBool state.structs state.globals →
      structInfosOk state.structs →
      panStructShapeMapEq context.locals state.locals →
      panStructShapeMapEq context.globals state.globals →
      structOldExpShape context expression = panSemShapeOf value ∧
      panStructValueFieldsOkBool state.structs value = true ∧
      evalPanValueExpFull (panStructConvertState context state).structs
        (panStructConvertState context state).locals
        (panStructConvertState context state).globals
        (panStructConvertState context state).memory
        (panStructConvertState context state).baseAddress
        (panStructConvertState context state).topAddress bytesInWord
        (structCompileExp context expression)
        (memoryAccess := some memoryAccess) =
          some (panStructConvertValue value)
  intro expression
  refine Exp.rec (motive_1 := motive)
    (motive_2 := fun expressions => PanStructAll motive expressions)
    (motive_3 := fun fields => PanStructAll motive (fields.map Prod.snd))
    (motive_4 := fun field => motive field.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression
  · intro constant value heval hstructs hlocals hglobals hinfos hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectConstCase context state bytesInWord
      (some memoryAccess) constant value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
  · intro kind name value heval hstructs hlocals hglobals hinfos hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectVarCase context state bytesInWord
      (some memoryAccess) name kind value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
  · intro expressions hinduction value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectRStructCase context state bytesInWord
      memoryAccess expressions value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap hinduction
  · intro index subexpression ih value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectRFieldCase context state bytesInWord
      (some memoryAccess) index subexpression value heval hstructs hlocals hglobals
      hinfos hlocalsMap hglobalsMap ih
  · intro name fields hinduction value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectNStructCase context state bytesInWord
      memoryAccess name fields value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap hinduction
  · intro field subexpression ih value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectNFieldCase context state bytesInWord
      (some memoryAccess) field subexpression value heval hstructs hlocals hglobals
      hinfos hlocalsMap hglobalsMap ih
  · intro shape address ih value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
    have addressIH : ∀ addressValue,
        evalPanValueExpFull state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord address
          (memoryAccess := some memoryAccess) = some addressValue →
        structOldExpShape context address = panSemShapeOf addressValue ∧
        panStructValueFieldsOkBool state.structs addressValue = true ∧
        evalPanValueExpFull (panStructConvertState context state).structs
          (panStructConvertState context state).locals
          (panStructConvertState context state).globals
          (panStructConvertState context state).memory
          (panStructConvertState context state).baseAddress
          (panStructConvertState context state).topAddress bytesInWord
          (structCompileExp context address) (memoryAccess := some memoryAccess) =
            some (panStructConvertValue addressValue) := by
      intro addressValue haddress
      exact ih addressValue haddress hstructs hlocals hglobals hinfos
        hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectLoadCase context state bytesInWord
      memoryAccess shape address value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap addressIH
  · intro address ih value heval hstructs hlocals hglobals hinfos hlocalsMap hglobalsMap
    have addressIH : ∀ addressValue,
        evalPanValueExpFull state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord address
          (memoryAccess := some memoryAccess) = some addressValue →
        structOldExpShape context address = panSemShapeOf addressValue ∧
        panStructValueFieldsOkBool state.structs addressValue = true ∧
        evalPanValueExpFull (panStructConvertState context state).structs
          (panStructConvertState context state).locals
          (panStructConvertState context state).globals
          (panStructConvertState context state).memory
          (panStructConvertState context state).baseAddress
          (panStructConvertState context state).topAddress bytesInWord
          (structCompileExp context address) (memoryAccess := some memoryAccess) =
            some (panStructConvertValue addressValue) := by
      intro addressValue haddress
      exact ih addressValue haddress hstructs hlocals hglobals hinfos
        hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectLoad32Case context state bytesInWord
      memoryAccess address value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap addressIH
  · intro address ih value heval hstructs hlocals hglobals hinfos hlocalsMap hglobalsMap
    have addressIH : ∀ addressValue,
        evalPanValueExpFull state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord address
          (memoryAccess := some memoryAccess) = some addressValue →
        structOldExpShape context address = panSemShapeOf addressValue ∧
        panStructValueFieldsOkBool state.structs addressValue = true ∧
        evalPanValueExpFull (panStructConvertState context state).structs
          (panStructConvertState context state).locals
          (panStructConvertState context state).globals
          (panStructConvertState context state).memory
          (panStructConvertState context state).baseAddress
          (panStructConvertState context state).topAddress bytesInWord
          (structCompileExp context address) (memoryAccess := some memoryAccess) =
            some (panStructConvertValue addressValue) := by
      intro addressValue haddress
      exact ih addressValue haddress hstructs hlocals hglobals hinfos
        hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectLoadByteCase context state bytesInWord
      memoryAccess address value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap addressIH
  · intro operator arguments hinduction value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
    have ihPointwise : ∀ argument, argument ∈ arguments → ∀ subvalue,
        evalPanValueExpFull state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord argument
          (memoryAccess := some memoryAccess) = some subvalue →
        panStructContextShapeView context.structs =
          panStructContextShapeView state.structs →
        panStructEveryValueFieldsOkBool state.structs state.locals →
        panStructEveryValueFieldsOkBool state.structs state.globals →
        structInfosOk state.structs →
        panStructShapeMapEq context.locals state.locals →
        panStructShapeMapEq context.globals state.globals →
        structOldExpShape context argument = panSemShapeOf subvalue ∧
        panStructValueFieldsOkBool state.structs subvalue = true ∧
        evalPanValueExpFull (panStructConvertState context state).structs
          (panStructConvertState context state).locals
          (panStructConvertState context state).globals
          (panStructConvertState context state).memory
          (panStructConvertState context state).baseAddress
          (panStructConvertState context state).topAddress bytesInWord
          (structCompileExp context argument) (memoryAccess := some memoryAccess) =
            some (panStructConvertValue subvalue) := by
      intro argument hmem subvalue heval'
      have ihArgument := panStructAll_mem hinduction argument hmem
      intro hstructs' hlocals' hglobals' hinfos' hlocalsMap' hglobalsMap'
      exact ihArgument subvalue heval' hstructs' hlocals' hglobals' hinfos'
        hlocalsMap' hglobalsMap'
    exact panStructCompileExpCorrectOpCase context state bytesInWord
      memoryAccess operator arguments value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap ihPointwise
  · intro operator arguments hinduction value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
    have ihPointwise : ∀ argument, argument ∈ arguments → ∀ subvalue,
        evalPanValueExpFull state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord argument
          (memoryAccess := some memoryAccess) = some subvalue →
        panStructContextShapeView context.structs =
          panStructContextShapeView state.structs →
        panStructEveryValueFieldsOkBool state.structs state.locals →
        panStructEveryValueFieldsOkBool state.structs state.globals →
        structInfosOk state.structs →
        panStructShapeMapEq context.locals state.locals →
        panStructShapeMapEq context.globals state.globals →
        structOldExpShape context argument = panSemShapeOf subvalue ∧
        panStructValueFieldsOkBool state.structs subvalue = true ∧
        evalPanValueExpFull (panStructConvertState context state).structs
          (panStructConvertState context state).locals
          (panStructConvertState context state).globals
          (panStructConvertState context state).memory
          (panStructConvertState context state).baseAddress
          (panStructConvertState context state).topAddress bytesInWord
          (structCompileExp context argument) (memoryAccess := some memoryAccess) =
            some (panStructConvertValue subvalue) := by
      intro argument hmem subvalue heval'
      have ihArgument := panStructAll_mem hinduction argument hmem
      intro hstructs' hlocals' hglobals' hinfos' hlocalsMap' hglobalsMap'
      exact ihArgument subvalue heval' hstructs' hlocals' hglobals' hinfos'
        hlocalsMap' hglobalsMap'
    exact panStructCompileExpCorrectPanOpCase context state bytesInWord
      memoryAccess operator arguments value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap ihPointwise
  · intro operator left right ihLeft ihRight value heval hstructs hlocals
      hglobals hinfos hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectCmpCase context state bytesInWord
      (some memoryAccess) operator left right value heval hstructs hlocals hglobals
      hinfos hlocalsMap hglobalsMap ihLeft ihRight
  · intro operator left right ihLeft ihRight value heval hstructs hlocals
      hglobals hinfos hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectShiftCase context state bytesInWord
      memoryAccess operator left right
      (fun leftWord rightWord _ _ => hshiftCompatible operator leftWord rightWord)
      value heval hstructs hlocals hglobals hinfos hlocalsMap hglobalsMap
      ihLeft ihRight
  · intro value heval hstructs hlocals hglobals hinfos hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectBaseAddrCase context state bytesInWord
      (some memoryAccess) value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
  · intro value heval hstructs hlocals hglobals hinfos hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectTopAddrCase context state bytesInWord
      (some memoryAccess) value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
  · intro value heval hstructs hlocals hglobals hinfos hlocalsMap hglobalsMap
    exact panStructCompileExpCorrectBytesInWordCase context state bytesInWord
      (some memoryAccess) value heval hstructs hlocals hglobals hinfos
      hlocalsMap hglobalsMap
  · exact PanStructAll.nil
  · intro head tail ihHead ihTail
    exact PanStructAll.cons ihHead ihTail
  · exact PanStructAll.nil
  · intro head tail ihHead ihTail
    simpa using PanStructAll.cons ihHead ihTail
  · intro fieldName subexpression ih
    exact ih

end Flapjack
