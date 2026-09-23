import Flapjack.HolRef
import Flapjack.Pancake.PanStructs

/-!
Proof lemmas for CakeML Pancake's `pan_structs` theory.

The `afindi` results below are ports of declarations from
`cakeml/pancake/proofs/pan_structsProofScript.sml`. Helpers whose Lean
statements use different equality or indexing APIs are kept untagged and their
translation limits are documented at the declarations.
-/

namespace Flapjack

/-- HOL's local `compile_exps_eq_map` (`pan_structsProofScript.sml:11`): the
    production recursive helper used by `structCompileExp` maps the production
    single-expression compiler over the list. `List.map` represents HOL `MAP`;
    `[BEq String]` is the typeclass needed by the Lean implementation's lookup. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exps_eq_map" 11]
theorem structCompileExps_eq_map {α : Type} [BEq String] (context : StructPassContext) :
    (structCompileExp.structCompileExps (α := α) context :
      List (Exp α) → List (Exp α)) =
      fun expressions => expressions.map (structCompileExp context) := by
  funext expressions
  induction expressions with
  | nil => simp [structCompileExp.structCompileExps]
  | cons expression expressions ih =>
      simp [structCompileExp.structCompileExps, ih]

/-- Fuel-indexed analogue of HOL `compile_shapes_eq_map`
    (`pan_structsProofScript.sml:310`). The HOL statement has no fuel
    parameter and concerns mutually recursive `compile_shape`/`compile_shapes`.
    This auxiliary helper theorem is deliberately untagged; the production
    no-fuel theorem `structCompileShapes_eq_map` below establishes the exact
    HOL statement instead. -/
theorem structCompileShapesFuel_eq_map (fuel : Nat) (context : StructContext) :
    (structCompileShapeFuel.structCompileShapesFuel fuel context : List Shape → List Shape) =
      fun shapes => shapes.map (structCompileShapeFuel fuel context) := by
  funext shapes
  induction shapes with
  | nil => simp [structCompileShapeFuel.structCompileShapesFuel]
  | cons shape shapes ih =>
      simp [structCompileShapeFuel.structCompileShapesFuel, ih]

/-- Exact no-fuel port of HOL `compile_shapes_eq_map`
    (`pan_structsProofScript.sml:310`). The production mutually recursive
    compiler decreases on the HOL context-suffix/syntax-size measure, so this
    statement keeps the source theorem's context and list arguments unchanged. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shapes_eq_map" 310]
theorem structCompileShapes_eq_map (context : StructContext) :
    (structCompileShapeWF.structCompileShapesWF context : List Shape → List Shape) =
      fun shapes => shapes.map (structCompileShapeWF context) := by
  funext shapes
  induction shapes with
  | nil => simp [structCompileShapeWF.structCompileShapesWF]
  | cons shape shapes ih =>
      simp [structCompileShapeWF.structCompileShapesWF, ih]

/-- HOL's mutual `is_wf_shape_compile_shape`
    (`pan_structsProofScript.sml:298`): compiling a shape, or a list of
    shapes, removes every `Named` constructor, so the result is well formed in
    any outer structure context. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "is_wf_shape_compile_shape" 298]
theorem structCompileShapeWF_isWfShape [BEq String]
    (outer : StructContext) :
    (∀ (context : StructContext) (shape : Shape),
      isWfShape outer (structCompileShapeWF context shape) = true) ∧
    (∀ (context : StructContext) (shapes : List Shape),
      isWfShape.isWfShapeList outer
        (structCompileShapeWF.structCompileShapesWF context shapes) = true) := by
  have hshape : ∀ (context : StructContext) (shape : Shape),
      isWfShape outer (structCompileShapeWF context shape) = true := by
    intro context shape
    apply structCompileShapeWF.induct
      (motive1 := fun context shapes =>
        isWfShape.isWfShapeList outer
          (structCompileShapeWF.structCompileShapesWF context shapes) = true)
      (motive2 := fun context shape =>
        isWfShape outer (structCompileShapeWF context shape) = true)
    · intro context
      simp [structCompileShapeWF.structCompileShapesWF, isWfShape.isWfShapeList]
    · intro context shape shapes ihShape ihShapes
      simp only [structCompileShapeWF.structCompileShapesWF,
        isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨ihShape, ihShapes⟩
    · intro context
      simp [structCompileShapeWF, isWfShape]
    · intro context shapes ih
      simp only [structCompileShapeWF, isWfShape]
      exact ih
    · intro context name info suffix hlookup ih
      rw [structCompileShapeWF.eq_def]
      dsimp only
      rw [hlookup]
      simp [isWfShape]
      exact ih
    · intro context name hlookup
      rw [structCompileShapeWF.eq_def]
      dsimp only
      rw [hlookup]
      simp [isWfShape]
  constructor
  · exact hshape
  · intro context shapes
    rw [structCompileShapes_eq_map]
    induction shapes with
    | nil => simp [isWfShape.isWfShapeList]
    | cons shape shapes ih =>
        simp only [List.map_cons, isWfShape.isWfShapeList, Bool.and_eq_true]
        exact ⟨hshape context shape, ih⟩

/-- HOL's `old_exp_shapes_eq` (`pan_structsProofScript.sml:679`): the
    production old-shape list helper equals `MAP` of the production
    single-expression old-shape function, with no additional premises. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "old_exp_shapes_eq" 679]
theorem structOldExpShapes_eq_map {α : Type} (context : StructPassContext) :
    (structOldExpShape.structOldExpShapes (α := α) context :
      List (Exp α) → List Shape) =
      fun expressions => expressions.map (structOldExpShape context) := by
  funext expressions
  induction expressions with
  | nil => simp [structOldExpShape.structOldExpShapes]
  | cons expression expressions ih =>
      simp [structOldExpShape.structOldExpShapes, ih]

/-- Cake's `opt_mmap_eq_some_el`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:19`). The `getElem?`
    formulation is the total Lean translation of HOL's total `EL`: under the
    in-range premise, each optional lookup succeeds and supplies that element. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "opt_mmap_eq_some_el"]
theorem optMmapEqSomeEl {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔
      xs.length = ys.length ∧ ∀ n, n < ys.length → (xs[n]?).bind f = ys[n]? := by
  induction xs generalizing ys with
  | nil =>
      constructor
      · intro h
        cases h
        simp
      · intro h
        obtain ⟨hlen, _⟩ := h
        have : ys = [] := by simpa using hlen.symm
        subst this
        rfl
  | cons x xs ih =>
      rw [List.mapM_cons]
      constructor
      · intro h
        cases hx : f x with
        | none => simp [hx] at h
        | some b =>
            simp only [hx] at h
            cases hxs : xs.mapM f with
            | none => simp [hxs] at h
            | some ys' =>
                simp only [hxs] at h
                have hb : b :: ys' = ys := by simpa using h
                subst hb
                obtain ⟨hlen, hpt⟩ := (ih ys').mp hxs
                refine ⟨by simp [hlen], ?_⟩
                intro n hn
                cases n with
                | zero => simp [hx]
                | succ m =>
                    simp only [List.getElem?_cons_succ, List.length_cons] at hn ⊢
                    have hm : m < ys'.length := by omega
                    simpa using hpt m hm
      · intro h
        obtain ⟨hlen, hpt⟩ := h
        cases ys with
        | nil => simp at hlen
        | cons b ys' =>
            have hfx : f x = some b := by
              have := hpt 0 (by simp)
              simpa using this
            have htail : xs.length = ys'.length ∧
                ∀ n, n < ys'.length → (xs[n]?).bind f = ys'[n]? := by
              refine ⟨by simpa using hlen, ?_⟩
              intro n hn
              have := hpt (n + 1) (by simp; omega)
              simpa [List.getElem?_cons_succ] using this
            have hxs : xs.mapM f = some ys' := (ih ys').mpr htail
            simp [hfx, hxs]

/-! Faithful port of Cake `afindi_less_length`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:345`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_less_length"]
theorem afindi_less_length [DecidableEq α] (key : α) :
    ∀ (entries : List (α × β)) (index : Nat),
      afindi key entries = some index → index < entries.length := by
  intro entries
  induction entries with
  | nil =>
      intro index h
      simp [afindi] at h
  | cons entry rest ih =>
      intro index h
      obtain ⟨candidate, value⟩ := entry
      simp only [afindi] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp
      · split at h
        · simp at h
        · rename_i found hfound
          simp only [Option.some.injEq] at h
          subst h
          have hlt := ih found hfound
          simp only [List.length_cons]
          omega

/-! Faithful Lean indexing form of Cake `afindi_EL`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:430`). Given the
    successful search, `getElem?` is `some` exactly at the in-range `EL` index. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_EL"]
theorem afindi_el_fst [DecidableEq α] (key : α) :
    ∀ (entries : List (α × β)) (index : Nat),
      afindi key entries = some index →
        (entries[index]?).map Prod.fst = some key := by
  intro entries
  induction entries with
  | nil =>
      intro index h
      simp [afindi] at h
  | cons entry rest ih =>
      intro index h
      obtain ⟨candidate, value⟩ := entry
      simp only [afindi] at h
      split at h
      · rename_i hbeq
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.getElem?_cons_zero, Option.map_some]
        exact congrArg some hbeq.symm
      · split at h
        · simp at h
        · rename_i found hfound
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.getElem?_cons_succ]
          exact ih found hfound

/-! Faithful port of Cake `afindi_append`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:417`). The source uses
    `LENGTH xs + index`; this Lean statement writes the commuted Nat sum. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_append"]
theorem afindi_append [DecidableEq α] (key : α) (xs ys : List (α × β)) :
    afindi key (xs ++ ys) =
      (match afindi key xs with
        | none => (afindi key ys).map (fun index => index + xs.length)
        | some index => some index) := by
  induction xs with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key = candidate
      · simp [afindi, hbeq]
      · simp only [List.cons_append, afindi, hbeq]
        rw [ih]
        cases ha : afindi key rest with
        | none =>
            cases hb : afindi key ys with
            | none => simp
            | some index => simp; omega
        | some index => simp

/-! Faithful port of Cake `afindi_MAP_eq`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:356`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_MAP_eq"]
theorem afindi_map_eq [DecidableEq α] (key : α) (f : α × β → α × γ)
    (entries : List (α × β))
    (hf : ∀ x y, (x, y) ∈ entries → (f (x, y)).1 = x) :
    afindi key (entries.map f) = afindi key entries := by
  induction entries with
  | nil => simp only [List.map_nil, afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      have hhead : (f (candidate, value)).1 = candidate :=
        hf candidate value (by simp)
      have htail : ∀ x y, (x, y) ∈ rest → (f (x, y)).1 = x :=
        fun x y hxy => hf x y (by simp [hxy])
      simp only [List.map_cons]
      rw [afindi_cons, afindi_cons, hhead, ih htail]

/-! Faithful API translation of Cake `dropWhile_afindi`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:334`). HOL's logical
    inequality predicate is expressed with `decide` for Lean's Bool-valued
    `List.dropWhile`; HOL `DROP` translates to `List.drop`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "dropWhile_afindi"]
theorem afindi_dropWhile [DecidableEq α] (key : α) (entries : List (α × β)) :
    entries.dropWhile (fun entry => decide (key ≠ entry.1)) =
      match afindi key entries with
      | none => []
      | some index => entries.drop index := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hb : key = candidate
      · simp [afindi_cons, hb]
      · have hdec : decide (key ≠ candidate) = true := by simp [hb]
        simp only [List.dropWhile_cons, afindi_cons, hdec, if_neg hb]
        rw [ih]
        cases afindi key rest with
        | none => simp
        | some index => simp [List.drop_succ_cons]

/-! Faithful API translation of Cake `ALOOKUP_eq_afindi`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:405`). `List.lookup`
    translates `ALOOKUP`; the optional indexed projection translates HOL's
    `OPTION_MAP` of `SND ∘ EL`, with `afindi_less_length` ensuring successful
    indices are in range. Its synthesized `BEq` comes from `DecidableEq`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "ALOOKUP_eq_afindi"]
theorem afindi_lookup [DecidableEq α] (key : α) (entries : List (α × β)) :
    entries.lookup key =
      (afindi key entries).bind (fun index => (entries[index]?).map Prod.snd) := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key = candidate
      · simp [afindi_cons, hbeq]
      · have hbeq' : (key == candidate) = false := by
          simp [BEq.beq, hbeq]
        simp only [List.lookup_cons, hbeq', afindi_cons, if_neg hbeq]
        rw [ih]
        cases afindi key rest with
        | none => simp
        | some index => simp [List.getElem?_cons_succ]

/-! Lean list-lookup adaptation of Cake's local `alookup_drop_helper`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:78`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "alookup_drop_helper"]
theorem lookup_drop_helper [DecidableEq α]
    (n : Nat) (xs : List (α × β)) (key : α) (value : β)
    (hlookup : List.lookup key (xs.drop n) = some value)
    (hnodup : (xs.map Prod.fst).Nodup) :
    key ∉ (xs.take n).map Prod.fst ∧ List.lookup key xs = some value := by
  have hmem_drop : key ∈ (xs.drop n).map Prod.fst := by
    obtain ⟨l₁, l₂, heq, _⟩ :=
      (List.lookup_eq_some_iff (l := xs.drop n) (k := key) (b := value)).mp hlookup
    exact List.mem_map.mpr ⟨(key, value), by rw [heq]; simp, rfl⟩
  have hmap : xs.map Prod.fst =
      (xs.take n).map Prod.fst ++ (xs.drop n).map Prod.fst := by
    rw [← List.map_append, List.take_append_drop]
  have hnodup' : ((xs.take n).map Prod.fst ++ (xs.drop n).map Prod.fst).Nodup := by
    rw [← hmap]; exact hnodup
  have hnot_mem : key ∉ (xs.take n).map Prod.fst := by
    intro hk
    exact (List.nodup_append.mp hnodup').2.2 key hk key hmem_drop rfl
  refine ⟨hnot_mem, ?_⟩
  have htake_none : List.lookup key (xs.take n) = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    rw [bne_iff_ne]
    intro hkp
    exact hnot_mem (List.mem_map.mpr ⟨p, hp, hkp.symm⟩)
  have h1 := List.lookup_append (l₁ := xs.take n) (l₂ := xs.drop n) (k := key)
  rw [htake_none] at h1
  simp only [Option.none_or] at h1
  rw [← List.take_append_drop n xs, h1]
  exact hlookup

/-! Helper for Cake's local `map_fst_eq_alookup`: equal key lists imply
    identical `afindi` positions. This intermediate theorem is not a separate
    HOL declaration, so it has no `@[hol]` tag. -/
theorem afindi_eq_of_map_fst_eq [DecidableEq α] (key : α) :
    ∀ (xs ys : List (α × β)), xs.map Prod.fst = ys.map Prod.fst →
      afindi key xs = afindi key ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      simp only [List.map_nil] at h
      have hy : ys = [] := (List.map_eq_nil_iff.mp h.symm)
      subst hy
      simp [afindi]
  | cons x xs ih =>
      intro ys h
      obtain ⟨cx, vx⟩ := x
      cases ys with
      | nil => simp at h
      | cons y ys =>
          obtain ⟨cy, vy⟩ := y
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hhead, htail⟩ := h
          have hcy : cx = cy := hhead
          subst hcy
          by_cases hbc : key = cx
          · rw [afindi_cons key (cx, vx) xs, afindi_cons key (cx, vy) ys,
              if_pos hbc, if_pos hbc]
          · rw [afindi_cons key (cx, vx) xs, afindi_cons key (cx, vy) ys,
              if_neg hbc, if_neg hbc, ih ys htail]

/-! Lean option-indexing adaptation of Cake's local `map_fst_eq_alookup`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:278`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "map_fst_eq_alookup"]
theorem map_fst_eq_lookup
    (xs ys : List (String × β)) (nm : String) {v : β}
    (hlen : xs.map Prod.fst = ys.map Prod.fst)
    (hlookup : xs.lookup nm = some v) :
    ∃ i, afindi nm xs = some i ∧ afindi nm ys = some i ∧
      i < xs.length ∧ i < ys.length ∧
      (xs[i]?).map Prod.snd = some v ∧ (ys[i]?).map Prod.snd = ys.lookup nm := by
  have hafindi := afindi_eq_of_map_fst_eq nm xs ys hlen
  have hbridge := afindi_lookup nm xs
  rw [hlookup] at hbridge
  cases h : afindi nm xs with
  | none =>
      rw [h] at hbridge
      simp at hbridge
  | some i =>
      rw [h] at hbridge
      simp only [Option.bind_some] at hbridge
      have hxs : (xs[i]?).map Prod.snd = some v := hbridge.symm
      have hi_xs : i < xs.length := afindi_less_length nm xs i h
      have hys : afindi nm ys = some i := by rw [← hafindi]; exact h
      have hi_ys : i < ys.length := afindi_less_length nm ys i hys
      have hybridge := afindi_lookup nm ys
      rw [hys] at hybridge
      simp only [Option.bind_some] at hybridge
      refine ⟨i, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · exact hys
      · exact hi_xs
      · exact hi_ys
      · exact hxs
      · exact hybridge.symm

end Flapjack
