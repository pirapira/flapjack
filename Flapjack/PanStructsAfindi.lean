import Flapjack.Static

/-!
Faithful executable port of CakeML Pancake's `pan_structs$afindi` helper.
`afindi` returns the first zero-based position of a key in an association
list, preserving the original first-match behavior on duplicate keys.
-/

namespace Flapjack

def afindi [BEq α] (key : α) : List (α × β) → Option Nat
  | [] => none
  | (candidate, _) :: entries =>
      if key == candidate then some 0
      else match afindi key entries with
        | none => none
        | some index => some (index + 1)
termination_by entries => sizeOf entries
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial

/-! CakeML `pan_structsProofScript.sml` lemmas about `afindi`
    (`afindi_less_length`, `afindi_EL`, `afindi_append`, `afindi_MAP_eq`). -/

theorem afindi_cons [BEq α] (key : α) (entry : α × β) (rest : List (α × β)) :
    afindi key (entry :: rest) =
      if key == entry.1 then some 0
      else match afindi key rest with
        | none => none
        | some index => some (index + 1) := by
  obtain ⟨candidate, value⟩ := entry
  simp [afindi]

theorem afindi_less_length [BEq α] (key : α) :
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

theorem afindi_el_fst [BEq α] [LawfulBEq α] (key : α) :
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
        exact congrArg some (eq_of_beq hbeq).symm
      · split at h
        · simp at h
        · rename_i found hfound
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.getElem?_cons_succ]
          exact ih found hfound

theorem afindi_append [BEq α] (key : α) (xs ys : List (α × β)) :
    afindi key (xs ++ ys) =
      (match afindi key xs with
        | none => (afindi key ys).map (fun index => index + xs.length)
        | some index => some index) := by
  induction xs with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key == candidate
      · simp [afindi, hbeq]
      · simp only [List.cons_append, afindi, hbeq]
        rw [ih]
        cases ha : afindi key rest with
        | none =>
            cases hb : afindi key ys with
            | none => simp
            | some index => simp; omega
        | some index => simp

theorem afindi_map_eq [BEq α] (key : α) (f : α × β → α × γ)
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

theorem afindi_dropWhile [BEq α] (key : α) (entries : List (α × β)) :
    entries.dropWhile (fun entry => !(key == entry.1)) =
      match afindi key entries with
      | none => []
      | some index => entries.drop index := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      cases hb : (key == candidate) with
      | true => simp [afindi_cons, hb]
      | false =>
          simp only [List.dropWhile_cons, afindi_cons, hb]
          rw [ih]
          cases afindi key rest with
          | none => simp
          | some index => simp [List.drop_succ_cons]

theorem afindi_lookup [BEq α] (key : α) (entries : List (α × β)) :
    entries.lookup key =
      (afindi key entries).bind (fun index => (entries[index]?).map Prod.snd) := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key == candidate
      · simp [List.lookup_cons, afindi_cons, hbeq]
      · simp only [List.lookup_cons, hbeq, afindi_cons]
        rw [ih]
        cases afindi key rest with
        | none => simp
        | some index => simp [List.getElem?_cons_succ]
/-! CakeML `pan_structsProofScript.sml` `is_wf_shape_drop`: dropping a prefix
    of the struct context preserves well-formedness of a shape, because a name
    found in the suffix is also found (at least as far left) in the whole
    context. -/

theorem lookupInfo_isSome_drop (name : String) (context : StructContext) (n : Nat) :
    (lookupInfo name (context.drop n)).isSome = true →
      (lookupInfo name context).isSome = true := by
  induction context generalizing n with
  | nil => cases n <;> simp [lookupInfo]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      cases n with
      | zero => simp
      | succ m =>
          simp only [List.drop_succ_cons]
          intro h
          have hrest := ih m h
          by_cases hc : candidate == name
          · simp [lookupInfo, hc]
          · simp only [lookupInfo, hc]
            exact hrest

theorem isWfShape_drop (shape : Shape) (context : StructContext) (n : Nat) :
    isWfShape (context.drop n) shape = true → isWfShape context shape = true :=
  (isWfShape.induct
    (motive1 := fun shapes => ∀ (context : StructContext) (n : Nat),
      isWfShape.isWfShapeList (context.drop n) shapes = true →
        isWfShape.isWfShapeList context shapes = true)
    (motive2 := fun shape => ∀ (context : StructContext) (n : Nat),
      isWfShape (context.drop n) shape = true → isWfShape context shape = true)
    (by intro context n _; simp [isWfShape.isWfShapeList])
    (by
      intro shape shapes ih1 ih2 context n h
      simp only [isWfShape.isWfShapeList, Bool.and_eq_true] at h ⊢
      exact ⟨ih1 context n h.1, ih2 context n h.2⟩)
    (by intro context n _; simp [isWfShape])
    (by
      intro shapes ih context n h
      have h' : isWfShape.isWfShapeList (context.drop n) shapes = true := by
        simpa [isWfShape] using h
      simpa [isWfShape] using ih context n h')
    (by
      intro name context n h
      simp only [isWfShape] at h ⊢
      exact lookupInfo_isSome_drop name context n h))
    shape context n

/-! CakeML `pan_structsProofScript.sml` `alookup_drop_helper`: a successful
    lookup in a suffix `DROP n xs` of a context with distinct keys is also a
    successful lookup in the whole context, and the key does not occur in the
    dropped prefix. -/

theorem lookup_drop_helper [BEq α] [LawfulBEq α]
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

/-- Cake `pan_structs` `map_uncurry_zip_again`: mapping an uncurried pair
constructor over a `zip` equals the `zip` of the two maps. -/
theorem list_zip_map_eq {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    (xs.zip ys).map (fun p => (f p.1, g p.2)) = (xs.map f).zip (ys.map g) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zip_cons_cons, List.map_cons, List.length_cons] at h ⊢
          have h' : xs.length = ys.length := by omega
          rw [ih ys h']

/-- Cake `pan_structs` `UNCURRY_EQ_o_SND`: an uncurried constant pair
function is the constant composed with `SND`. -/
theorem prod_uncurry_const_eq_comp_snd {α β γ : Type} (f : β → γ) :
    Function.uncurry (fun _ : α => f) = f ∘ Prod.snd := by
  funext p
  cases p
  rfl

/-- `lookupInfo` is the `List.lookup` of the underlying association list. -/
theorem lookupInfo_eq_lookup (name : String) (entries : InfoMap α) :
    lookupInfo name entries = List.lookup name entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨candidate, value⟩ := entry
      simp only [lookupInfo, List.lookup_cons, ih]
      by_cases h : (candidate == name) = true
      · have h' : (name == candidate) = true := by
          rw [beq_iff_eq] at h ⊢
          exact h.symm
        simp [h, h']
      · have h' : (name == candidate) = false :=
          beq_eq_false_iff_ne.mpr (fun hc => h (beq_iff_eq.mpr hc.symm))
        simp [h, h']

/-- Cake `pan_structs` `alookup_drop_helper` specialised to `lookupInfo`:
a hit in a suffix survives dropping the prefix, provided the keys are distinct. -/
theorem lookupInfo_drop_helper (n : Nat)
    (context : StructContext) (name : String) (info : StructInfo)
    (hlookup : lookupInfo name (context.drop n) = some info)
    (hnodup : (context.map Prod.fst).Nodup) :
    lookupInfo name context = some info := by
  rw [lookupInfo_eq_lookup] at hlookup ⊢
  exact (lookup_drop_helper n context name info hlookup hnodup).2

/-- A member of a well-formed shape list is itself a well-formed shape. -/
theorem isWfShape_of_mem {context : StructContext} {shapes : List Shape} {shape : Shape}
    (h : isWfShape.isWfShapeList context shapes = true) (hmem : shape ∈ shapes) :
    isWfShape context shape = true := by
  induction shapes with
  | nil => simp at hmem
  | cons s ss ih =>
      simp only [isWfShape.isWfShapeList, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact h.1
      · exact ih h.2 hmem'

/-- Cake `pan_structs` `size_of_sh_with_ctxt_drop`: dropping a prefix of the
structure context preserves the shape size, provided the remaining context
still witnesses the shape and the context keys are distinct. -/
theorem shapeSizeWithContext_drop (n : Nat) (context : StructContext) (shape : Shape)
    (h : isWfShape (context.drop n) shape = true)
    (hnodup : (context.map Prod.fst).Nodup) :
    shapeSizeWithContext (context.drop n) shape = shapeSizeWithContext context shape := by
  revert h hnodup
  induction shape using shapeSizeWithContext.induct with
  | case1 => intro _ _; simp only [shapeSizeWithContext]
  | case2 shapes ih =>
      intro h hnodup
      have hlist : isWfShape.isWfShapeList (context.drop n) shapes = true := by
        simpa [isWfShape] using h
      have hpoint : ∀ s ∈ shapes,
          shapeSizeWithContext (context.drop n) s = shapeSizeWithContext context s :=
        fun s hs => ih s hs (isWfShape_of_mem hlist hs) hnodup
      have hfold : ∀ (l : List Shape),
          (∀ s ∈ l, shapeSizeWithContext (context.drop n) s = shapeSizeWithContext context s) →
          ∀ acc, l.foldl (fun total shape => total + shapeSizeWithContext (context.drop n) shape) acc =
              l.foldl (fun total shape => total + shapeSizeWithContext context shape) acc := by
        intro l
        induction l with
        | nil => intro _ acc; rfl
        | cons s ss ihs =>
            intro hl acc
            simp only [List.foldl_cons]
            rw [hl s (by simp)]
            exact ihs (fun t ht => hl t (by simp [ht])) (acc + shapeSizeWithContext context s)
      simp only [shapeSizeWithContext]
      exact hfold shapes hpoint 0
  | case3 name =>
      intro h hnodup
      have hsome : (lookupInfo name (context.drop n)).isSome = true := by
        simpa [isWfShape] using h
      cases hlk : lookupInfo name (context.drop n) with
      | none => simp [hlk] at hsome
      | some info =>
          have hctx := lookupInfo_drop_helper n context name info hlk hnodup
          simp only [shapeSizeWithContext, hlk, hctx]

/-- Cake's `dropWhile_eq_cons_IMP`
(`cakeml/pancake/semantics/panPropsScript.sml:74-86`): if `dropWhile P xs`
returns a nonempty list headed by `y`, then `y` is some element of `xs` at
which `P` first fails, and `drop` at that index yields the same tail. -/
theorem dropWhile_eq_cons_imp {α : Type} (P : α → Bool) (xs : List α)
    (y : α) (ys : List α) (h : xs.dropWhile P = y :: ys) :
    ∃ n, n < xs.length ∧ xs[n]? = some y ∧ P y = false ∧ xs.drop n = y :: ys := by
  induction xs generalizing y ys with
  | nil => simp at h
  | cons x rest ih =>
      cases hP : P x with
      | false =>
          simp only [List.dropWhile_cons, hP, Bool.false_eq_true, if_false] at h
          cases h
          exact ⟨0, by simp, by simp, hP, by simp⟩
      | true =>
          simp only [List.dropWhile_cons, hP, if_true] at h
          obtain ⟨n, hn, hget, hpy, hdrop⟩ := ih y ys h
          refine ⟨n + 1, by simpa using hn, ?_, hpy, ?_⟩
          · simpa [List.getElem?_cons_succ] using hget
          · simpa [List.drop_succ_cons] using hdrop

theorem lookupInfoWithRest_length_lt [BEq String] {name : String}
    {context : StructContext} {info : StructInfo} {rest : StructContext}
    (h : lookupInfoWithRest name context = some (info, rest)) :
    rest.length < context.length := by
  induction context with
  | nil => simp [lookupInfoWithRest] at h
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      simp only [lookupInfoWithRest] at h
      by_cases hc : (candidate == name) = true
      · rw [if_pos hc] at h
        have hrest : context = rest := by
          simpa using congrArg Prod.snd (Option.some.inj h)
        subst hrest
        simp
      · rw [if_neg hc] at h
        have := ih h
        simp only [List.length_cons]
        omega

mutual
  /-- Counterpart of Cake's `pan_structs$compile_shape`
      (`cakeml/pancake/pan_structsScript.sml:37`): resolve every named shape in
      the struct context into the combination of its field shapes, using the
      remaining context for nested names. -/
  def compileShape [BEq String] (context : StructContext) (shape : Shape) : Shape :=
    match shape with
    | .one => .one
    | .comb shapes => .comb (compileShapes context shapes)
    | .named name =>
        match _hlookup : lookupInfoWithRest name context with
        | some (info, rest) =>
            .comb (compileShapes rest (info.fields.map Prod.snd))
        | none => .one
  termination_by (context.length, sizeOf shape)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ (lookupInfoWithRest_length_lt (by assumption))
      | exact Prod.Lex.right _ (by decreasing_trivial)

  def compileShapes [BEq String] (context : StructContext) (shapes : List Shape) :
      List Shape :=
    match shapes with
    | [] => []
    | shape :: rest => compileShape context shape :: compileShapes context rest
  termination_by (context.length, sizeOf shapes)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ (lookupInfoWithRest_length_lt (by assumption))
      | exact Prod.Lex.right _ (by decreasing_trivial)
end

/-- Counterpart of Cake's `compile_shapes_eq_map`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:310`). -/
theorem compileShapes_eq_map [BEq String] (context : StructContext)
    (shapes : List Shape) :
    compileShapes context shapes = shapes.map (compileShape context) := by
  induction shapes with
  | nil => simp [compileShapes]
  | cons shape rest ih => simp [compileShapes, ih]

/-- Counterpart of the first conjunct of Cake's `is_wf_shape_compile_shape`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:298`): a compiled shape
    is well formed in every context, because it contains no named shapes. -/
theorem compileShape_isWfShape_of [BEq String] (outer : StructContext)
    (context : StructContext) (shape : Shape) :
    isWfShape outer (compileShape context shape) = true := by
  have hmain : ∀ outer : StructContext, ∀ context shape,
      isWfShape outer (compileShape context shape) = true := by
    intro outer
    apply compileShape.induct
      (motive1 := fun context shape => isWfShape outer (compileShape context shape) = true)
      (motive2 := fun context shapes =>
        isWfShape.isWfShapeList outer (compileShapes context shapes) = true)
    · intro context
      simp [compileShape, isWfShape]
    · intro context shapes ih
      simp only [compileShape, isWfShape]
      exact ih
    · intro context name info rest hlookup ih
      rw [compileShape.eq_def]
      dsimp only
      rw [hlookup]
      simp [isWfShape]
      exact ih
    · intro context name hlookup
      rw [compileShape.eq_def]
      dsimp only
      rw [hlookup]
      simp [isWfShape]
    · intro context
      simp [compileShapes, isWfShape.isWfShapeList]
    · intro context shape rest ihHead ihTail
      simp only [compileShapes, isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨ihHead, ihTail⟩
  exact hmain outer context shape

/-- Cake's `is_wf_shape_compile_shape` at the shape level. -/
theorem compileShape_isWfShape [BEq String] (context : StructContext)
    (shape : Shape) : isWfShape context (compileShape context shape) = true :=
  compileShape_isWfShape_of context context shape

/-- Counterpart of the second conjunct of Cake's `is_wf_shape_compile_shape`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:298`). -/
theorem compileShapes_isWfShape [BEq String] (outer : StructContext)
    (context : StructContext) (shapes : List Shape) :
    isWfShape.isWfShapeList outer (compileShapes context shapes) = true := by
  rw [compileShapes_eq_map]
  induction shapes with
  | nil => simp [isWfShape.isWfShapeList]
  | cons shape rest ih =>
      simp only [List.map_cons, isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨compileShape_isWfShape_of outer context shape, ih⟩

/-- Counterpart of Cake's `dropWhile_MAP_helper`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:542`): dropping a prefix
    and then mapping commutes, provided the two predicates agree on the mapped
    elements. -/
theorem dropWhile_map_helper {α β : Type} (P : α → Bool) (Q : β → Bool)
    (f : α → β) (xs : List α) (ys : List α)
    (h : xs.dropWhile P = ys)
    (hPQ : ∀ x ∈ xs, P x = Q (f x)) :
    (xs.map f).dropWhile Q = ys.map f := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.dropWhile_nil] at h
      subst h
      simp
  | cons x xs ih =>
      have hx : P x = Q (f x) := hPQ x (by simp)
      rw [List.dropWhile_cons] at h
      by_cases hP : P x = true
      · rw [if_pos hP] at h
        have hQ : Q (f x) = true := by rw [← hx]; exact hP
        rw [List.map_cons, List.dropWhile_cons, hQ]
        simp only [if_true]
        exact ih ys h (fun y hy => hPQ y (by simp [hy]))
      · rw [if_neg hP] at h
        have hPfalse : P x = false := by simpa using hP
        have hQ : Q (f x) = false := by rw [← hx]; exact hPfalse
        rw [← h, List.map_cons, List.dropWhile_cons, hQ]
        simp only [Bool.false_eq_true, if_false]

theorem isWfShapeList_of_all {context : StructContext} {shapes : List Shape}
    (h : ∀ shape ∈ shapes, isWfShape context shape = true) :
    isWfShape.isWfShapeList context shapes = true := by
  induction shapes with
  | nil => simp [isWfShape.isWfShapeList]
  | cons s ss ih =>
      simp only [isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨h s (by simp), ih (fun t ht => h t (by simp [ht]))⟩

/-- Cake `pan_structs` `struct_infos_ok`: the structure context records distinct
    field names, distinct structure names, well-formed field shapes (each
    resolved in the context suffix after its own entry) and matching sizes. -/
def structInfosOk (context : StructContext) : Prop :=
  (∀ entry ∈ context, (entry.2.fields.map Prod.fst).Nodup) ∧
  (context.map Prod.fst).Nodup ∧
  (∀ (i : Nat) (name : StructName) (info : StructInfo),
      context[i]? = some (name, info) →
      ∀ shape ∈ info.fields.map Prod.snd,
        isWfShape (context.drop (i + 1)) shape = true) ∧
  (∀ entry ∈ context,
      entry.2.size =
        shapeSizeWithContext context (.comb (entry.2.fields.map Prod.snd)))

theorem structInfosOk_drop (n : Nat) (context : StructContext)
    (h : structInfosOk context) : structInfosOk (context.drop n) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hdrop_drop : ∀ (i : Nat) (shape : Shape),
      isWfShape (context.drop (n + i + 1)) shape = true →
        isWfShape ((context.drop n).drop (i + 1)) shape = true := by
    intro i shape hshape
    have hdrop : (context.drop n).drop (i + 1) = context.drop (n + i + 1) := by
      rw [List.drop_drop]
      rw [Nat.add_assoc]
    rwa [hdrop]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro entry hentry
    exact h1 entry (List.mem_of_mem_drop hentry)
  · rw [List.map_drop]
    exact h2.drop
  · intro i name info hget shape hmem
    have hget' : context[n + i]? = some (name, info) := by
      rw [← List.getElem?_drop]
      exact hget
    exact hdrop_drop i shape (h3 (n + i) name info hget' shape hmem)
  · intro entry hentry
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hentry
    have hget : context[n + i]? = some entry := by
      rw [← List.getElem?_drop]
      rw [List.getElem?_eq_getElem hi]
      exact congrArg some heq
    obtain ⟨name, info⟩ := entry
    have hwfFields : isWfShape (context.drop n)
        (.comb (info.fields.map Prod.snd)) = true := by
      have hlist : isWfShape.isWfShapeList (context.drop n)
          (info.fields.map Prod.snd) = true := by
        refine isWfShapeList_of_all (fun shape hmem => ?_)
        have hshape := h3 (n + i) name info hget shape hmem
        exact isWfShape_drop shape (context.drop n) (i + 1)
          (hdrop_drop i shape hshape)
      simpa [isWfShape] using hlist
    have hsize := shapeSizeWithContext_drop n context
      (.comb (info.fields.map Prod.snd)) hwfFields h2
    have hctx := h4 (name, info) (List.mem_of_mem_drop hentry)
    rw [hsize]
    exact hctx

theorem structInfosOk_append (xs ys : StructContext)
    (h : structInfosOk (xs ++ ys)) : structInfosOk ys := by
  have hdrop := structInfosOk_drop xs.length (xs ++ ys) h
  rwa [List.drop_left] at hdrop

/-- Cake `pan_structs` `struct_infos_ok_cons`: prepending a fresh structure
    whose fields are distinct, whose shapes are well formed in the existing
    context and whose recorded size matches keeps the context well formed. -/
theorem structInfosOk_cons (xs : StructContext) (nm : StructName) (info : StructInfo)
    (hxs : structInfosOk xs)
    (hflds : (info.fields.map Prod.fst).Nodup)
    (hfresh : nm ∉ xs.map Prod.fst)
    (hwf : ∀ shape ∈ info.fields.map Prod.snd, isWfShape xs shape = true)
    (hsize : info.size = shapeSizeWithContext xs (.comb (info.fields.map Prod.snd))) :
    structInfosOk ((nm, info) :: xs) := by
  obtain ⟨h1, h2, h3, h4⟩ := hxs
  have hkeys : (((nm, info) :: xs).map Prod.fst).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨hfresh, h2⟩
  have hdropOne : ∀ (shape : Shape),
      isWfShape xs shape = true →
      shapeSizeWithContext xs shape =
        shapeSizeWithContext ((nm, info) :: xs) shape := by
    intro shape hshape
    have hd := shapeSizeWithContext_drop 1 ((nm, info) :: xs) shape
      (by simpa using hshape) hkeys
    simpa using hd
  refine ⟨?_, hkeys, ?_, ?_⟩
  · intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | hentry
    · exact hflds
    · exact h1 entry hentry
  · intro i name info' hget shape hmem
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        obtain ⟨rfl, rfl⟩ := hget
        have hdrop : ((nm, info) :: xs).drop (0 + 1) = xs := rfl
        rw [hdrop]
        exact hwf shape hmem
    | succ k =>
        simp only [List.getElem?_cons_succ] at hget
        have hdrop : ((nm, info) :: xs).drop (Nat.succ k + 1) = xs.drop (k + 1) := by
          rw [Nat.succ_eq_add_one, List.drop_succ_cons]
        rw [hdrop]
        exact h3 k name info' hget shape hmem
  · intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | hentry
    · have hlist : isWfShape.isWfShapeList xs (info.fields.map Prod.snd) = true :=
        isWfShapeList_of_all hwf
      have hwfComb : isWfShape xs (.comb (info.fields.map Prod.snd)) = true := by
        simpa [isWfShape] using hlist
      rw [← hdropOne (.comb (info.fields.map Prod.snd)) hwfComb]
      exact hsize
    · obtain ⟨name, info'⟩ := entry
      obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hentry
      have hget : xs[i]? = some (name, info') := by
        rw [List.getElem?_eq_getElem hi]
        exact congrArg some heq
      have hlist : isWfShape.isWfShapeList xs (info'.fields.map Prod.snd) = true :=
        isWfShapeList_of_all (fun shape hmem =>
          isWfShape_drop shape xs (i + 1) (h3 i name info' hget shape hmem))
      have hwfComb : isWfShape xs (.comb (info'.fields.map Prod.snd)) = true := by
        simpa [isWfShape] using hlist
      rw [← hdropOne (.comb (info'.fields.map Prod.snd)) hwfComb]
      exact h4 (name, info') hentry

/-- Cake `pan_structs` `alookup_map_structs_ok`: a structure found in a
    well-formed context has distinct field names. -/
theorem lookupInfo_fields_nodup [BEq String] [LawfulBEq String] (name : String)
    (context : StructContext) (info : StructInfo)
    (hlookup : lookupInfo name context = some info)
    (hok : structInfosOk context) :
    (info.fields.map Prod.fst).Nodup := by
  induction context with
  | nil => simp [lookupInfo] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      simp only [lookupInfo] at hlookup
      by_cases hc : (candidate == name) = true
      · rw [if_pos hc] at hlookup
        have heq : entryInfo = info := Option.some.inj hlookup
        subst heq
        exact hok.1 (candidate, entryInfo) (by simp)
      · rw [if_neg hc] at hlookup
        exact ih hlookup (structInfosOk_drop 1 ((candidate, entryInfo) :: context) hok)

/-! CakeML `pan_structsProofScript.sml` `map_fst_eq_alookup`: two association
    lists with the same key order find the same key at the same index. -/

theorem afindi_eq_of_map_fst_eq [BEq α] (key : α) :
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
          by_cases hbc : key == cx
          · rw [afindi_cons key (cx, vx) xs, afindi_cons key (cx, vy) ys,
              if_pos hbc, if_pos hbc]
          · rw [afindi_cons key (cx, vx) xs, afindi_cons key (cx, vy) ys,
              if_neg hbc, if_neg hbc, ih ys htail]

/-- Counterpart of Cake's `map_fst_eq_alookup`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:278`): if two
    association lists have the same keys in the same order, a successful
    lookup in the first is also found at the same index in the second. -/
theorem map_fst_eq_lookup [BEq String] [LawfulBEq String]
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
