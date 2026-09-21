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

end Flapjack
