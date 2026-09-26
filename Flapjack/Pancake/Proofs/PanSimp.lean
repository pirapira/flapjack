import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.PanGlobals
import Flapjack.PanProgramSemantics
import Flapjack.Pancake.PanSimp

/-!
Counterpart of Cake's `decs_stcnames_compile_prog`
(`cakeml/pancake/proofs/pan_simpProofScript.sml:1334-1341`):

    !ctxt pan_code. decs_stcnames ctxt (compile_prog pan_code) =
                    decs_stcnames ctxt pan_code

Flapjack's `collectPanValueStructs` is the executable counterpart of Cake's
`decs_stcnames` (`cakeml/pancake/semantics/panSemScript.sml:839-859`), and
`panSimpDecls` is the counterpart of `pan_simp$compile_prog`.  Because
`pan_simp` rewrites only function bodies and leaves every other declaration
constructor untouched, it cannot change the struct-name context that
`collectPanValueStructs` accumulates. -/

namespace Flapjack

/-- Cons equation for `collectPanValueStructs`, mirroring Cake's
    `decs_stcnames_def`. -/
theorem collectPanValueStructs_cons (declaration : Decl α) (declarations : List (Decl α))
    (context : StructContext) :
    collectPanValueStructs (declaration :: declarations) context =
      (match declaration with
       | .name name fields =>
           if (lookupInfo name context).isSome then none
           else if !(fields.map (fun field => field.1)).Nodup then none
           else if !fields.all (fun field => isWfShape context field.2) then none
           else collectPanValueStructs declarations
                  ((name, panValueDeclStructInfo context fields) :: context)
       | _ => collectPanValueStructs declarations context) := by
  cases declaration <;> rw [collectPanValueStructs.eq_def]

/-- Flapjack-only analogue of Cake's `decs_stcnames_compile_prog`: `pan_simp`
    preserves the struct-name context collected from a declaration list.  This
    statement reads the production String-keyed `Prog`/`Decl` carriers, whereas
    HOL `cakeml/pancake/proofs/pan_simpProofScript.sml` states it over the exact
    `mlstring`-keyed panLang syntax; the HOL tag was therefore withdrawn (bead
    flapjack-4ac.8) and the exact port is tracked by flapjack-4ac.8 (blocked by
    the exact-transformation prerequisite flapjack-4ac.8.1). -/
theorem collectPanValueStructs_panSimpDecls (declarations : List (Decl α))
    (context : StructContext) :
    collectPanValueStructs (panSimpDecls declarations) context =
      collectPanValueStructs declarations context := by
  rw [panSimpDecls_eq_map]
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      simp only [List.map_cons]
      cases declaration <;>
        simp [panSimpDecl, collectPanValueStructs_cons, ih]

/-- Cake's `decs_stcnames_only_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1592`): a declaration list
    without struct declarations leaves the struct-name context unchanged. -/
theorem collectPanValueStructs_of_no_names (context : StructContext)
    (declarations : List (Decl α))
    (hall : declarations.all (fun declaration => !isName declaration) = true) :
    collectPanValueStructs declarations context = some context := by
  induction declarations generalizing context with
  | nil => simp [collectPanValueStructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hnotname : isName declaration = false := by simpa using hhead
      cases declaration with
      | function declaration =>
          simpa [collectPanValueStructs_cons] using ih context htail
      | decl shape name value =>
          simpa [collectPanValueStructs_cons] using ih context htail
      | exnDecl exception shape =>
          simpa [collectPanValueStructs_cons] using ih context htail
      | name name fields => simp [isName] at hnotname

/-- Cake's `decs_stcnames_only_functions2`
    (`cakeml/pancake/semantics/panPropsScript.sml:1600`): a list of function
    declarations only leaves the struct-name context unchanged. -/
theorem collectPanValueStructs_of_functions (context : StructContext)
    (declarations : List (Decl α))
    (hall : declarations.all globalDeclIsFunction = true) :
    collectPanValueStructs declarations context = some context := by
  refine collectPanValueStructs_of_no_names context declarations ?_
  refine List.all_eq_true.mpr (fun declaration hmem => ?_)
  have hfunction := List.all_eq_true.mp hall declaration hmem
  cases declaration <;> simp_all [globalDeclIsFunction, isName]

theorem lookupInfo_isSome_of_mem [BEq String] [LawfulBEq String] (name : String)
    (context : InfoMap β) (hmem : name ∈ context.map Prod.fst) :
    (lookupInfo name context).isSome = true := by
  induction context with
  | nil => simp at hmem
  | cons entry context ih =>
      obtain ⟨candidate, info⟩ := entry
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · subst heq
        simp [lookupInfo]
      · simp only [lookupInfo]
        by_cases hc : (candidate == name) = true
        · simp [hc]
        · simp [hc]
          exact ih hmem

theorem lookupInfo_eq_some_of_mem_of_nodup [BEq String] [LawfulBEq String]
    (name : String) (context : InfoMap β) (value : β)
    (hmem : (name, value) ∈ context)
    (hnodup : context.map Prod.fst |>.Nodup) :
    lookupInfo name context = some value := by
  induction context with
  | nil => simp at hmem
  | cons entry context ih =>
      obtain ⟨candidate, candidateValue⟩ := entry
      simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hmem hnodup
      rcases hmem with hhead | htail
      · cases hhead
        simp [lookupInfo]
      · have hne : candidate ≠ name := by
          intro heq
          subst candidate
          apply hnodup.1
          exact List.mem_map.mpr ⟨(name, value), htail, rfl⟩
        have hlookup := ih htail hnodup.2
        simp [lookupInfo, hne, hlookup]

theorem collectPanValueStructs_structInfosOk {α : Type} (declarations : List (Decl α)) :
    ∀ (context context' : StructContext),
      collectPanValueStructs declarations context = some context' →
        structInfosOk context → structInfosOk context' := by
  induction declarations with
  | nil =>
      intro context context' hcollect hok
      simp only [collectPanValueStructs] at hcollect
      have : context' = context := (Option.some.injEq _ _).mp hcollect.symm
      subst this
      exact hok
  | cons declaration declarations ih =>
      intro context context' hcollect hok
      cases declaration with
      | name name fields =>
          simp only [collectPanValueStructs_cons] at hcollect
          by_cases hsome : (lookupInfo name context).isSome = true
          · simp [hsome] at hcollect
          · have hsomeFalse : (lookupInfo name context).isSome = false := by
              simpa using hsome
            by_cases hnodup : (fields.map (fun field => field.1)).Nodup
            · by_cases hall : fields.all (fun field => isWfShape context field.2) = true
              · simp only [hsomeFalse, hnodup, hall] at hcollect
                have hfresh : name ∉ context.map Prod.fst := by
                  intro hmem
                  have hbin := lookupInfo_isSome_of_mem name context hmem
                  rw [hsomeFalse] at hbin
                  simp at hbin
                have hwf : ∀ shape ∈ fields.map Prod.snd,
                    isWfShape context shape = true := by
                  intro shape hmem
                  obtain ⟨field, hfield, rfl⟩ := List.mem_map.mp hmem
                  exact List.all_eq_true.mp hall field hfield
                exact ih ((name, panValueDeclStructInfo context fields) :: context)
                  context' hcollect
                  (structInfosOk_cons context name (panValueDeclStructInfo context fields)
                    hok hnodup hfresh hwf rfl)
              · simp [hsomeFalse, hnodup, hall] at hcollect
            · simp [hsomeFalse, hnodup] at hcollect
      | decl shape name value =>
          simp only [collectPanValueStructs_cons] at hcollect
          exact ih context context' hcollect hok
      | exnDecl exception shape =>
          simp only [collectPanValueStructs_cons] at hcollect
          exact ih context context' hcollect hok
      | function declaration =>
          simp only [collectPanValueStructs_cons] at hcollect
          exact ih context context' hcollect hok

/-- Cake's `decs_stcnames_lemma`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4966`): a list of
    declarations that are each either a function or an exception declaration
    leaves the struct-name context unchanged.  This is the disjunctive form
    used by `state_rel_imp_semantics_decls_to_crep`. -/
theorem collectPanValueStructs_of_functions_or_exnDecls (context : StructContext)
    (declarations : List (Decl α))
    (hall : declarations.all
      (fun declaration => globalDeclIsFunction declaration || isExnDecl declaration) = true) :
    collectPanValueStructs declarations context = some context := by
  refine collectPanValueStructs_of_no_names context declarations ?_
  refine List.all_eq_true.mpr (fun declaration hmem => ?_)
  have hfunction := List.all_eq_true.mp hall declaration hmem
  cases declaration <;> simp_all [globalDeclIsFunction, isExnDecl, isName]

/-! Cake's `OPT_MMAP` is `List.mapM` for `Option`, so the list-mapping helper
lemmas used by `compile_correct` (`cakeml/pancake/proofs/pan_simpProofScript.sml`)
have the following `List.mapM` counterparts.  These are the pieces needed to
transfer an `OPT_MMAP (eval s) es = SOME vs` hypothesis to a related state `t`
(`opt_mmap_eq_some_helper`, `OPT_MMAP_NONE`, `OPT_MMAP_NONE'`). -/

/-- Cake's `opt_mmap_eq_some_helper` (`pan_simpProofScript.sml:394`): if two
    functions agree on every element that the first maps successfully, then
    mapping the second succeeds with the same result. -/
theorem list_mapM_eq_some_of_eq_some {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α) (zs : List β), xs.mapM f = some zs →
      (∀ x ∈ xs, ∀ y, f x = some y → g x = some y) → xs.mapM g = some zs
  | [], zs, h, _ => h
  | x :: xs, zs, h, hfg => by
      rw [List.mapM_cons] at h ⊢
      cases hx : f x with
      | none => simp [hx] at h
      | some a =>
          have hga : g x = some a := hfg x (by simp) a hx
          rw [hga]
          simp at h ⊢
          cases hys : List.mapM f xs with
          | none => simp [hys] at h
          | some ys =>
              have hz : zs = a :: ys := by simpa [hys, hx] using h.symm
              subst hz
              rw [list_mapM_eq_some_of_eq_some f g xs ys hys
                    (fun z hz' b hb => hfg z (by simp [hz']) b hb)]
              rfl

/-- Cake's `opt_mmap_flookup_update` (`pan_commonPropsScript.sml:156`):
    mapping a lookup over a list that does not mention the updated name is
    unchanged by the update. -/
theorem list_mapM_updatePanValueMap_not_mem {γ : Type} [BEq γ] [LawfulBEq γ]
    {α : Type} (values : γ → Option α) (xs : List γ) (ys : List α)
    (name : γ) (value : α)
    (h : xs.mapM (fun x => values x) = some ys)
    (hnotmem : name ∉ xs) :
    xs.mapM (fun x => updatePanValueMap values name value x) = some ys := by
  refine list_mapM_eq_some_of_eq_some (α := γ) (β := α) (fun x => values x)
    (fun x => updatePanValueMap values name value x) xs ys h ?_
  intro x hx y hy
  have hne : x ≠ name := fun heq => hnotmem (heq ▸ hx)
  simp [updatePanValueMap, beq_iff_eq, hne, hy]

/-- Cake's `OPT_MMAP_NONE` (`pan_simpProofScript.sml:500`): a failing map has
    a failing element. -/
theorem list_mapM_eq_none_exists {α β : Type} (f : α → Option β) (xs : List α)
    (h : xs.mapM f = none) : ∃ x ∈ xs, f x = none := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      rw [List.mapM_cons] at h
      cases hx : f x with
      | none => exact ⟨x, by simp, hx⟩
      | some y =>
          cases hys : List.mapM f xs with
          | none =>
              obtain ⟨z, hz, hfz⟩ := ih hys
              exact ⟨z, by simp [hz], hfz⟩
          | some ys =>
              simp [hys] at h
              exact absurd hx (h y)

/-- Cake's `OPT_MMAP_NONE'` (`pan_simpProofScript.sml:509`): a failing element
    makes the whole map fail. -/
theorem list_mapM_eq_none_of_mem {α β : Type} (f : α → Option β) {x : α} {xs : List α}
    (hx : x ∈ xs) (hf : f x = none) : xs.mapM f = none := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.mapM_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp [hf]
      · cases hy : f y with
        | none => simp
        | some b => simp [ih hx']

/-- Cake's `opt_mmap_eq_some_el` (`pan_structsProofScript.sml:19`): a successful
    `OPT_MMAP` is exactly a length match together with a pointwise success
    condition, adapted from total `EL` to `getElem?`. -/
theorem list_mapM_eq_some_iff {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) :
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

/-- Cake's `OPT_MMAP_MEM_IMP`
(`cakeml/pancake/semantics/panPropsScript.sml:115-123`): every element of a
successful `OPT_MMAP` image has a preimage in the source list on which `f`
succeeds. -/
theorem list_mapM_mem_exists {α β : Type} (f : α → Option β) (xs : List α)
    (ys : List β) (h : xs.mapM f = some ys) (y : β) (hy : y ∈ ys) :
    ∃ x, x ∈ xs ∧ f x = some y := by
  obtain ⟨_, hpt⟩ := (list_mapM_eq_some_iff f xs ys).mp h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hy
  have hi' : i < ys.length := (List.getElem?_eq_some_iff.mp hi).1
  have hb := hpt i hi'
  rw [hi] at hb
  cases hx : xs[i]? with
  | none => simp [hx] at hb
  | some x =>
      simp only [hx, Option.bind_some] at hb
      exact ⟨x, List.mem_of_getElem? hx, hb⟩

/-- Cake's `opt_mmap_length_eq` (`pan_commonPropsScript.sml:82`): a successful
    `OPT_MMAP` preserves the list length. -/
theorem list_mapM_length {α β : Type} (f : α → Option β) (xs : List α)
    (ys : List β) (h : xs.mapM f = some ys) : xs.length = ys.length :=
  (list_mapM_eq_some_iff f xs ys).mp h |>.1

/-- Cake's `opt_mmap_mem_func` (`pan_commonPropsScript.sml:49`): every element
    of a successfully mapped list has a successful image. -/
theorem list_mapM_mem_func {α β : Type} (f : α → Option β) {x : α} {xs : List α}
    (ys : List β) (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ y, f x = some y := by
  cases hf : f x with
  | none => exact absurd (list_mapM_eq_none_of_mem f hx hf) (by rw [h]; simp)
  | some y => exact ⟨y, rfl⟩

/-- Cake's `opt_mmap_el` (`pan_commonPropsScript.sml:71`): a successful
    `OPT_MMAP` maps the `n`-th element to the `n`-th image, stated with
    `getElem?` so no length side condition is needed. -/
theorem list_mapM_getElem? {α β : Type} (f : α → Option β) (xs : List α)
    (ys : List β) (h : xs.mapM f = some ys) (n : Nat) :
    (xs[n]?).bind f = ys[n]? := by
  by_cases hn : n < ys.length
  · exact (list_mapM_eq_some_iff f xs ys).mp h |>.2 n hn
  · have hxsn : xs.length ≤ n := by
      have hlen := list_mapM_length f xs ys h
      omega
    rw [List.getElem?_eq_none hxsn, List.getElem?_eq_none (by omega)]
    rfl

/-! A successful `OPT_MMAP` remains successful on the same `drop`/`take`
window of its input and output. This Flapjack list utility supports projecting
the target local words associated with one `ctxtFc` parameter. -/
theorem list_mapM_takeDrop_of_success {α β : Type} (f : α → Option β)
    (inputs : List α) (outputs : List β) (start count : Nat)
    (hmap : inputs.mapM f = some outputs) :
    ((inputs.drop start).take count).mapM f =
      some ((outputs.drop start).take count) := by
  apply (list_mapM_eq_some_iff f _ _).2
  constructor
  · simp only [List.length_take, List.length_drop]
    have hlength := list_mapM_length f inputs outputs hmap
    omega
  · intro index hindex
    have hlength := list_mapM_length f inputs outputs hmap
    have hcount : index < count := by
      simp only [List.length_take, List.length_drop] at hindex
      omega
    have hinput : start + index < inputs.length := by
      have hdrop : index < (inputs.drop start).length := by
        have hindex' : index < min count (inputs.length - start) := by
          simpa [List.length_take, List.length_drop, hlength] using hindex
        have hmin : min count (inputs.length - start) ≤
            (inputs.drop start).length := by
          rw [List.length_drop]
          exact Nat.min_le_right _ _
        exact Nat.lt_of_lt_of_le hindex' hmin
      simp only [List.length_drop] at hdrop
      omega
    have houtput : start + index < outputs.length := by
      have hdrop : index < (outputs.drop start).length := by
        have hindex' : index < min count (outputs.length - start) := by
          simpa [List.length_take, List.length_drop] using hindex
        have hmin : min count (outputs.length - start) ≤
            (outputs.drop start).length := by
          rw [List.length_drop]
          exact Nat.min_le_right _ _
        exact Nat.lt_of_lt_of_le hindex' hmin
      simp only [List.length_drop] at hdrop
      omega
    have hpoint := (list_mapM_eq_some_iff f inputs outputs).mp hmap |>.2
      (start + index) houtput
    simpa [List.getElem?_take, List.getElem?_drop, hcount, hinput, houtput]
      using hpoint

/-- Cake's `opt_mmap_mem_defined` (`pan_commonPropsScript.sml:59`): a
    successful `OPT_MMAP` contains the image of every successful element map. -/
theorem list_mapM_mem_defined {α β : Type} (f : α → Option β) {x : α} {xs : List α}
    {e : β} {ys : List β} (h : xs.mapM f = some ys) (hx : x ∈ xs)
    (hf : f x = some e) : e ∈ ys := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hx
  have hpoint := list_mapM_getElem? f xs ys h n
  rw [hn] at hpoint
  rw [Option.bind_some] at hpoint
  rw [hf] at hpoint
  exact List.mem_of_getElem? hpoint.symm

/-- Cake's `opt_mmap_opt_map` (`pan_commonPropsScript.sml:92`): mapping a
    successful `OPT_MMAP` through a total function maps the result. -/
theorem list_mapM_map {α β γ : Type} (f : α → Option β) (xs : List α)
    (ys : List β) (g : β → γ) (h : xs.mapM f = some ys) :
    xs.mapM (fun x => (f x).map g) = some (ys.map g) := by
  refine (list_mapM_eq_some_iff (fun x => (f x).map g) xs (ys.map g)).mpr ⟨?_, ?_⟩
  · rw [List.length_map, list_mapM_length f xs ys h]
  · intro n _
    have hpoint := list_mapM_getElem? f xs ys h n
    rw [List.getElem?_map]
    rw [show (fun x => (f x).map g) = (Option.map g ∘ f) from rfl]
    rw [← Option.map_bind, hpoint]

/-- Compatibility name for the exact HOL `opt_mmap_eq_some` theorem now in
    `PanCommonProps`; retained for existing PanSimp consumers. -/
theorem list_mapM_eq_some_map_some {α β : Type} (f : α → Option β)
    (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔ xs.map f = ys.map some :=
  optMmapEqSome xs f ys

/-- Cake's `map_some_the_map` (`pan_commonPropsScript.sml:615`): if mapping `f`
    over `xs` yields `ys` tagged with `some`, then recovering the payload with a
    total `getD` returns `ys`.  Cake writes the payload recovery as `THE (f n)`;
    the total `Option.getD` is the constructive analogue. -/
theorem map_getD_map_some {α β : Type} (f : α → Option β) (default : β)
    (xs : List α) (ys : List β) (h : xs.map f = ys.map some) :
    xs.map (fun x => (f x).getD default) = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hfx, htail⟩ := h
          simp only [List.map_cons, hfx, Option.getD_some, List.cons.injEq]
          exact ⟨trivial, ih ys htail⟩

/-- Cake's `map_the_some_cancel` (`pan_commonPropsScript.sml:332`):
    mapping `THE ∘ SOME` over a list is the identity. Flapjack's total
    `Option.getD` replaces Cake's partial `THE`, so the statement is the
    `some`/`getD` form below. -/
theorem map_some_getD_eq_self {α : Type} (default : α) (xs : List α) :
    xs.map (fun x => (some x : Option α).getD default) = xs := by
  simp

/-- Cake's `set_eq_membership` (`pan_commonPropsScript.sml:624`): membership
    transports along an equality. -/
theorem mem_of_eq_mem {α : Type} {a b : α} {s : List α} (h : a = b)
    (hmem : a ∈ s) : b ∈ s := h ▸ hmem

/-- Cake's `lookup_some_el` (`pan_commonPropsScript.sml:758`), stated for the
    list-backed lookup that Flapjack uses instead of Cake's `fromAList` finite
    map: a successful lookup exposes an index carrying the entry. -/
theorem lookup_mem_exists {α β : Type} [BEq α] [LawfulBEq α]
    (key : α) (xs : List (α × β)) (value : β) (h : xs.lookup key = some value) :
    ∃ m : Nat, xs[m]? = some (key, value) := by
  obtain ⟨l₁, l₂, heq, _⟩ :=
    (List.lookup_eq_some_iff (l := xs) (k := key) (b := value)).mp h
  have hmem : (key, value) ∈ xs := by
    rw [heq]
    exact List.mem_append_right _ (by simp)
  exact List.mem_iff_getElem?.mp hmem

/-- Cake's `map_append_eq_drop` (`pan_commonPropsScript.sml:39`): the tail of a
    mapped list after the first component of an append decomposition. -/
theorem map_eq_append_drop {α β : Type} (f : α → β) (xs : List α)
    (ys zs : List β) (h : xs.map f = ys ++ zs) :
    (xs.drop ys.length).map f = zs := by
  rw [List.map_drop, h, List.drop_left]

/-! Cake's `state_rel_imp_evaluate_decls`
(`cakeml/pancake/proofs/pan_simpProofScript.sml:1303-1331`) says that evaluating a
declaration list and evaluating the `pan_simp`-simplified declaration list agree
up to a state relation that only changes function bodies.  The Flapjack analogue
below states that relation explicitly (`panValueProgramStateRel`) and proves the
same preservation for `evalPanValueDeclarationsWithStructs` and for the
struct-name-collecting entry point `evalPanValueDeclarations`. -/

def panValueFunctionsSimp :
    List (FunName × List VarName × Prog α) →
      List (FunName × List VarName × Prog α)
  | [] => []
  | (name, parameters, body) :: rest =>
      (name, parameters, panSimpProg body) :: panValueFunctionsSimp rest

/-! The evaluator uses the source-shaped `lookupPanFunction` table rather than
    Cake's richer declaration projection.  This is the direct function-table
    lookup bridge needed when lifting `state_rel_imp_semantics`: a successful
    source lookup remains successful after `pan_simp`, with only the body
    transformed. -/
theorem lookupPanFunction_panValueFunctionsSimp
    (functions : List (FunName × List VarName × Prog α)) (name : FunName)
    {parameters : List VarName} {body : Prog α}
    (hlookup : lookupPanFunction name functions = some (parameters, body)) :
    lookupPanFunction name (panValueFunctionsSimp functions) =
      some (parameters, panSimpProg body) := by
  induction functions with
  | nil =>
      simp [lookupPanFunction] at hlookup
  | cons entry functions ih =>
      obtain ⟨candidate, parameters', body'⟩ := entry
      by_cases hname : name == candidate
      · simp [lookupPanFunction, panValueFunctionsSimp, hname] at hlookup ⊢
        rcases hlookup with ⟨rfl, rfl⟩
        simp
      · have htail : lookupPanFunction name functions = some (parameters, body) := by
          simpa [lookupPanFunction, hname] using hlookup
        have htail' := ih htail
        simpa [lookupPanFunction, panValueFunctionsSimp, hname] using htail'

def panValueProgramStateRel (s t : PanValueProgramState α) : Prop :=
  s.structs = t.structs ∧
  s.globals = t.globals ∧
  s.memory = t.memory ∧
  s.returnShapes = t.returnShapes ∧
  s.parameterShapes = t.parameterShapes ∧
  s.exceptions = t.exceptions ∧
  s.baseAddress = t.baseAddress ∧
  s.topAddress = t.topAddress ∧
  s.bytesInWord = t.bytesInWord ∧
  t.functions = panValueFunctionsSimp s.functions

/-! State-relation form of the lookup bridge.  This is the call-site fact used
    by the Cake `state_rel_imp_semantics` induction: related states differ in
    function bodies only, so a source callee lookup lifts to its `pan_simp`
    body in the target state. -/
theorem panValueProgramStateRel_lookupPanFunction
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (name : FunName) {parameters : List VarName} {body : Prog α}
    (hlookup : lookupPanFunction name s.functions = some (parameters, body)) :
    lookupPanFunction name t.functions = some (parameters, panSimpProg body) := by
  obtain ⟨_hstructs, _hglobals, _hmemory, _hreturnShapes, _hparameterShapes,
    _hexceptions, _hbaseAddress, _htopAddress, _hbytesInWord, hfunctions⟩ := hrel
  rw [hfunctions]
  exact lookupPanFunction_panValueFunctionsSimp s.functions name hlookup

/-- Cake's `state_rel_upd_inv` (`pan_simpProofScript.sml:387`): the source
    state can be recovered from the target state by resetting the simplified
    function table. -/
theorem panValueProgramStateRel_functions_recover
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t) :
    ∃ functions, s = { t with functions := functions } := by
  refine ⟨s.functions, ?_⟩
  cases s
  cases t
  simp_all [panValueProgramStateRel]

/-- Cake's `state_rel_intro` (`pan_simpProofScript.sml:377`): the target state is
    the source state with its function table replaced by the simplified one. -/
theorem panValueProgramStateRel_intro
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t) :
    t = { s with functions := panValueFunctionsSimp s.functions } := by
  cases s
  cases t
  simp_all [panValueProgramStateRel]

theorem panSimpDecls_nil : panSimpDecls ([] : List (Decl α)) = [] := by
  simp [panSimpDecls]

theorem panSimpDecls_function (declaration : FunDecl α) (declarations : List (Decl α)) :
    panSimpDecls (.function declaration :: declarations) =
      .function { declaration with body := panSimpProg declaration.body } ::
        panSimpDecls declarations := by
  simp [panSimpDecls]

theorem panSimpDecls_name (name : StructName) (fields : List (FieldName × Shape))
    (declarations : List (Decl α)) :
    panSimpDecls (.name name fields :: declarations) = .name name fields :: panSimpDecls declarations := by
  simp [panSimpDecls]

end Flapjack

namespace Flapjack

theorem panValueProgramStateRel_evalPanValueDeclarationsWithStructs
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (s t : PanValueProgramState α)
    (hrel : panValueProgramStateRel s t)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (s' : PanValueProgramState α)
    (hs : evalPanValueDeclarationsWithStructs structs s declarations memoryAccess = some s') :
    ∃ t', evalPanValueDeclarationsWithStructs structs t (panSimpDecls declarations)
        memoryAccess = some t' ∧ panValueProgramStateRel s' t' := by
  induction declarations generalizing s t s' with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at hs
      refine ⟨t, ?_, ?_⟩
      · simp [panSimpDecls_nil, evalPanValueDeclarationsWithStructs]
      · rw [show s' = s from ?_]
        · exact hrel
        · simp only [Option.some.injEq] at hs; exact hs.symm
  | cons declaration declarations ih =>
      cases declaration with
      | name struct fields =>
          simp only [panSimpDecls_name, evalPanValueDeclarationsWithStructs] at hs ⊢
          exact ih s t hrel s' hs
      | decl shape name expression =>
          simp only [panSimpDecls, evalPanValueDeclarationsWithStructs] at hs ⊢
          obtain ⟨hstructs, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩ := hrel
          rw [hglobals, hmemory, hbase, htop, hbiw] at hs
          cases hval : evalPanValueExp structs (fun _ => none) t.globals t.memory
              t.baseAddress t.topAddress t.bytesInWord expression
              (memoryAccess := memoryAccess) with
          | none => simp [hval] at hs
          | some value =>
              by_cases hmatch : panShapeMatches (panValueShape structs value) shape = true
              · simp [hval, hmatch] at hs ⊢
                refine ih _ _ ?_ s' hs
                exact ⟨rfl, rfl, rfl, hret, hparam, hexn, rfl, rfl, rfl, hfuncs⟩
              · simp [hval, hmatch] at hs
      | function declaration =>
          simp only [panSimpDecls_function, evalPanValueDeclarationsWithStructs] at hs ⊢
          obtain ⟨hstructs, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩ := hrel
          by_cases hwf : (declaration.params.all (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at hs ⊢
            refine ih _ _ ?_ s' hs
            exact ⟨rfl, hglobals, hmemory, by rw [hret], by rw [hparam],
              hexn, hbase, htop, hbiw, by simp [hfuncs, panValueFunctionsSimp]⟩
          · simp [hwf] at hs
      | exnDecl exception shape =>
          simp only [panSimpDecls, evalPanValueDeclarationsWithStructs] at hs ⊢
          obtain ⟨hstructs, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩ := hrel
          rw [hexn] at hs
          by_cases hexists : (lookupInfo exception t.exceptions).isSome = true
          · simp [hexists] at hs
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at hs ⊢
              refine ih _ _ ?_ s' hs
              exact ⟨rfl, hglobals, hmemory, hret, hparam, rfl, hbase, htop, hbiw, hfuncs⟩
            · simp [hexists, hwf] at hs

theorem panValueProgramStateRel_evalPanValueDeclarations
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (s' : PanValueProgramState α)
    (hs : evalPanValueDeclarations s declarations memoryAccess = some s') :
    ∃ t', evalPanValueDeclarations t (panSimpDecls declarations) memoryAccess = some t' ∧
      panValueProgramStateRel s' t' := by
  obtain ⟨hstructs, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩ := hrel
  simp only [evalPanValueDeclarations] at hs ⊢
  cases hcollect : collectPanValueStructs declarations s.structs with
  | none => simp [hcollect] at hs
  | some structs =>
      have htcollect : collectPanValueStructs (panSimpDecls declarations) t.structs =
          some structs := by
        rw [collectPanValueStructs_panSimpDecls, ← hstructs]
        exact hcollect
      simp only [hcollect, htcollect] at hs ⊢
      refine panValueProgramStateRel_evalPanValueDeclarationsWithStructs structs
        { s with structs := structs } { t with structs := structs } ?_ declarations
        memoryAccess s' hs
      exact ⟨rfl, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩

/-! A concrete declaration/evaluator bridge for the Cake
    `state_rel_imp_semantics_decls_to_crep` induction.  The declaration
    evaluator is run on both related states, and a source callee lookup is
    transported through the resulting state relation.  This is stronger than
    carrying the relation as a premise: it produces the target evaluator
    result and the exact `pan_simp` body that the compiled call sees. -/
theorem panValueProgramStateRel_evalDeclarations_lookupPanFunction
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (s' : PanValueProgramState α)
    (hs : evalPanValueDeclarations s declarations memoryAccess = some s')
    (name : FunName) {parameters : List VarName} {body : Prog α}
    (hlookup : lookupPanFunction name s'.functions = some (parameters, body)) :
    ∃ t', evalPanValueDeclarations t (panSimpDecls declarations) memoryAccess = some t' ∧
      lookupPanFunction name t'.functions =
        some (parameters, panSimpProg body) := by
  obtain ⟨t', ht, hrel'⟩ := panValueProgramStateRel_evalPanValueDeclarations
    s t hrel declarations memoryAccess s' hs
  refine ⟨t', ht, ?_⟩
  exact panValueProgramStateRel_lookupPanFunction s' t' hrel' name hlookup

/-! The declaration-state adequacy package used by the Cake
    `state_rel_imp_semantics_decls_to_crep` induction.  Besides transporting a
    callee lookup, retain the whole post-declaration state relation and its
    exception-table component.  This makes the evaluator output—not merely the
    relation premise—available to the subsequent returned/raised call bridge. -/
theorem panValueProgramStateRel_evalDeclarations_adequacy
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (s' : PanValueProgramState α)
    (hs : evalPanValueDeclarations s declarations memoryAccess = some s')
    (name : FunName) {parameters : List VarName} {body : Prog α}
    (hlookup : lookupPanFunction name s'.functions = some (parameters, body)) :
    ∃ t', evalPanValueDeclarations t (panSimpDecls declarations) memoryAccess = some t' ∧
      panValueProgramStateRel s' t' ∧
      lookupPanFunction name t'.functions =
        some (parameters, panSimpProg body) ∧
      s'.exceptions = t'.exceptions := by
  obtain ⟨t', ht, hrel'⟩ := panValueProgramStateRel_evalPanValueDeclarations
    s t hrel declarations memoryAccess s' hs
  have hlookup' := panValueProgramStateRel_lookupPanFunction s' t' hrel' name hlookup
  have hexceptions : s'.exceptions = t'.exceptions := by
    rcases hrel' with ⟨_hstructs, _hglobals, _hmemory, _hreturnShapes,
      _hparameterShapes, hexceptions, _hbaseAddress, _htopAddress, _hbytesInWord,
      _hfunctions⟩
    exact hexceptions
  exact ⟨t', ht, hrel', hlookup', hexceptions⟩

/-! The returned-call declaration step only needs the return-shape projection
    of the full adequacy package.  Keep this smaller bridge available to the
    `state_rel_imp_semantics_decls_to_crep` induction so a caller can consume
    the target declaration evaluator, post-state relation, and callee shape
    without unpacking the function-table lookup case. -/
theorem panValueProgramStateRel_evalDeclarations_returnShape_adequacy
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (s' : PanValueProgramState α)
    (hs : evalPanValueDeclarations s declarations memoryAccess = some s')
    (name : FunName) (shape : Shape)
    (hlookup : lookupInfo name s'.returnShapes = some shape) :
    ∃ t', evalPanValueDeclarations t (panSimpDecls declarations) memoryAccess = some t' ∧
      panValueProgramStateRel s' t' ∧
      lookupInfo name t'.returnShapes = some shape ∧
      s'.exceptions = t'.exceptions := by
  obtain ⟨t', ht, hrel'⟩ :=
    panValueProgramStateRel_evalPanValueDeclarations
      s t hrel declarations memoryAccess s' hs
  rcases hrel' with ⟨hstructs, hglobals, hmemory, hreturnShapes,
    hparameterShapes, hexceptions', hbaseAddress, htopAddress, hbytesInWord,
    hfunctions⟩
  have htargetLookup : lookupInfo name t'.returnShapes = some shape := by
    rw [← hreturnShapes]
    exact hlookup
  exact ⟨t', ht,
    ⟨hstructs, hglobals, hmemory, hreturnShapes, hparameterShapes, hexceptions',
      hbaseAddress, htopAddress, hbytesInWord, hfunctions⟩,
    htargetLookup, by exact hexceptions'⟩

/-! The parameter-shape projection needed by the argument side of Cake's
    `state_rel_imp_semantics_decls_to_crep` call step.  Declaration evaluation
    preserves the complete state relation, so the target parameter table can
    be used directly by the subsequent evaluator relation rather than being
    carried as an unproved premise. -/
theorem panValueProgramStateRel_evalDeclarations_parameterShape_adequacy
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (s' : PanValueProgramState α)
    (hs : evalPanValueDeclarations s declarations memoryAccess = some s')
    (name : FunName) (parameters : List (VarName × Shape))
    (hlookup : lookupInfo name s'.parameterShapes = some parameters) :
    ∃ t', evalPanValueDeclarations t (panSimpDecls declarations) memoryAccess = some t' ∧
      panValueProgramStateRel s' t' ∧
      lookupInfo name t'.parameterShapes = some parameters ∧
      s'.exceptions = t'.exceptions := by
  obtain ⟨t', ht, hrel'⟩ := panValueProgramStateRel_evalPanValueDeclarations
    s t hrel declarations memoryAccess s' hs
  rcases hrel' with ⟨hstructs, hglobals, hmemory, hreturnShapes,
    hparameterShapes, hexceptions', hbaseAddress, htopAddress, hbytesInWord,
    hfunctions⟩
  have htargetLookup : lookupInfo name t'.parameterShapes = some parameters := by
    rw [← hparameterShapes]
    exact hlookup
  exact ⟨t', ht,
    ⟨hstructs, hglobals, hmemory, hreturnShapes, hparameterShapes, hexceptions',
      hbaseAddress, htopAddress, hbytesInWord, hfunctions⟩,
    htargetLookup, by exact hexceptions'⟩

/-! Cake's `map_snd_f_eq` (`pan_simpProofScript.sml:43`): rewriting only the
    body component of a declaration triple commutes with projecting that body
    and applying a further function.  Stated for `List (α × β × γ)`, whose
    nested `Prod.snd` projections are Cake's `SND ∘ SND`. -/

/-- Cake's `map_snd_f_eq` (`pan_simpProofScript.sml:43`). -/
theorem list_map_third_map_eq {α β γ δ ε : Type} (f : γ → δ) (g : δ → ε)
    (p : List (α × β × γ)) :
    (p.map (fun t => (t.1, t.2.1, f t.2.2))).map (fun t => g t.2.2) =
      p.map (fun t => g (f t.2.2)) := by
  induction p with
  | nil => rfl
  | cons t ts ih => simp [ih]

/-! Cake's `compile_eval_correct` (`pan_simpProofScript.sml:489-...`): an
    expression that evaluates successfully before `pan_simp` evaluates to the
    same value in any state related by `state_rel`.  `pan_simp` rewrites only
    function bodies, which expression evaluation never observes, so the
    Flapjack counterpart follows from the component equalities recorded in
    `panValueProgramStateRel`. -/

/-- Expression-level counterpart of Cake's `compile_eval_correct`: evaluation
    is invariant under `panValueProgramStateRel` (locals are passed
    explicitly because `PanValueProgramState` does not store them). -/
theorem evalPanValueExp_panValueProgramStateRel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals : VarName → Option (PanValue α))
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (expression : Exp α) (memoryAccess : Option (PanValueMemoryAccess α))
    (value : PanValue α)
    (hs : evalPanValueExp structs locals s.globals s.memory s.baseAddress
        s.topAddress s.bytesInWord expression (memoryAccess := memoryAccess) =
      some value) :
    evalPanValueExp structs locals t.globals t.memory t.baseAddress
      t.topAddress t.bytesInWord expression (memoryAccess := memoryAccess) =
      some value := by
  obtain ⟨_hstructs, hglobals, hmemory, _hret, _hparam, _hexn, hbase, htop,
    hbiw, _hfuncs⟩ := hrel
  simpa only [hglobals, hmemory, hbase, htop, hbiw] using hs

/-! Compose declaration-state adequacy with the expression evaluator.  This is
    the concrete argument-evaluation step needed by Cake's
    `state_rel_imp_semantics_decls_to_crep` call branch: after the declarations
    have produced a related target state, a successful source argument keeps
    the same value in that post-declaration target state.  The evaluator
    equations and the post-state relation are produced by this theorem; they
    are not merely carried as caller premises. -/
theorem panValueProgramStateRel_evalDeclarations_evalExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (s' : PanValueProgramState α)
    (expression : Exp α) (value : PanValue α)
    (hs : evalPanValueDeclarations s declarations memoryAccess = some s')
    (hvalue : evalPanValueExp s'.structs (fun _ => none) s'.globals
        s'.memory s'.baseAddress s'.topAddress s'.bytesInWord expression
        (memoryAccess := memoryAccess) = some value) :
    ∃ t', evalPanValueDeclarations t (panSimpDecls declarations) memoryAccess = some t' ∧
      panValueProgramStateRel s' t' ∧
      evalPanValueExp s'.structs (fun _ => none) t'.globals
        t'.memory t'.baseAddress t'.topAddress t'.bytesInWord expression
        (memoryAccess := memoryAccess) = some value := by
  obtain ⟨t', ht, hrel'⟩ := panValueProgramStateRel_evalPanValueDeclarations
    s t hrel declarations memoryAccess s' hs
  refine ⟨t', ht, hrel', ?_⟩
  exact evalPanValueExp_panValueProgramStateRel s'.structs (fun _ => none)
    s' t' hrel' expression memoryAccess value hvalue

/-! Cake's `OPT_MMAP_eval_some_eq` (`pan_simpProofScript.sml:518`): a whole
    list of expressions that evaluates successfully evaluates to the same
    values under `state_rel`.  This is Cake's `OPT_MMAP_eval_some_eq`, whose
    `OPT_MMAP` is `List.mapM` for `Option`, and it is the list-level consumer
    of the `compile_eval_correct` bridge above. -/

/-- List-level counterpart of Cake's `OPT_MMAP_eval_some_eq`: if a list of
    expressions maps successfully under `state_rel`-related states, the
    mapped values agree. -/
theorem list_mapM_eval_panValueProgramStateRel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals : VarName → Option (PanValue α))
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (expressions : List (Exp α)) (values : List (PanValue α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hs : expressions.mapM (fun expression =>
        evalPanValueExp structs locals s.globals s.memory s.baseAddress
          s.topAddress s.bytesInWord expression (memoryAccess := memoryAccess)) =
      some values) :
    expressions.mapM (fun expression =>
      evalPanValueExp structs locals t.globals t.memory t.baseAddress
        t.topAddress t.bytesInWord expression (memoryAccess := memoryAccess)) =
      some values :=
  list_mapM_eq_some_of_eq_some
    (fun expression => evalPanValueExp structs locals s.globals s.memory
      s.baseAddress s.topAddress s.bytesInWord expression
      (memoryAccess := memoryAccess))
    (fun expression => evalPanValueExp structs locals t.globals t.memory
      t.baseAddress t.topAddress t.bytesInWord expression
      (memoryAccess := memoryAccess))
    expressions values hs
    (fun expression _ value heval =>
      evalPanValueExp_panValueProgramStateRel structs locals s t hrel expression
        memoryAccess value heval)

/-! Cake's `evaluate_decls_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1518`):

        !s pan_code s'. evaluate_decls s pan_code = SOME s' ==>
                     s'.code = s.code |++ functions pan_code

    Evaluating a declaration list installs exactly the function declarations it
    contains, in source order, leaving every other declaration constructor
    untouched.  Cake's `|++` folds map updates in source order, so a later
    function wins; Flapjack's function table is a lookup list that prepends each
    installed function, so the accumulated table is the reversed source-order
    projection of `functions`. -/

/-- Source-order projection of a declaration list's function entries into the
    `(name, parameter names, body)` shape stored by `PanValueProgramState`. -/
def panFunctionEntries (declarations : List (Decl α)) :
    List (FunName × List VarName × Prog α) :=
  (functions declarations).reverse.map
    (fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
      (entry.1, entry.2.1.map Prod.fst, entry.2.2.1))

/-- Source-order projection of a declaration list's function entries into the
    `(name, return shape)` pairs stored in `returnShapes`. -/
def panReturnShapeEntries (declarations : List (Decl α)) : InfoMap Shape :=
  (functions declarations).reverse.map
    (fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
      (entry.1, entry.2.2.2))

/-- Source-order projection of a declaration list's function entries into the
    `(name, parameters)` pairs stored in `parameterShapes`. -/
def panParameterShapeEntries (declarations : List (Decl α)) :
    InfoMap (List (VarName × Shape)) :=
  (functions declarations).reverse.map
    (fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
      (entry.1, entry.2.1))

/-- Cake's `evaluate_decls_functions` (`panPropsScript.sml:1518`): a successful
    declaration evaluation only prepends the list's function entries to the
    function table. -/
theorem evalPanValueDeclarationsWithStructs_functions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state'.functions = panFunctionEntries declarations ++ state.functions := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      simp [panFunctionEntries, functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration with
      | name struct fields =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          rw [ih state heval]
          simp [panFunctionEntries, functions, functionEntries]
      | decl shape name expression =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          cases hval : evalPanValueExp structs (fun _ => none) state.globals
              state.memory state.baseAddress state.topAddress state.bytesInWord
              expression (memoryAccess := memoryAccess) with
          | none => simp [hval] at heval
          | some value =>
              by_cases hmatch :
                  panShapeMatches (panValueShape structs value) shape = true
              · simp [hval, hmatch] at heval
                rw [ih _ heval]
                simp [panFunctionEntries, functions, functionEntries]
              · simp [hval, hmatch] at heval
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at heval
            rw [ih _ heval]
            simp [panFunctionEntries, functions, functionEntries, List.reverse_cons, List.map_append]
          · simp [hwf] at heval
      | exnDecl exception shape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at heval
              rw [ih _ heval]
              simp [panFunctionEntries, functions, functionEntries]
            · simp [hexists, hwf] at heval

/-! Cake's `evaluate_decls_eshapes`
    (`cakeml/pancake/semantics/panPropsScript.sml:1409`):

        !s ds s'. evaluate_decls s ds = SOME s' ==>
                     s'.eshapes = s.eshapes |++ exceptions ds

    The exception-table counterpart of `evaluate_decls_functions`: a successful
    declaration evaluation only prepends the list's exception declarations, in
    source order, to the exception-shape table.  Flapjack prepends each
    installed exception, so the accumulated table is the reversed source-order
    projection of `exceptionEntries`. -/

/-- Source-order projection of a declaration list's exception entries into the
    `(exception, shape)` pairs stored by `PanValueProgramState`. -/
def panExceptionEntries (declarations : List (Decl α)) : List (ExceptionId × Shape) :=
  (exceptionEntries declarations).reverse

theorem panExceptionEntries_nil : panExceptionEntries ([] : List (Decl α)) = [] := by
  simp [panExceptionEntries, exceptionEntries]

theorem panExceptionEntries_cons (declaration : Decl α) (declarations : List (Decl α)) :
    panExceptionEntries (declaration :: declarations) =
      (match declaration with
       | .exnDecl exception shape =>
           panExceptionEntries declarations ++ [(exception, shape)]
       | _ => panExceptionEntries declarations) := by
  cases declaration <;>
    simp [panExceptionEntries, exceptionEntries_cons, List.reverse_cons]

/-- Cake's `evaluate_decls_eshapes` (`panPropsScript.sml:1409`): a successful
    declaration evaluation only prepends the list's exception entries to the
    exception-shape table. -/
theorem evalPanValueDeclarationsWithStructs_exceptions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state'.exceptions = panExceptionEntries declarations ++ state.exceptions := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      simp [panExceptionEntries_nil]
  | cons declaration declarations ih =>
      cases declaration with
      | name struct fields =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          rw [ih state heval]
          simp [panExceptionEntries_cons]
      | decl shape name expression =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          cases hval : evalPanValueExp structs (fun _ => none) state.globals
              state.memory state.baseAddress state.topAddress state.bytesInWord
              expression (memoryAccess := memoryAccess) with
          | none => simp [hval] at heval
          | some value =>
              by_cases hmatch :
                  panShapeMatches (panValueShape structs value) shape = true
              · simp [hval, hmatch] at heval
                rw [ih _ heval]
                simp [panExceptionEntries_cons]
              · simp [hval, hmatch] at heval
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at heval
            rw [ih _ heval]
            simp [panExceptionEntries_cons]
          · simp [hwf] at heval
      | exnDecl exception shape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at heval
              rw [ih _ heval]
              simp [panExceptionEntries_cons, List.append_assoc]
            · simp [hexists, hwf] at heval

/-! The same Cake `evaluate_decls_eshapes` equation at the public declaration
    evaluator.  This wrapper exposes the exception table after struct
    collection, which is the state needed by a later raised-call lookup. -/
theorem evalPanValueDeclarations_exceptions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    state'.exceptions = panExceptionEntries declarations ++ state.exceptions := by
  simp only [evalPanValueDeclarations] at heval
  cases hcollect : collectPanValueStructs declarations state.structs with
  | none => simp [hcollect] at heval
  | some structs =>
      simp only [hcollect] at heval
      exact evalPanValueDeclarationsWithStructs_exceptions structs
        { state with structs := structs } state' declarations memoryAccess heval

/-! Compose the public declaration-state equation with Cake's top-level raised
    call boundary.  The result keeps both the raised payload and the exception
    table available to the caller instead of hiding lookup in a premise. -/
theorem evalPanValueProgram_of_declarations_and_raised_call_with_exception_state
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α)) (entry : FunName)
    (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (state : PanValueProgramState α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (exception : ExceptionId)
    (value : PanValue α)
    (hdeclarations : evalPanValueDeclarations initial declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi
      state.structs state.functions state.baseAddress state.topAddress
      state.bytesInWord fuel (fun _ => none) state.globals state.memory none
      entry arguments (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value)) :
    evalPanValueProgram initial primitive ffi fuel declarations entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value) ∧
    state.exceptions = panExceptionEntries declarations ++ initial.exceptions := by
  constructor
  · exact evalPanValueProgram_of_declarations_and_raised_call initial primitive ffi
      fuel declarations entry arguments memoryAccess memoryHandler state locals globals
      memory exception value hdeclarations hcall
  · exact evalPanValueDeclarations_exceptions initial state declarations memoryAccess
      hdeclarations

/-! Package the public declaration facts needed by the raised evaluator: the
    collected struct context makes the exception payload shape well formed, and
    the resulting state carries Cake's exact exception table equation. -/
theorem evalPanValueDeclarations_exception_state_evidence
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    {exception : ExceptionId} {shape : Shape}
    (hmem : (.exnDecl exception shape : Decl α) ∈ declarations)
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    ∃ structs : StructContext,
      collectPanValueStructs declarations state.structs = some structs ∧
        state'.exceptions = panExceptionEntries declarations ++ state.exceptions ∧
        isWfShape structs shape = true := by
  obtain ⟨structs, hcollect, hwf⟩ :=
    evalPanValueDeclarations_exceptions_wf state state' declarations memoryAccess
      heval hmem
  exact ⟨structs, hcollect,
    evalPanValueDeclarations_exceptions state state' declarations memoryAccess heval,
    hwf⟩

/-! A declared exception remains present in the table installed by successful
    declaration evaluation.  This is the lookup-success half of the generic
    raised evaluator bridge; the actual target exception code remains a
    separate compiler-context premise. -/
theorem panExceptionEntries_mem_of_exnDecl_mem
    (declarations : List (Decl α)) {exception : ExceptionId} {shape : Shape}
    (hmem : (.exnDecl exception shape : Decl α) ∈ declarations) :
    (exception, shape) ∈ panExceptionEntries declarations := by
  induction declarations with
  | nil => simp at hmem
  | cons declaration declarations ih =>
      cases declaration with
      | name name fields =>
          simp only [panExceptionEntries_cons] at ⊢
          exact ih (by simpa using hmem)
      | decl declShape name value =>
          simp only [panExceptionEntries_cons] at ⊢
          exact ih (by simpa using hmem)
      | function declaration =>
          simp only [panExceptionEntries_cons] at ⊢
          exact ih (by simpa using hmem)
      | exnDecl declaredException declaredShape =>
          simp only [panExceptionEntries_cons]
          simp only [List.mem_cons] at hmem
          rcases hmem with hhead | hmem
          · injection hhead with hException hShape
            subst exception
            subst shape
            exact List.mem_append_right _ (by simp)
          · exact List.mem_append_left _ (ih hmem)

theorem evalPanValueDeclarations_exception_lookup_isSome
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    {exception : ExceptionId} {shape : Shape}
    (hmem : (.exnDecl exception shape : Decl α) ∈ declarations)
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    (lookupInfo exception state'.exceptions).isSome = true := by
  have hentries : (exception, shape) ∈ panExceptionEntries declarations :=
    panExceptionEntries_mem_of_exnDecl_mem declarations hmem
  have htable := evalPanValueDeclarations_exceptions state state' declarations
    memoryAccess heval
  rw [htable]
  have hname : exception ∈ (panExceptionEntries declarations).map Prod.fst :=
    List.mem_map.mpr ⟨(exception, shape), hentries, rfl⟩
  have hname' : exception ∈
      (panExceptionEntries declarations ++ state.exceptions).map Prod.fst := by
    simp only [List.map_append]
    exact List.mem_append_left _ hname
  exact lookupInfo_isSome_of_mem exception
    (panExceptionEntries declarations ++ state.exceptions) hname'

theorem evalPanValueDeclarations_exception_shape_lookup
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    {exception : ExceptionId} {shape : Shape}
    (hmem : (.exnDecl exception shape : Decl α) ∈ declarations)
    (hnodup : (state'.exceptions.map Prod.fst).Nodup)
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    lookupInfo exception state'.exceptions = some shape := by
  have hentries : (exception, shape) ∈ panExceptionEntries declarations :=
    panExceptionEntries_mem_of_exnDecl_mem declarations hmem
  have htable := evalPanValueDeclarations_exceptions state state' declarations
    memoryAccess heval
  have hnodup' :
      ((panExceptionEntries declarations ++ state.exceptions).map Prod.fst).Nodup := by
    rw [← htable]
    exact hnodup
  rw [htable]
  exact lookupInfo_eq_some_of_mem_of_nodup exception
    (panExceptionEntries declarations ++ state.exceptions) shape
    (List.mem_append_left _ hentries) hnodup'

/-! Package the source-side raised call with the declaration-derived exception
    context.  This is the evaluator evidence needed before a generic raised
    payload can be related to the compiled exception code: the successful
    program result, collected struct context, exact exception-table equation,
    and well-formed declared payload shape are all retained. -/
theorem evalPanValueProgram_of_declarations_and_raised_call_with_exception_evidence
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α)) (entry : FunName)
    (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (state : PanValueProgramState α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (exception : ExceptionId)
    (value : PanValue α) (shape : Shape)
    (hmem : (.exnDecl exception shape : Decl α) ∈ declarations)
    (hdeclarations : evalPanValueDeclarations initial declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi
      state.structs state.functions state.baseAddress state.topAddress
      state.bytesInWord fuel (fun _ => none) state.globals state.memory none
      entry arguments (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value)) :
    evalPanValueProgram initial primitive ffi fuel declarations entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value) ∧
    ∃ structs : StructContext,
      collectPanValueStructs declarations initial.structs = some structs ∧
        state.exceptions = panExceptionEntries declarations ++ initial.exceptions ∧
        isWfShape structs shape = true := by
  refine ⟨(evalPanValueProgram_of_declarations_and_raised_call_with_exception_state
    initial primitive ffi fuel declarations entry arguments memoryAccess
    memoryHandler state locals globals memory exception value hdeclarations hcall).1,
    ?_⟩
  exact evalPanValueDeclarations_exception_state_evidence initial state
    declarations memoryAccess hmem hdeclarations

/-! Combine the successful raised-program witness with the declaration-derived
    exception lookup.  This is the source-side evidence needed by the generic
    clocked result bridge; the target exception code remains an explicit
    relation premise at that boundary. -/
theorem evalPanValueProgram_of_declarations_and_raised_call_with_exception_lookup_evidence
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α)) (entry : FunName)
    (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (state : PanValueProgramState α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (exception : ExceptionId)
    (value : PanValue α) (shape : Shape)
    (hmem : (.exnDecl exception shape : Decl α) ∈ declarations)
    (hdeclarations : evalPanValueDeclarations initial declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi
      state.structs state.functions state.baseAddress state.topAddress
      state.bytesInWord fuel (fun _ => none) state.globals state.memory none
      entry arguments (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value)) :
    evalPanValueProgram initial primitive ffi fuel declarations entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value) ∧
    ∃ structs : StructContext,
      collectPanValueStructs declarations initial.structs = some structs ∧
        state.exceptions = panExceptionEntries declarations ++ initial.exceptions ∧
        isWfShape structs shape = true ∧
        (lookupInfo exception state.exceptions).isSome = true := by
  have hprogram :=
    evalPanValueProgram_of_declarations_and_raised_call_with_exception_evidence
      initial primitive ffi fuel declarations entry arguments memoryAccess memoryHandler
      state locals globals memory exception value shape hmem hdeclarations hcall
  have hlookup := evalPanValueDeclarations_exception_lookup_isSome
    initial state declarations memoryAccess hmem hdeclarations
  rcases hprogram with ⟨hprogram, structs, hcollect, hexceptions, hwf⟩
  exact ⟨hprogram, structs, hcollect, hexceptions, hwf, hlookup⟩

/-! Cake's `evaluate_decls_only_exn_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1436`): when every
    declaration is an exception declaration, successful evaluation changes
    only the exception-shape table.  This stronger state equation is useful
    when composing the exception environment with later function/global
    declarations. -/
theorem evalPanValueDeclarationsWithStructs_only_exn_decls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all isExnDecl = true)
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state' = { state with
      structs := structs
      exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      rw [panExceptionEntries_nil, List.nil_append, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hexndecl : isExnDecl declaration = true := hhead
      cases declaration with
      | exnDecl exception shape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at heval
              rw [ih _ (by rfl) htail heval]
              simp [panExceptionEntries_cons, List.append_assoc]
            · simp [hexists, hwf] at heval
      | function _ => simp [isExnDecl] at hexndecl
      | decl _ _ _ => simp [isExnDecl] at hexndecl
      | name _ _ => simp [isExnDecl] at hexndecl

/-- Cake's `evaluate_decls_only_exn_decls` (`panPropsScript.sml:1436`) at the
    `evalPanValueDeclarations` level: struct-name collection is a no-op for an
    exception-only declaration list, so the state's struct context is kept. -/
theorem evalPanValueDeclarations_only_exn_decls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all isExnDecl = true)
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    state' = { state with
      exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  simp only [evalPanValueDeclarations] at heval
  cases hcollect : collectPanValueStructs declarations state.structs with
  | none => simp [hcollect] at heval
  | some structs =>
      simp only [hcollect] at heval
      have hnames : declarations.all (fun declaration => !isName declaration) = true := by
        refine List.all_eq_true.mpr (fun declaration hmem => ?_)
        have h := List.all_eq_true.mp hall declaration hmem
        cases declaration <;> simp_all [isExnDecl, isName]
      have hstructs : structs = state.structs := by
        have hno := collectPanValueStructs_of_no_names state.structs declarations hnames
        rw [hcollect] at hno
        exact Option.some.inj hno
      subst hstructs
      have hmain := evalPanValueDeclarationsWithStructs_only_exn_decls state.structs
        { state with structs := state.structs } state' declarations memoryAccess
        (by rfl) hall heval
      simpa using hmain

/-! Cake's `evaluate_decls_names`
    (`cakeml/pancake/semantics/panPropsScript.sml:1552`): a declaration list
    consisting only of structure names is skipped by declaration evaluation. -/
theorem evalPanValueDeclarationsWithStructs_names
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all isName = true) :
    evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state := by
  induction declarations with
  | nil =>
      simp [evalPanValueDeclarationsWithStructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hname : isName declaration = true := hhead
      cases declaration with
      | name name fields =>
          simp only [evalPanValueDeclarationsWithStructs]
          exact ih htail
      | decl shape name expression =>
          simp [isName] at hname
      | function declaration =>
          simp [isName] at hname
      | exnDecl exception shape =>
          simp [isName] at hname

/-- Cake's `evaluate_decls_only_funs_and_exn_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1561`): when every declaration
    is a function or an exception declaration, a successful evaluation changes
    only the function and exception tables, together with Flapjack's separate
    return-shape and parameter-shape maps. -/
theorem evalPanValueDeclarationsWithStructs_only_funs_and_exn_decls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all
      (fun declaration =>
        globalDeclIsFunction declaration || isExnDecl declaration) = true)
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state' = { state with
      structs := structs
      functions := panFunctionEntries declarations ++ state.functions
      returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
      parameterShapes :=
        panParameterShapeEntries declarations ++ state.parameterShapes
      exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      simp [panFunctionEntries, panReturnShapeEntries, panParameterShapeEntries,
        panExceptionEntries, functions, functionEntries, exceptionEntries, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at heval
            rw [ih _ (by rfl) htail heval]
            simp [panFunctionEntries, panReturnShapeEntries,
              panParameterShapeEntries, panExceptionEntries, functions, functionEntries,
              exceptionEntries, List.reverse_cons, List.map_append,
              List.append_assoc]
          · simp [hwf] at heval
      | exnDecl exception shape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at heval
              rw [ih _ (by rfl) htail heval]
              simp [panFunctionEntries, panReturnShapeEntries,
                panParameterShapeEntries, panExceptionEntries_cons, functions, functionEntries,
                List.append_assoc]
            · simp [hexists, hwf] at heval
      | decl shape name expression =>
          simp [globalDeclIsFunction, isExnDecl] at hhead
      | name name fields =>
          simp [globalDeclIsFunction, isExnDecl] at hhead

/-! Cake's `evaluate_decls_only_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1528`): a function-only
    declaration list changes only the function, return-shape, and
    parameter-shape tables.  This specializes the mixed function/exception
    equation while making the absence of exception entries explicit. -/
theorem evalPanValueDeclarationsWithStructs_only_functions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all globalDeclIsFunction = true)
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state' = { state with
      structs := structs
      functions := panFunctionEntries declarations ++ state.functions
      returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
      parameterShapes :=
        panParameterShapeEntries declarations ++ state.parameterShapes } := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      simp [panFunctionEntries, panReturnShapeEntries, panParameterShapeEntries,
        functions, functionEntries, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at heval
            rw [ih _ (by rfl) htail heval]
            simp [panFunctionEntries, panReturnShapeEntries,
              panParameterShapeEntries, functions, functionEntries, List.reverse_cons,
              List.map_append, List.append_assoc]
          · simp [hwf] at heval
      | decl shape name expression =>
          simp [globalDeclIsFunction] at hhead
      | exnDecl exception shape =>
          simp [globalDeclIsFunction] at hhead
      | name name fields =>
          simp [globalDeclIsFunction] at hhead

/-- Cake's `evaluate_decls_only_functions` (`panPropsScript.sml:1529`) at the
    `evalPanValueDeclarations` level: struct-name collection is a no-op for a
    function-only declaration list, so the state's struct context is kept. -/
theorem evalPanValueDeclarations_only_functions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all globalDeclIsFunction = true)
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    state' = { state with
      functions := panFunctionEntries declarations ++ state.functions
      returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
      parameterShapes :=
        panParameterShapeEntries declarations ++ state.parameterShapes } := by
  simp only [evalPanValueDeclarations] at heval
  cases hcollect : collectPanValueStructs declarations state.structs with
  | none => simp [hcollect] at heval
  | some structs =>
      simp only [hcollect] at heval
      have hstructs : structs = state.structs := by
        have hno := collectPanValueStructs_of_functions state.structs declarations hall
        rw [hcollect] at hno
        exact Option.some.inj hno
      subst hstructs
      have hmain := evalPanValueDeclarationsWithStructs_only_functions state.structs
        { state with structs := state.structs } state' declarations memoryAccess
        (by rfl) hall heval
      simpa using hmain

/-- Cake's `evaluate_decls_only_functions_SOME`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2390`): when every
    declaration is a function declaration whose parameter and return shapes are
    well formed, evaluation succeeds and installs exactly the function table
    together with Flapjack's separate return-shape and parameter-shape maps.
    This is the converse direction of
    `evalPanValueDeclarationsWithStructs_only_functions`. -/
theorem evalPanValueDeclarationsWithStructs_only_functions_sufficiency
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all globalDeclIsFunction = true)
    (hwf : ∀ declaration, declaration ∈ declarations →
      (match declaration with
        | .function function =>
            function.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs function.returnShape
        | _ => true) = true) :
    evalPanValueDeclarationsWithStructs structs state declarations memoryAccess =
      some { state with
        structs := structs
        functions := panFunctionEntries declarations ++ state.functions
        returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
        parameterShapes :=
          panParameterShapeEntries declarations ++ state.parameterShapes } := by
  induction declarations generalizing state with
  | nil =>
      simp [evalPanValueDeclarationsWithStructs, panFunctionEntries,
        panReturnShapeEntries, panParameterShapeEntries, functions, functionEntries, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs]
          have hdeclWf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true :=
            hwf (.function declaration) (by simp)
          rw [if_pos hdeclWf]
          rw [ih _ (by rfl) htail
            (fun other hmem => hwf other (by simp [hmem]))]
          simp [panFunctionEntries, panReturnShapeEntries,
            panParameterShapeEntries, functions, functionEntries, List.reverse_cons,
            List.map_append, List.append_assoc]
      | decl shape name expression =>
          simp [globalDeclIsFunction] at hhead
      | exnDecl exception shape =>
          simp [globalDeclIsFunction] at hhead
      | name name fields =>
          simp [globalDeclIsFunction] at hhead

/-! Cake's `exns_wf_evaluate_decls` (`cakeml/pancake/semantics/panPropsScript.sml:1448`):
    for an exception-only declaration list the exception-table well-formedness
    conditions (distinct ids, ids absent from the incoming table, well-formed
    shapes) are sufficient for the evaluator to succeed and install exactly
    that table.  This is the converse direction of
    `evalPanValueDeclarationsWithStructs_exceptions_wf`. -/

theorem lookupInfo_of_ne [BEq String] {name candidate : String} {value : α}
    {entries : InfoMap α} (hne : (candidate == name) = false) :
    lookupInfo name ((candidate, value) :: entries) =
      lookupInfo name entries := by
  simp [lookupInfo, hne]

theorem evalPanValueDeclarationsWithStructs_exns_wf_sufficiency
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all isExnDecl = true)
    (hnodup :
      ((panExceptionEntries declarations).map (fun entry => entry.1)).Nodup)
    (hnone : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        lookupInfo exception state.exceptions = none)
    (hwf : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        isWfShape structs shape = true) :
    evalPanValueDeclarationsWithStructs structs state declarations memoryAccess =
      some { state with
        structs := structs
        exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  induction declarations generalizing state with
  | nil =>
      simp [evalPanValueDeclarationsWithStructs, panExceptionEntries_nil,
        List.nil_append, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function function => simp [isExnDecl] at hhead
      | decl shape name expression => simp [isExnDecl] at hhead
      | exnDecl exception shape =>
          simp only [panExceptionEntries_cons]
          simp only [evalPanValueDeclarationsWithStructs]
          have hheadNone : lookupInfo exception state.exceptions = none :=
            hnone exception shape (by simp [panExceptionEntries_cons])
          have hheadWf : isWfShape structs shape = true :=
            hwf exception shape (by simp [panExceptionEntries_cons])
          rw [hheadNone]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false,
            hheadWf, if_true]
          simp only [panExceptionEntries_cons, List.map_append, List.map_cons,
            List.map_nil] at hnodup
          obtain ⟨hnodupTail, _, hdisjoint⟩ := List.nodup_append.mp hnodup
          let next : PanValueProgramState α :=
            { state with
              structs := structs
              exceptions := (exception, shape) :: state.exceptions }
          have htailNone : ∀ eid shape',
              (eid, shape') ∈ panExceptionEntries declarations →
                lookupInfo eid next.exceptions = none := by
            intro eid shape' hmem
            have heid : eid ∈ (panExceptionEntries declarations).map
                (fun entry => entry.1) :=
              List.mem_map.mpr ⟨(eid, shape'), hmem, rfl⟩
            have hne : (exception == eid) = false := by
              rw [Bool.eq_false_iff]
              intro h
              exact (hdisjoint eid heid exception (by simp))
                (beq_iff_eq.mp h).symm
            show lookupInfo eid ((exception, shape) :: state.exceptions) = none
            rw [lookupInfo_of_ne (name := eid) (candidate := exception)
              (value := shape) (entries := state.exceptions) hne]
            exact hnone eid shape' (by
              simp only [panExceptionEntries_cons]
              exact List.mem_append_left _ hmem)
          have htailWf : ∀ eid shape',
              (eid, shape') ∈ panExceptionEntries declarations →
                isWfShape structs shape' = true :=
            fun eid shape' hmem =>
              hwf eid shape' (by
                simp only [panExceptionEntries_cons]
                exact List.mem_append_left _ hmem)
          have hrec := ih next (by rfl) htail hnodupTail htailNone htailWf
          exact hrec.trans (by simp [next, List.append_assoc])
      | name struct fields => simp [isExnDecl] at hhead

/-- Cake's `exns_wf_evaluate_decls` at the `evalPanValueDeclarations` level:
    the exception-only list collects no struct names, so the incoming struct
    context is preserved. -/
theorem evalPanValueDeclarations_exns_wf_sufficiency
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (state : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all isExnDecl = true)
    (hnodup :
      ((panExceptionEntries declarations).map (fun entry => entry.1)).Nodup)
    (hnone : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        lookupInfo exception state.exceptions = none)
    (hwf : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        isWfShape state.structs shape = true) :
    evalPanValueDeclarations state declarations memoryAccess =
      some { state with
        exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  simp only [evalPanValueDeclarations]
  have hnames :
      declarations.all (fun declaration => !isName declaration) = true := by
    refine List.all_eq_true.mpr (fun declaration hmem => ?_)
    have h := List.all_eq_true.mp hall declaration hmem
    cases declaration <;> simp_all [isExnDecl, isName]
  rw [collectPanValueStructs_of_no_names state.structs declarations hnames]
  have hmain := evalPanValueDeclarationsWithStructs_exns_wf_sufficiency
    state.structs { state with structs := state.structs } declarations
    memoryAccess (by rfl) hall hnodup hnone hwf
  simpa using hmain

/-- Cake's `evaluate_decls_only_functions_and_exns_SOME`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2404`): for a list of
    function and exception declarations, the per-function parameter/return
    well-formedness conditions together with exception distinctness, freshness
    and shape well-formedness are sufficient for the evaluator to succeed and
    install exactly the function and exception tables.  This combines
    `evalPanValueDeclarationsWithStructs_only_functions_sufficiency` and
    `evalPanValueDeclarationsWithStructs_exns_wf_sufficiency`. -/
theorem evalPanValueDeclarationsWithStructs_only_functions_and_exns_sufficiency
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all
      (fun declaration =>
        globalDeclIsFunction declaration || isExnDecl declaration) = true)
    (hfunctions : ∀ declaration, declaration ∈ declarations →
      (match declaration with
        | .function function =>
            function.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs function.returnShape
        | _ => true) = true)
    (hnodup :
      ((panExceptionEntries declarations).map (fun entry => entry.1)).Nodup)
    (hnone : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        lookupInfo exception state.exceptions = none)
    (hexns : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        isWfShape structs shape = true) :
    evalPanValueDeclarationsWithStructs structs state declarations memoryAccess =
      some { state with
        structs := structs
        functions := panFunctionEntries declarations ++ state.functions
        returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
        parameterShapes :=
          panParameterShapeEntries declarations ++ state.parameterShapes
        exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  induction declarations generalizing state with
  | nil =>
      simp [evalPanValueDeclarationsWithStructs, panFunctionEntries,
        panReturnShapeEntries, panParameterShapeEntries, panExceptionEntries_nil,
        functions, functionEntries, List.nil_append, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function function =>
          simp only [evalPanValueDeclarationsWithStructs]
          have hdeclWf : (function.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs function.returnShape) = true :=
            hfunctions (.function function) (by simp)
          rw [if_pos hdeclWf]
          have hnodupTail :
              ((panExceptionEntries declarations).map
                (fun entry => entry.1)).Nodup := by
            simpa [panExceptionEntries_cons] using hnodup
          have hnoneTail : ∀ exception shape,
              (exception, shape) ∈ panExceptionEntries declarations →
                lookupInfo exception state.exceptions = none := by
            intro exception shape hmem
            exact hnone exception shape (by
              simpa [panExceptionEntries_cons] using hmem)
          have hexnsTail : ∀ exception shape,
              (exception, shape) ∈ panExceptionEntries declarations →
                isWfShape structs shape = true := by
            intro exception shape hmem
            exact hexns exception shape (by
              simpa [panExceptionEntries_cons] using hmem)
          let next : PanValueProgramState α :=
            { state with
              structs := structs
              functions :=
                (function.name, function.params.map Prod.fst, function.body) ::
                  state.functions
              returnShapes :=
                (function.name, function.returnShape) :: state.returnShapes
              parameterShapes :=
                (function.name, function.params) :: state.parameterShapes }
          exact (ih next (by rfl) htail
            (fun other hmem => hfunctions other (by simp [hmem]))
            hnodupTail hnoneTail hexnsTail).trans (by
              simp [next, panFunctionEntries, panReturnShapeEntries,
                panParameterShapeEntries, panExceptionEntries_cons, functions,
                functionEntries, List.reverse_cons, List.map_append,
                List.append_assoc])
      | exnDecl exception shape =>
          simp only [panExceptionEntries_cons]
          simp only [evalPanValueDeclarationsWithStructs]
          have hheadNone : lookupInfo exception state.exceptions = none :=
            hnone exception shape (by simp [panExceptionEntries_cons])
          have hheadWf : isWfShape structs shape = true :=
            hexns exception shape (by simp [panExceptionEntries_cons])
          rw [hheadNone]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false,
            hheadWf, if_true]
          simp only [panExceptionEntries_cons, List.map_append, List.map_cons,
            List.map_nil] at hnodup
          obtain ⟨hnodupTail, _, hdisjoint⟩ := List.nodup_append.mp hnodup
          let next : PanValueProgramState α :=
            { state with
              structs := structs
              exceptions := (exception, shape) :: state.exceptions }
          have hnoneTail : ∀ eid shape',
              (eid, shape') ∈ panExceptionEntries declarations →
                lookupInfo eid next.exceptions = none := by
            intro eid shape' hmem
            have heid : eid ∈ (panExceptionEntries declarations).map
                (fun entry => entry.1) :=
              List.mem_map.mpr ⟨(eid, shape'), hmem, rfl⟩
            have hne : (exception == eid) = false := by
              rw [Bool.eq_false_iff]
              intro h
              exact (hdisjoint eid heid exception (by simp))
                (beq_iff_eq.mp h).symm
            show lookupInfo eid ((exception, shape) :: state.exceptions) = none
            rw [lookupInfo_of_ne (name := eid) (candidate := exception)
              (value := shape) (entries := state.exceptions) hne]
            exact hnone eid shape' (by
              simp only [panExceptionEntries_cons]
              exact List.mem_append_left _ hmem)
          have hexnsTail : ∀ eid shape',
              (eid, shape') ∈ panExceptionEntries declarations →
                isWfShape structs shape' = true :=
            fun eid shape' hmem =>
              hexns eid shape' (by
                simp only [panExceptionEntries_cons]
                exact List.mem_append_left _ hmem)
          have hrec := ih next (by rfl) htail
            (fun other hmem => hfunctions other (by simp [hmem]))
            hnodupTail hnoneTail hexnsTail
          exact hrec.trans (by
            simp [next, panFunctionEntries,
              panReturnShapeEntries, panParameterShapeEntries, functions,
              functionEntries, List.append_assoc])
      | decl shape name expression =>
          simp [globalDeclIsFunction, isExnDecl] at hhead
      | name name fields =>
          simp [globalDeclIsFunction, isExnDecl] at hhead

theorem evalPanValueDeclarationsWithStructs_function_exnDecl_commute
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declaration : FunDecl α) (exception : ExceptionId) (shape : Shape)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueDeclarationsWithStructs structs state
        (.function declaration :: .exnDecl exception shape :: declarations)
        memoryAccess =
      evalPanValueDeclarationsWithStructs structs state
        (.exnDecl exception shape :: .function declaration :: declarations)
        memoryAccess := by
  simp only [evalPanValueDeclarationsWithStructs]
  by_cases hwf : (declaration.params.all
        (fun parameter => isWfShape structs parameter.2) &&
      isWfShape structs declaration.returnShape) = true
  · by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
    · simp [hwf, hexists]
    · by_cases hshape : isWfShape structs shape = true
      · simp [hwf, hexists, hshape]
      · simp [hwf, hexists, hshape]
  · by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
    · simp [hwf, hexists]
    · by_cases hshape : isWfShape structs shape = true
      · simp [hwf, hexists, hshape]
      · simp [hwf, hexists, hshape]

/-- Cake's `evaluate_decls_one_fun_last`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1854`): a function
    declaration may be moved to the front past a list of global and exception
    declarations. -/
theorem evalPanValueDeclarationsWithStructs_one_fun_last
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declaration : FunDecl α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hrest : declarations.all (fun declaration =>
      isDecl declaration || isExnDecl declaration) = true) :
    evalPanValueDeclarationsWithStructs structs state
        (declarations ++ [.function declaration]) memoryAccess =
      evalPanValueDeclarationsWithStructs structs state
        (.function declaration :: declarations) memoryAccess := by
  induction declarations generalizing state with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hrest
      obtain ⟨hhead, htail⟩ := hrest
      rw [List.cons_append]
      cases head with
      | function function => simp [isDecl, isExnDecl] at hhead
      | name name fields => simp [isDecl, isExnDecl] at hhead
      | decl shape name expression =>
          rw [evalPanValueDeclarationsWithStructs_function_decl_commute]
          simp only [evalPanValueDeclarationsWithStructs]
          cases hval : evalPanValueExp structs (fun _ => none) state.globals
              state.memory state.baseAddress state.topAddress state.bytesInWord
              expression (memoryAccess := memoryAccess) with
          | none => rfl
          | some value =>
              by_cases hmatch :
                  panShapeMatches (panValueShape structs value) shape = true
              · simp [hmatch]
                rw [ih _ htail]
                simp only [evalPanValueDeclarationsWithStructs]
              · simp [hmatch]
      | exnDecl exception shape =>
          rw [evalPanValueDeclarationsWithStructs_function_exnDecl_commute]
          simp only [evalPanValueDeclarationsWithStructs]
          rw [ih _ htail]
          simp only [evalPanValueDeclarationsWithStructs]

/-- The well-founded declaration filter agrees with `List.filter`, which makes
    the core list-filter API available for the resort argument. -/
theorem globalDeclsFilter_eq_filter (predicate : Decl α → Bool)
    (declarations : List (Decl α)) :
    globalDeclsFilter predicate declarations =
      List.filter predicate declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter]
  | cons declaration declarations ih =>
      cases h : predicate declaration <;> simp [globalDeclsFilter, h, ih]

theorem globalDeclsFilter_append (predicate : Decl α → Bool)
    (left right : List (Decl α)) :
    globalDeclsFilter predicate (left ++ right) =
      globalDeclsFilter predicate left ++ globalDeclsFilter predicate right := by
  simp only [globalDeclsFilter_eq_filter, List.filter_append]

/-- Exception declarations commute past global declarations. -/
theorem evalPanValueDeclarationsWithStructs_exnDecl_decl_commute
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (exception : ExceptionId) (shape : Shape)
    (declShape : Shape) (name : DeclarationName) (expression : Exp α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueDeclarationsWithStructs structs state
        (.exnDecl exception shape :: .decl declShape name expression :: declarations)
        memoryAccess =
      evalPanValueDeclarationsWithStructs structs state
        (.decl declShape name expression :: .exnDecl exception shape :: declarations)
        memoryAccess := by
  simp only [evalPanValueDeclarationsWithStructs]
  cases hval : evalPanValueExp structs (fun _ => none) state.globals
      state.memory state.baseAddress state.topAddress state.bytesInWord
      expression (memoryAccess := memoryAccess) with
  | none =>
      by_cases hexists : (lookupInfo exception state.exceptions).isSome = true <;>
        by_cases hshape : isWfShape structs shape = true <;>
        simp [hexists, hshape]
  | some value =>
      by_cases hmatch : panShapeMatches (panValueShape structs value) declShape = true <;>
        by_cases hexists : (lookupInfo exception state.exceptions).isSome = true <;>
        by_cases hshape : isWfShape structs shape = true <;>
        simp [hmatch, hexists, hshape]

/-- Bubbling a declaration that commutes with every element of `rest` to the
    end of that list. -/
theorem evalPanValueDeclarationsWithStructs_bubble_last
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (memoryAccess : Option (PanValueMemoryAccess α))
    (declaration : Decl α) (rest : List (Decl α))
    (hcomm : ∀ other ∈ rest, ∀ state tail,
      evalPanValueDeclarationsWithStructs structs state
          (declaration :: other :: tail) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state
          (other :: declaration :: tail) memoryAccess) :
    ∀ state,
      evalPanValueDeclarationsWithStructs structs state
          (declaration :: rest) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state
          (rest ++ [declaration]) memoryAccess := by
  induction rest with
  | nil => intro state; rw [List.nil_append]
  | cons other rest ih =>
      intro state
      have hcomm' : ∀ x ∈ rest, ∀ state tail,
          evalPanValueDeclarationsWithStructs structs state
              (declaration :: x :: tail) memoryAccess =
            evalPanValueDeclarationsWithStructs structs state
              (x :: declaration :: tail) memoryAccess :=
        fun x hx => hcomm x (List.mem_cons_of_mem other hx)
      rw [hcomm other (List.mem_cons_self ..) state rest]
      rw [List.cons_append]
      rw [show other :: declaration :: rest = [other] ++ (declaration :: rest) from rfl]
      rw [show other :: (rest ++ [declaration]) =
        [other] ++ (rest ++ [declaration]) from rfl]
      rw [evalPanValueDeclarationsWithStructs_append]
      rw [evalPanValueDeclarationsWithStructs_append]
      cases hstep : evalPanValueDeclarationsWithStructs structs state [other]
          memoryAccess with
      | none => rfl
      | some state' => exact ih hcomm' state'

/-- Moving a declaration out of a middle block and past a tail block it commutes
    with. -/
theorem evalPanValueDeclarationsWithStructs_insert_last
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (memoryAccess : Option (PanValueMemoryAccess α))
    (declaration : Decl α) (middle tail : List (Decl α))
    (hcomm : ∀ other ∈ tail, ∀ state rest,
      evalPanValueDeclarationsWithStructs structs state
          (declaration :: other :: rest) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state
          (other :: declaration :: rest) memoryAccess) :
    ∀ state,
      evalPanValueDeclarationsWithStructs structs state
          ((middle ++ [declaration]) ++ tail) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state
          ((middle ++ tail) ++ [declaration]) memoryAccess := by
  intro state
  rw [show (middle ++ [declaration]) ++ tail =
      middle ++ ([declaration] ++ tail) from by simp [List.append_assoc]]
  rw [show (middle ++ tail) ++ [declaration] =
      middle ++ (tail ++ [declaration]) from by simp [List.append_assoc]]
  rw [evalPanValueDeclarationsWithStructs_append]
  rw [evalPanValueDeclarationsWithStructs_append]
  cases h : evalPanValueDeclarationsWithStructs structs state middle memoryAccess with
  | none => rfl
  | some state' =>
      simpa using evalPanValueDeclarationsWithStructs_bubble_last structs memoryAccess
        declaration tail hcomm state'

/-- Cake's `resort_decls_evaluate`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1874`): the global pass's
    declaration resort preserves declaration evaluation. -/
theorem evalPanValueDeclarationsWithStructs_resortDecls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all (fun declaration =>
      isDecl declaration || isExnDecl declaration ||
        globalDeclIsFunction declaration) = true) :
    evalPanValueDeclarationsWithStructs structs state
        (globalResortDecls declarations) memoryAccess =
      evalPanValueDeclarationsWithStructs structs state declarations memoryAccess := by
  have h : ∀ reversed : List (Decl α),
      (reversed.reverse.all (fun declaration =>
        isDecl declaration || isExnDecl declaration ||
          globalDeclIsFunction declaration) = true) →
      evalPanValueDeclarationsWithStructs structs state
          (globalResortDecls reversed.reverse) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state reversed.reverse
          memoryAccess := by
    intro reversed
    induction reversed with
    | nil => intro _; simp [globalResortDecls, globalDeclsFilter]
    | cons declaration rest ih =>
        intro hall
        rw [List.reverse_cons]
        rw [List.reverse_cons] at hall
        have hdecl : (isDecl declaration || isExnDecl declaration ||
            globalDeclIsFunction declaration) = true :=
          List.all_eq_true.mp hall declaration
            (List.mem_append_right rest.reverse (List.mem_singleton_self declaration))
        have hallRest : rest.reverse.all (fun entry =>
            isDecl entry || isExnDecl entry ||
              globalDeclIsFunction entry) = true :=
          List.all_eq_true.mpr (fun entry hmem =>
            List.all_eq_true.mp hall entry
              (List.mem_append_left [declaration] hmem))
        have hbase := ih hallRest
        cases declaration with
        | function function =>
            have hresort : globalResortDecls (rest.reverse ++ [.function function]) =
                globalResortDecls rest.reverse ++ [.function function] := by
              simp only [globalResortDecls, globalDeclsFilter_append]
              simp [globalDeclsFilter, globalDeclIsName, globalDeclIsException,
                globalDeclIsGlobal, globalDeclIsFunction]
            rw [hresort]
            rw [evalPanValueDeclarationsWithStructs_append]
            rw [hbase]
            rw [evalPanValueDeclarationsWithStructs_append]
        | decl shape name expression =>
            have hresort : globalResortDecls
                (rest.reverse ++ [.decl shape name expression]) =
                (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse ++
                  globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                  [.decl shape name expression]) ++
                globalDeclsFilter globalDeclIsFunction rest.reverse := by
              simp only [globalResortDecls, globalDeclsFilter_append]
              simp [globalDeclsFilter, globalDeclIsName, globalDeclIsException,
                globalDeclIsGlobal, globalDeclIsFunction, List.append_assoc]
            have hcomm : ∀ other ∈
                  globalDeclsFilter globalDeclIsFunction rest.reverse,
                ∀ state' tail,
                  evalPanValueDeclarationsWithStructs structs state'
                      (.decl shape name expression :: other :: tail) memoryAccess =
                    evalPanValueDeclarationsWithStructs structs state'
                      (other :: .decl shape name expression :: tail) memoryAccess := by
              intro other hmem state' tail
              have hfun : globalDeclIsFunction other = true :=
                List.all_eq_true.mp
                  (globalDeclsFilter_all globalDeclIsFunction rest.reverse) other hmem
              cases other with
              | function function =>
                  exact (evalPanValueDeclarationsWithStructs_function_decl_commute
                    structs state' function shape name expression tail
                    memoryAccess).symm
              | decl _ _ _ => simp [globalDeclIsFunction] at hfun
              | exnDecl _ _ => simp [globalDeclIsFunction] at hfun
              | name _ _ => simp [globalDeclIsFunction] at hfun
            rw [hresort]
            rw [evalPanValueDeclarationsWithStructs_insert_last structs memoryAccess
              (.decl shape name expression)
              (globalDeclsFilter globalDeclIsName rest.reverse ++
                globalDeclsFilter globalDeclIsException rest.reverse ++
                globalDeclsFilter globalDeclIsGlobal rest.reverse)
              (globalDeclsFilter globalDeclIsFunction rest.reverse) hcomm]
            rw [show
              (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse ++
                  globalDeclsFilter globalDeclIsGlobal rest.reverse) ++
                globalDeclsFilter globalDeclIsFunction rest.reverse =
              globalResortDecls rest.reverse from rfl]
            rw [evalPanValueDeclarationsWithStructs_append]
            rw [hbase]
            rw [evalPanValueDeclarationsWithStructs_append]
        | exnDecl exception shape =>
            have hresort : globalResortDecls (rest.reverse ++ [.exnDecl exception shape]) =
                (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse ++
                  [.exnDecl exception shape]) ++
                (globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                  globalDeclsFilter globalDeclIsFunction rest.reverse) := by
              simp only [globalResortDecls, globalDeclsFilter_append]
              simp [globalDeclsFilter, globalDeclIsName, globalDeclIsException,
                globalDeclIsGlobal, globalDeclIsFunction, List.append_assoc]
            have hcomm : ∀ other ∈
                  globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                    globalDeclsFilter globalDeclIsFunction rest.reverse,
                ∀ state' tail,
                  evalPanValueDeclarationsWithStructs structs state'
                      (.exnDecl exception shape :: other :: tail) memoryAccess =
                    evalPanValueDeclarationsWithStructs structs state'
                      (other :: .exnDecl exception shape :: tail) memoryAccess := by
              intro other hmem state' tail
              rcases List.mem_append.mp hmem with hmem | hmem
              · have hglobal : globalDeclIsGlobal other = true :=
                  List.all_eq_true.mp
                    (globalDeclsFilter_all globalDeclIsGlobal rest.reverse) other hmem
                cases other with
                | decl declShape declName declExpr =>
                    exact evalPanValueDeclarationsWithStructs_exnDecl_decl_commute
                      structs state' exception shape declShape declName declExpr
                      tail memoryAccess
                | function _ => simp [globalDeclIsGlobal] at hglobal
                | exnDecl _ _ => simp [globalDeclIsGlobal] at hglobal
                | name _ _ => simp [globalDeclIsGlobal] at hglobal
              · have hfun : globalDeclIsFunction other = true :=
                  List.all_eq_true.mp
                    (globalDeclsFilter_all globalDeclIsFunction rest.reverse) other hmem
                cases other with
                | function function =>
                    exact (evalPanValueDeclarationsWithStructs_function_exnDecl_commute
                      structs state' function exception shape tail memoryAccess).symm
                | decl _ _ _ => simp [globalDeclIsFunction] at hfun
                | exnDecl _ _ => simp [globalDeclIsFunction] at hfun
                | name _ _ => simp [globalDeclIsFunction] at hfun
            rw [hresort]
            rw [evalPanValueDeclarationsWithStructs_insert_last structs memoryAccess
              (.exnDecl exception shape)
              (globalDeclsFilter globalDeclIsName rest.reverse ++
                globalDeclsFilter globalDeclIsException rest.reverse)
              (globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                globalDeclsFilter globalDeclIsFunction rest.reverse) hcomm]
            rw [show
              (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse) ++
                (globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                  globalDeclsFilter globalDeclIsFunction rest.reverse) =
              globalResortDecls rest.reverse from by
              rw [globalResortDecls]
              exact (List.append_assoc
                (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse)
                (globalDeclsFilter globalDeclIsGlobal rest.reverse)
                (globalDeclsFilter globalDeclIsFunction rest.reverse)).symm]
            rw [evalPanValueDeclarationsWithStructs_append]
            rw [hbase]
            rw [evalPanValueDeclarationsWithStructs_append]
        | name name fields =>
            simp [isDecl, isExnDecl, globalDeclIsFunction] at hdecl
  simpa using h declarations.reverse (by simpa using hall)

/-- Cake's `resort_decls_evaluate_IMP`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1943`). -/
theorem evalPanValueDeclarationsWithStructs_resortDecls_imp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all (fun declaration =>
      isDecl declaration || isExnDecl declaration ||
        globalDeclIsFunction declaration) = true)
    (heval : evalPanValueDeclarationsWithStructs structs state
        (globalResortDecls declarations) memoryAccess = some state') :
    evalPanValueDeclarationsWithStructs structs state declarations memoryAccess =
      some state' := by
  rw [evalPanValueDeclarationsWithStructs_resortDecls structs state declarations
    memoryAccess hall] at heval
  exact heval

/-! ## Flapjack-only `pan_simp` helper slice

The syntactic preservation lemmas below are the HOL declarations from
`cakeml/pancake/proofs/pan_simpProofScript.sml` that the `compile_correct`
proof uses, but they are stated over the production String-keyed
`Prog`/`Decl` transformations (`expIds`, `retToTail`, `seqAssoc`,
`panSimpDecls`, `panSimpProg`) in `Flapjack/Pancake/PanSimp.lean`, while the
HOL originals use the exact `mlstring`-keyed panLang syntax.  The `@[hol]`
tags were therefore withdrawn (bead flapjack-4ac.8) and the exact ports are
tracked by flapjack-4ac.8 (blocked by the exact-transformation prerequisite
flapjack-4ac.8.1). -/

theorem expIdsRetToTailEq (program : Prog α) :
    expIds (retToTail program) = expIds program :=
  expIds_retToTail program

theorem expIdsSeqAssocEq (pre program : Prog α) :
    expIds (seqAssoc pre program) = expIds pre ++ expIds program :=
  expIds_seqAssoc pre program

theorem expIdsCompileEq (program : Prog α) :
    expIds (panSimpProg program) = expIds program :=
  expIds_panSimpProg program

theorem sizeOfEidsPanSimpDeclsEq (declarations : List (Decl α)) :
    sizeOfEids (panSimpDecls declarations) = sizeOfEids declarations := by
  rw [panSimpDecls_eq_map, sizeOfEids_map_panSimpDecl]

theorem mapSndFEq {α β γ δ ε : Type} (entries : List (α × β × γ))
    (f : γ → δ) (g : δ → ε) :
    entries.map (fun entry => g (f entry.2.2)) =
      (entries.map (fun entry => entry.2.2)).map (fun body => g (f body)) := by
  rw [List.map_map]
  congr 1

theorem functionsCompileProg (declarations : List (Decl α)) :
    functions (panSimpDecls declarations) =
      (functions declarations).map (fun entry =>
        (entry.1, entry.2.1, panSimpProg entry.2.2.1, entry.2.2.2)) :=
  functions_panSimpDecls declarations

theorem firstCompileProgAllDistinctPanSimp (declarations : List (Decl α))
    (hnames : ((functions declarations).map (fun entry => entry.1)).Nodup) :
    ((functions (panSimpDecls declarations)).map (fun entry => entry.1)).Nodup :=
  functions_panSimpDecls_names_nodup declarations hnames

end Flapjack
