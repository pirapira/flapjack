import Flapjack.HolRef
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.CrepInline
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Basis.Pure.MlString
import Std.Data.HashSet.Lemmas

/-!
The first executable call-substitution layer for Crepe.

The inline map is represented as the finite list used by the CakeML pass.  This
slice performs one direct call substitution; recursive traversal of the
inlined callee is a separate layer so its termination measure stays explicit.
-/

namespace Flapjack

abbrev CrepInlineEntry (α : Type u) := FunName × (List Nat × CrepProg α)

def crepInlineLookup [BEq FunName] (name : FunName) :
    List (CrepInlineEntry α) → Option (List Nat × CrepProg α)
  | [] => none
  | (candidate, definition) :: entries =>
      if name == candidate then some definition else crepInlineLookup name entries

def crepInlineRemove [BEq FunName] (name : FunName) :
    List (CrepInlineEntry α) → List (CrepInlineEntry α)
  | [] => []
  | entry :: entries =>
      if entry.1 == name then crepInlineRemove name entries
      else entry :: crepInlineRemove name entries

/-- Temporary-name generator.  Calls the generic `crepExpVars`; the tagged
    width-indexed `crepExpVarsW` is a definitional delegation of it, so this
    executed use computes the identical function (`flapjack-pxn.18.4.3.82`). -/
def crepInlineTmpNames (arguments argumentNames : List Nat) : List Nat :=
  let maximum := max (arguments.foldl max 0) (argumentNames.foldl max 0)
  (List.range argumentNames.length).map (fun offset => offset + maximum + 1)

def crepAllDistinct : List Nat → Bool
  | [] => true
  | name :: names => !names.contains name && crepAllDistinct names

def crepInlineCallBody [OfNat α 0] [OfNat α 1]
    (returnInfo : Option (List Nat × Option (α × CrepProg α)))
    (name : FunName) (arguments : List (CrepExp α))
    (argumentNames : List Nat) (body : CrepProg α) : CrepProg α :=
  let temporaryNames := crepInlineTmpNames
    (arguments.flatMap crepExpVars) argumentNames
  match returnInfo with
  | none =>
      crepInlineTail
        (crepArgLoad temporaryNames arguments argumentNames body)
  | some (returnNames, none) =>
      if !crepAllDistinct returnNames then
        .call returnInfo name arguments
      else
        let returnMaximum := returnNames.foldl max 0
        let bodyMaximum := crepVmaxProg body
        let temporaryMaximum := temporaryNames.foldl max 0
        let returnStart := max returnMaximum
          (max bodyMaximum temporaryMaximum) + 1
        let temporaryReturns :=
          (List.range returnNames.length).map
            (fun offset => offset + returnStart)
        let transformed :=
          if crepNotBranchRet body then
            .seq .tick (crepTransformEoc temporaryReturns body)
          else
            .while (.const 1)
              (crepTransformBranch 0 temporaryReturns body)
        crepInlineNontail transformed returnNames temporaryReturns
          temporaryNames arguments argumentNames
  | some (_, some _) => .call returnInfo name arguments

def crepInlineCall [BEq FunName] [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α))
    (returnInfo : Option (List Nat × Option (α × CrepProg α)))
    (name : FunName) (arguments : List (CrepExp α)) : CrepProg α :=
  match crepInlineLookup name inlineable with
  | none => .call returnInfo name arguments
  | some (argumentNames, body) =>
      crepInlineCallBody returnInfo name arguments argumentNames body

def crepInlineProg [BEq FunName] [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α)) : CrepProg α → CrepProg α
  | .dec name value body =>
      .dec name value (crepInlineProg inlineable body)
  | .seq first second =>
      .seq (crepInlineProg inlineable first) (crepInlineProg inlineable second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (crepInlineProg inlineable thenBranch)
        (crepInlineProg inlineable elseBranch)
  | .while condition body =>
      .while condition (crepInlineProg inlineable body)
  | .call none name arguments =>
      crepInlineCall inlineable none name arguments
  | .call (some (returnNames, none)) name arguments =>
      crepInlineCall inlineable (some (returnNames, none)) name arguments
  | .call (some (returnNames, some (handler, body))) name arguments =>
      .call (some (returnNames, some (handler,
        crepInlineProg inlineable body))) name arguments
  | program => program
termination_by program => sizeOf program
decreasing_by
  all_goals simp_wf; decreasing_trivial

/-! ## Exact finite-map representation of Cake's inlineable finite map

HOL `inline_prog_def` (`cakeml/pancake/crep_inlineScript.sml:203-257`) recurses
on `(inlineable_fs, prog)` using the lexicographic termination measure
`(CARD (FDOM inlineable_fs), prog_size prog)`, because a Cake finite map is a
finite sptree with unique keys.  Lean's `Flapjack.FiniteMap` is the function
`α → Option β`, whose domain need not be finite, so its `FDOM` has no
cardinality and HOL's termination argument does not transfer.

`CrepInlineFmap` below is a finite map with a **unique-key invariant**:
its `entries` list carries a proof that the key projection is
duplicate-free, so every key is bound at most once and `card` (the entry count)
is exactly the number of distinct keys in the domain, matching HOL
`CARD (FDOM fs)`.  `lookup` is HOL `FLOOKUP`, `remove` is HOL `DOMSUB` and
`submap` is HOL `SUBMAP`.  The only public construction paths are `empty` and
the smart `insert`, which replaces any existing binding rather than shadowing
it, so the invariant is preserved by construction. Its list order is not
canonical, but lookup and cardinality represent a finite map rather than a
shadowing association list. -/

structure CrepInlineFmap (α : Type u) where
  entries : List (FunName × (List Nat × CrepProg α))
  nodupKeys : (entries.map Prod.fst).Nodup

namespace CrepInlineFmap

/-- The empty finite map (HOL `FEMPTY`). -/
def empty : CrepInlineFmap α :=
  { entries := [], nodupKeys := by simp }

/-- HOL `FLOOKUP`. -/
def lookup [BEq FunName] (name : FunName) (fs : CrepInlineFmap α) :
    Option (List Nat × CrepProg α) :=
  List.lookup name fs.entries

/-- Number of bindings; with the unique-key invariant this is HOL
    `CARD (FDOM fs)`. -/
def card (fs : CrepInlineFmap α) : Nat := fs.entries.length

theorem not_mem_map_fst_filter_bne [BEq FunName] [LawfulBEq FunName]
    (name : FunName) (l : List (FunName × (List Nat × CrepProg α))) :
    name ∉ List.map Prod.fst (l.filter (fun e => e.1 != name)) := by
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨e, he, hfe⟩ := hmem
  rw [List.mem_filter] at he
  rw [← hfe] at he
  simpa using he.2

/-- Remove every binding of `name` (HOL DOMSUB `fs \\ name`). -/
def remove [BEq FunName] [LawfulBEq FunName] (name : FunName)
    (fs : CrepInlineFmap α) : CrepInlineFmap α :=
  { entries := fs.entries.filter (fun e => e.1 != name)
    nodupKeys :=
      fs.nodupKeys.sublist ((List.filter_sublist (l := fs.entries)).map Prod.fst) }

/-- Insert `name ↦ value`, replacing any existing binding
    (HOL `fs |+ (name, value)`). -/
def insert [BEq FunName] [LawfulBEq FunName] (name : FunName)
    (value : List Nat × CrepProg α) (fs : CrepInlineFmap α) : CrepInlineFmap α :=
  { entries := (name, value) :: fs.entries.filter (fun e => e.1 != name)
    nodupKeys := by
      rw [List.map_cons]
      refine List.nodup_cons.mpr ⟨not_mem_map_fst_filter_bne name fs.entries, ?_⟩
      exact fs.nodupKeys.sublist
        ((List.filter_sublist (l := fs.entries)).map Prod.fst) }

/-- HOL finite-map `SUBMAP`: every binding of `a` is a binding of `b`. -/
def submap [BEq FunName] (a b : CrepInlineFmap α) : Prop :=
  ∀ name value, a.lookup name = some value → b.lookup name = some value

theorem eraseDups_eq_self_of_nodup [BEq FunName] [LawfulBEq FunName]
    {l : List FunName} (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.eraseDups_cons]
      have ha : a ∉ t := (List.nodup_cons.mp h).1
      have ht : t.Nodup := (List.nodup_cons.mp h).2
      have hfilter : (t.filter fun b => !b == a) = t := by
        apply List.filter_eq_self.mpr
        intro b hb
        have hne : b ≠ a := fun hba => ha (hba ▸ hb)
        simpa using hne
      rw [hfilter, ih ht]

/-- `card` is exactly the number of distinct keys, i.e. HOL `CARD (FDOM fs)`. -/
theorem card_eq_domain_cardinality [BEq FunName] [LawfulBEq FunName]
    (fs : CrepInlineFmap α) :
    fs.card = (fs.entries.map Prod.fst).eraseDups.length := by
  rw [eraseDups_eq_self_of_nodup fs.nodupKeys]
  simp [card, List.length_map]

theorem lookup_insert_self [BEq FunName] [LawfulBEq FunName] (name : FunName)
    (value : List Nat × CrepProg α) (fs : CrepInlineFmap α) :
    (insert name value fs).lookup name = some value := by
  rw [insert, lookup]
  exact List.lookup_eq_some_iff.mpr ⟨[], _, rfl, by simp⟩

theorem submap_refl [BEq FunName] (fs : CrepInlineFmap α) : submap fs fs := fun _ _ h => h

/-- Removing a bound key strictly decreases the domain cardinality. -/
theorem length_filter_lt_of_lookup [BEq FunName] [LawfulBEq FunName]
    (name : FunName) {v : List Nat × CrepProg α}
    {l : List (FunName × (List Nat × CrepProg α))}
    (h : List.lookup name l = some v) :
    (l.filter (fun e => e.1 != name)).length < l.length := by
  obtain ⟨l₁, l₂, heq, hkeys⟩ := List.lookup_eq_some_iff.mp h
  subst heq
  have hl₁ : (l₁.filter (fun e => e.1 != name)) = l₁ := by
    apply List.filter_eq_self.mpr
    intro e he
    have hne : e.1 ≠ name := by
      have hk := hkeys e he
      rw [bne_iff_ne] at hk
      exact fun hx => hk hx.symm
    rw [bne_iff_ne]; exact hne
  have hhead : ((name, v) :: l₂).filter (fun e => e.1 != name)
      = l₂.filter (fun e => e.1 != name) := by
    simp [bne_self_eq_false]
  rw [List.filter_append, hl₁, hhead]
  simp only [List.length_append, List.length_cons]
  exact Nat.add_lt_add_left (Nat.lt_succ_of_le (List.length_filter_le _ l₂)) l₁.length

theorem card_remove_lt [BEq FunName] [LawfulBEq FunName] (name : FunName)
    (fs : CrepInlineFmap α) {value : List Nat × CrepProg α}
    (h : fs.lookup name = some value) : (fs.remove name).card < fs.card := by
  show (fs.entries.filter (fun e => e.1 != name)).length < fs.entries.length
  exact length_filter_lt_of_lookup name h

theorem lookup_remove_none [BEq FunName] [LawfulBEq FunName] (name : FunName)
    (fs : CrepInlineFmap α) : (fs.remove name).lookup name = none := by
  rw [remove, lookup]
  cases h : List.lookup name (fs.entries.filter (fun e => e.1 != name)) with
  | none => rfl
  | some b =>
      obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp h
      have hmem : (name, b) ∈ fs.entries.filter (fun e => e.1 != name) := by
        rw [heq]; simp
      rw [List.mem_filter] at hmem
      simpa using hmem.2

/-! ### Carrier bridge to the HOL finite-map view

The HOL source uses `FLOOKUP`/`\\`/`SUBMAP`/`CARD (FDOM _)` on an
`mlstring |-> _ fmap`.  `toFiniteMap` reads the same partial function out of a
`CrepInlineFmap`, so the HOL `FLOOKUP` view is represented exactly, and `card`
is the finite domain cardinality (see `card_eq_domain_cardinality`).  This is a
*view* bridge, not a type isomorphism: the carrier is the unique-key entry list
rather than an sptree, which is why `crepInlineProgFmap` carries no `@[hol]`
tag (see the tag review in the definition's docstring). -/

/-- The partial function of a `CrepInlineFmap`, i.e. its HOL `fmap` read view. -/
def toFiniteMap [BEq FunName] (fs : CrepInlineFmap α) :
    FiniteMap FunName (List Nat × CrepProg α) :=
  fun name => fs.lookup name

theorem FLOOKUP_toFiniteMap [BEq FunName] (fs : CrepInlineFmap α) (name : FunName) :
    FLOOKUP (toFiniteMap fs) name = fs.lookup name := rfl

theorem submap_iff_flookup [BEq FunName] (a b : CrepInlineFmap α) :
    submap a b ↔
      ∀ name value,
        FLOOKUP (toFiniteMap a) name = some value →
        FLOOKUP (toFiniteMap b) name = some value := by
  constructor
  · intro h name value hf
    exact h name value hf
  · intro h name value hl
    exact h name value hl

/-- Removing a key from the entry list is the HOL `DOMSUB` view: the lookup of
    the removed key is `none` and every other lookup is unchanged. -/
theorem lookup_filter_bne {α : Type u} {β : Type v} [BEq α] [LawfulBEq α]
    (key name : α) (l : List (α × β)) (hnd : (l.map Prod.fst).Nodup) :
    List.lookup key (l.filter (fun e => e.1 != name)) =
      if key == name then none else List.lookup key l := by
  induction l with
  | nil => simp
  | cons e t ih =>
      obtain ⟨k, v⟩ := e
      rw [List.map_cons] at hnd
      obtain ⟨hk, hnd_t⟩ := List.nodup_cons.mp hnd
      rw [List.filter_cons]
      by_cases hkn : (k != name) = true
      · rw [if_pos hkn, List.lookup_cons, List.lookup_cons, ih hnd_t]
        have hkne : k ≠ name := by simpa [bne_iff_ne] using hkn
        cases hkey : key == k with
        | true =>
            have hk_eq : key = k := by simpa using hkey
            have hnm : (key == name) = false := by
              rw [beq_eq_false_iff_ne]; exact fun h => hkne (hk_eq ▸ h)
            simp [hnm]
        | false => simp
      · rw [if_neg hkn, List.lookup_cons, ih hnd_t]
        have hke : k = name := Classical.byContradiction (by
          intro h
          exact hkn (by rw [bne_iff_ne]; exact h))
        by_cases hkey : key == name
        · rw [if_pos hkey, if_pos hkey]
        · rw [if_neg hkey, if_neg hkey]
          have hkeq : (key == k) = false := by
            rw [beq_eq_false_iff_ne]
            intro h
            exact hkey (by rw [← hke, h]; exact beq_self_eq_true k)
          rw [hkeq]

/-- The carrier bridge commutes with `remove` (HOL `\\`): the view of a removed
    map is the view with that key deleted. -/
theorem toFiniteMap_remove [BEq FunName] [LawfulBEq FunName]
    (fs : CrepInlineFmap α) (name : FunName) :
    toFiniteMap (remove name fs) =
      fun key => if key == name then none else toFiniteMap fs key := by
  funext key
  simp only [toFiniteMap, lookup, remove]
  exact lookup_filter_bne key name fs.entries fs.nodupKeys

/-- The carrier bridge commutes with `insert`: a freshly inserted key is
    visible and every other lookup is unchanged. -/
theorem lookup_insert [BEq FunName] [LawfulBEq FunName]
    (key name : FunName) (value : List Nat × CrepProg α) (fs : CrepInlineFmap α) :
    (insert name value fs).lookup key =
      if key == name then some value else fs.lookup key := by
  unfold CrepInlineFmap.insert CrepInlineFmap.lookup
  rw [List.lookup_cons]
  cases hkey : key == name with
  | true => simp
  | false =>
      have hneg : ¬ (key == name) = true := by rw [hkey]; simp
      rw [lookup_filter_bne key name fs.entries fs.nodupKeys, if_neg hneg]
      rfl

end CrepInlineFmap

/-! ## Exact HOL inline-map input carrier

`compile_inl_top_def` starts from a list of function triples, filters by the
inline-name list, then applies HOL `alist_to_fmap`. Its map keys are `mlstring`
and its values contain `crepLang$prog` at one fixed word width. The generic
`CrepInlineFmap` above is useful for the untagged executable traversal, but it
does not model those carriers. This exact input map keeps HOL's first-binding
behavior for duplicate association-list keys and retains the selected source
list separately so the later `compile_inl_prog` boundary can preserve order.
-/

abbrev CrepInlineMapHOLName := Flapjack.Basis.Pure.MlString.MlString

structure CrepInlineFmapHOL (width : Nat) [NeZero width] where
  entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width))
  nodupKeys : (entries.map Prod.fst).Nodup

namespace CrepInlineFmapHOL

variable {width : Nat} [NeZero width]

def empty : CrepInlineFmapHOL width :=
  { entries := [], nodupKeys := by simp }

def lookup [BEq CrepInlineMapHOLName] (name : CrepInlineMapHOLName)
    (fs : CrepInlineFmapHOL width) :
    Option (List Nat × CrepProgHOL width) := List.lookup name fs.entries

def remove [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (name : CrepInlineMapHOLName) (fs : CrepInlineFmapHOL width) :
    CrepInlineFmapHOL width :=
  { entries := fs.entries.filter (fun e => e.1 != name)
    nodupKeys := fs.nodupKeys.sublist
      ((List.filter_sublist (l := fs.entries)).map Prod.fst) }

private theorem not_mem_fst_filter_bne [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName] (name : CrepInlineMapHOLName)
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width))) :
    name ∉ (entries.filter (fun e => e.1 != name)).map Prod.fst := by
  intro h
  rw [List.mem_map] at h
  obtain ⟨entry, he, hfst⟩ := h
  rw [List.mem_filter] at he
  rw [← hfst] at he
  simpa using he.2

def insert [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (name : CrepInlineMapHOLName) (value : List Nat × CrepProgHOL width)
    (fs : CrepInlineFmapHOL width) : CrepInlineFmapHOL width :=
  { entries := (name, value) :: fs.entries.filter (fun e => e.1 != name)
    nodupKeys := by
      rw [List.map_cons]
      exact List.nodup_cons.mpr
        ⟨not_mem_fst_filter_bne name fs.entries,
          fs.nodupKeys.sublist
            ((List.filter_sublist (l := fs.entries)).map Prod.fst)⟩ }

/-- HOL `alist_to_fmap`: right-fold updates make the first association-list
    binding win in the resulting finite map. -/
def ofAList [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName] :
    List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width)) →
      CrepInlineFmapHOL width
  | [] => empty
  | (name, value) :: rest => insert name value (ofAList rest)

theorem lookup_insert [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName] (key name : CrepInlineMapHOLName)
    (value : List Nat × CrepProgHOL width) (fs : CrepInlineFmapHOL width) :
    (insert name value fs).lookup key =
      if key == name then some value else fs.lookup key := by
  unfold insert lookup
  rw [List.lookup_cons]
  cases h : key == name with
  | true => simp
  | false =>
    have hn : ¬ (key == name) = true := by rw [h]; simp
    rw [CrepInlineFmap.lookup_filter_bne]
    · simp [h]
    · exact fs.nodupKeys

theorem lookup_remove [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName] (key name : CrepInlineMapHOLName)
    (fs : CrepInlineFmapHOL width) :
    (remove name fs).lookup key =
      if key == name then none else fs.lookup key := by
  unfold remove lookup
  exact CrepInlineFmap.lookup_filter_bne key name fs.entries fs.nodupKeys

theorem lookup_ofAList [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName] (key : CrepInlineMapHOLName)
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width))) :
    (ofAList entries).lookup key = List.lookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name, value⟩ := entry
    rw [ofAList, lookup_insert, ih]
    cases h : key == name <;> simp [h, List.lookup_cons]

end CrepInlineFmapHOL

/-- Source-order filtering and the exact HOL `alist_to_fmap` carrier bridge
    used as the input to `compile_inl_prog`. -/
def crepInlineSelectedHOLRows {width : Nat} [NeZero width]
    [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (inlineNames : List CrepInlineMapHOLName)
    (functions : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width))) :=
  functions.filter (fun row => inlineNames.contains row.1)

def crepInlineMapHOL {width : Nat} [NeZero width]
    [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (inlineNames : List CrepInlineMapHOLName)
    (functions : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width))) :
    CrepInlineFmapHOL width :=
  CrepInlineFmapHOL.ofAList (crepInlineSelectedHOLRows inlineNames functions)

theorem crepInlineMapHOL_lookup {width : Nat} [NeZero width]
    [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (inlineNames : List CrepInlineMapHOLName)
    (functions : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width)))
    (name : CrepInlineMapHOLName) :
    (crepInlineMapHOL inlineNames functions).lookup name =
      List.lookup name (crepInlineSelectedHOLRows inlineNames functions) :=
  CrepInlineFmapHOL.lookup_ofAList name _

/-- Exact shape of Cake `crep_inline$inline_prog`
    (`cakeml/pancake/crep_inlineScript.sml:203-257`) over the genuine
    finite-map representation above.  The recursion follows the source script
    equation by equation: `Dec`/`Seq`/`If`/`While` recurse structurally; the
    `Call` equation inlines the recursively-inlined handler, removes the
    callee name from the finite map before recursing into the looked-up callee
    body, and dispatches on the (possibly handler-inlined) call type.
    Termination uses HOL's measure `CARD (FDOM fs) LEX prog_size`, supplied
    here by `CrepInlineFmap.card` and `CrepInlineFmap.card_remove_lt`.

    **Tag review.** No `@[hol]` tag is attached. The carrier bridge
    `CrepInlineFmap.toFiniteMap` connects lookup and submap, `card` counts
    distinct keys, and `toFiniteMap_remove`/`lookup_insert` show the bridge
    commutes with `DOMSUB`/update. The universal theorem
    `crepInlineProgFmap_congr` proves this Lean pass depends on the inlineable
    map only through its finite-map lookup view, for every input program.
    This does not prove equality with HOL's sptree-recursive `inline_prog`;
    that cross-system correspondence is still open, so this definition has
    no `@[hol]` tag. The direct HOL oracle in
    `scripts/hol-probes/crep_inline_code_inl_probe.out` pins representative
    cases only. -/
def crepInlineProgFmap [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1]
    (inlineable : CrepInlineFmap α) : CrepProg α → CrepProg α
  | .dec name value body =>
      .dec name value (crepInlineProgFmap inlineable body)
  | .seq first second =>
      .seq (crepInlineProgFmap inlineable first)
        (crepInlineProgFmap inlineable second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (crepInlineProgFmap inlineable thenBranch)
        (crepInlineProgFmap inlineable elseBranch)
  | .while condition body =>
      .while condition (crepInlineProgFmap inlineable body)
  | .call none name arguments =>
      match _hlookup : inlineable.lookup name with
      | none => .call none name arguments
      | some (argumentNames, calleeBody) =>
          let inlinedCallee :=
            (crepUnreachElim
              (crepInlineProgFmap (inlineable.remove name) calleeBody)).1
          let temporaryNames :=
            crepInlineTmpNames (arguments.flatMap crepExpVars) argumentNames
          crepInlineTail
            (crepArgLoad temporaryNames arguments argumentNames inlinedCallee)
  | .call (some (returns, none)) name arguments =>
      if !crepAllDistinct returns then
        .call (some (returns, none)) name arguments
      else
        match _hlookup : inlineable.lookup name with
        | none => .call (some (returns, none)) name arguments
        | some (argumentNames, calleeBody) =>
            let inlinedCallee :=
              (crepUnreachElim
                (crepInlineProgFmap (inlineable.remove name) calleeBody)).1
            let temporaryNames :=
              crepInlineTmpNames (arguments.flatMap crepExpVars) argumentNames
            let returnMaximum := returns.foldl max 0
            let bodyMaximum := crepVmaxProg inlinedCallee
            let temporaryMaximum := temporaryNames.foldl max 0
            let returnStart :=
              max returnMaximum (max bodyMaximum temporaryMaximum) + 1
            let temporaryReturns :=
              (List.range returns.length).map
                (fun offset => offset + returnStart)
            let transformed :=
              if crepNotBranchRet inlinedCallee then
                .seq .tick (crepTransformEoc temporaryReturns inlinedCallee)
              else
                .while (.const 1)
                  (crepTransformBranch 0 temporaryReturns inlinedCallee)
            crepInlineNontail transformed returns temporaryReturns
              temporaryNames arguments argumentNames
  | .call (some (returns, some (w, handler))) name arguments =>
      .call (some (returns, some (w, crepInlineProgFmap inlineable handler)))
        name arguments
  | program => program
termination_by program => (inlineable.card, sizeOf program)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right
      decreasing_trivial
    | apply Prod.Lex.left
      exact CrepInlineFmap.card_remove_lt name inlineable _hlookup

/-- Representation independence within the Lean finite-map inline port: the
    pass depends on the inlineable map only through `toFiniteMap`. Thus any
    two Lean carriers with the same lookup view produce the same result for
    every program. Equality with HOL `inline_prog` is not established here. -/
theorem crepInlineProgFmap_congr [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1]
    {fs gs : CrepInlineFmap α}
    (h : CrepInlineFmap.toFiniteMap fs = CrepInlineFmap.toFiniteMap gs) :
    ∀ prog, crepInlineProgFmap fs prog = crepInlineProgFmap gs prog := by
  have key : ∀ (m : CrepInlineFmap α) (p : CrepProg α),
      ∀ n : CrepInlineFmap α,
        CrepInlineFmap.toFiniteMap n = CrepInlineFmap.toFiniteMap m →
        crepInlineProgFmap m p = crepInlineProgFmap n p := by
    apply crepInlineProgFmap.induct
      (motive := fun m p => ∀ n,
        CrepInlineFmap.toFiniteMap n = CrepInlineFmap.toFiniteMap m →
        crepInlineProgFmap m p = crepInlineProgFmap n p)
    · intro m name value body ih n hn
      rw [crepInlineProgFmap.eq_1, crepInlineProgFmap.eq_1, ih n hn]
    · intro m first second ih1 ih2 n hn
      rw [crepInlineProgFmap.eq_2, crepInlineProgFmap.eq_2, ih1 n hn, ih2 n hn]
    · intro m condition thenBranch elseBranch ih1 ih2 n hn
      rw [crepInlineProgFmap.eq_3, crepInlineProgFmap.eq_3, ih1 n hn, ih2 n hn]
    · intro m condition body ih n hn
      rw [crepInlineProgFmap.eq_4, crepInlineProgFmap.eq_4, ih n hn]
    · intro m name arguments hlookup n hn
      rw [crepInlineProgFmap.eq_5, crepInlineProgFmap.eq_5]
      have hnlookup : CrepInlineFmap.lookup name n = none :=
        (congrFun hn name).trans hlookup
      rw [hlookup, hnlookup]
    · intro m name arguments argumentNames calleeBody hlookup ih n hn
      rw [crepInlineProgFmap.eq_5, crepInlineProgFmap.eq_5]
      have hnlookup : CrepInlineFmap.lookup name n = some (argumentNames, calleeBody) :=
        (congrFun hn name).trans hlookup
      rw [hlookup, hnlookup]
      simp only []
      have hremove : CrepInlineFmap.toFiniteMap (CrepInlineFmap.remove name n) =
          CrepInlineFmap.toFiniteMap (CrepInlineFmap.remove name m) := by
        rw [CrepInlineFmap.toFiniteMap_remove, CrepInlineFmap.toFiniteMap_remove]
        funext k
        by_cases hk : k == name
        · rw [if_pos hk, if_pos hk]
        · rw [if_neg hk, if_neg hk]
          exact congrFun hn k
      rw [ih (CrepInlineFmap.remove name n) hremove]
    · intro m returnNames name arguments hdistinct n hn
      rw [crepInlineProgFmap.eq_6, crepInlineProgFmap.eq_6]
      rw [if_pos hdistinct, if_pos hdistinct]
    · intro m returnNames name arguments hnd hlookup n hn
      rw [crepInlineProgFmap.eq_6, crepInlineProgFmap.eq_6]
      have hnlookup : CrepInlineFmap.lookup name n = none :=
        (congrFun hn name).trans hlookup
      rw [if_neg hnd, if_neg hnd, hlookup, hnlookup]
    · intro m returnNames name arguments hnd argumentNames calleeBody hlookup ih n hn
      rw [crepInlineProgFmap.eq_6, crepInlineProgFmap.eq_6]
      have hnlookup : CrepInlineFmap.lookup name n = some (argumentNames, calleeBody) :=
        (congrFun hn name).trans hlookup
      rw [if_neg hnd, if_neg hnd, hlookup, hnlookup]
      simp only []
      have hremove : CrepInlineFmap.toFiniteMap (CrepInlineFmap.remove name n) =
          CrepInlineFmap.toFiniteMap (CrepInlineFmap.remove name m) := by
        rw [CrepInlineFmap.toFiniteMap_remove, CrepInlineFmap.toFiniteMap_remove]
        funext k
        by_cases hk : k == name
        · rw [if_pos hk, if_pos hk]
        · rw [if_neg hk, if_neg hk]
          exact congrFun hn k
      rw [ih (CrepInlineFmap.remove name n) hremove]
    · intro m returnNames handler body name arguments ih n hn
      rw [crepInlineProgFmap.eq_7, crepInlineProgFmap.eq_7, ih n hn]
    · intro m program h1 h2 h3 h4 h5 h6 h7 n hn
      rw [crepInlineProgFmap.eq_8 m program h1 h2 h3 h4 h5 h6 h7,
        crepInlineProgFmap.eq_8 n program h1 h2 h3 h4 h5 h6 h7]
  intro prog
  exact key fs prog gs h.symm

/-- The `Skip` clause of HOL `inline_prog` (`crep_inlineScript.sml:203`): the
    inline pass leaves `Skip` unchanged. -/
theorem crepInlineProgFmap_skip [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1] (inlFs : CrepInlineFmap α) :
    crepInlineProgFmap inlFs .skip = .skip := by
  simp only [crepInlineProgFmap]

/-! ## Clause form of `crepInlineProgFmap`

These seven theorems unfold `crepInlineProgFmap` on each program constructor,
stating its defining equations in the clause order of HOL `inline_prog_def`
(`cakeml/pancake/crep_inlineScript.sml:203`).  Each is a kernel-checked fact
about `crepInlineProgFmap` itself (derived from its own equation lemmas); they
are NOT a cross-system correspondence to HOL `inline_prog`.  In particular no
theorem here relates the Lean helpers (`crepUnreachElim`, `crepArgLoad`,
`crepInlineNontail`, `crepInlineTmpNames`, `crepTransformEoc`,
`crepTransformBranch`, ...) to the corresponding HOL helpers (`unreach_elim`,
`arg_load`, `inline_nontail`, `GENLIST`, `transform_eoc`, `transform_branch`,
...), and no theorem here proves that the recursive call equals HOL's.

The `Call` constructor is split, not one equation: `crepInlineProgFmap` has
separate equations for `.call none`, for `.call (some (rts, none))` (with the
`crepAllDistinct` distinct/non-distinct split), and for
`.call (some (rts, some (w, handler)))`.  The three theorems below state one
such Lean equation each; the `crepInlineProgFmap_call_hol` right side is the
`.call none` equation with its Lean `FLOOKUP` (`fs.lookup`) branch, not a
definitional identity with HOL's `case ctyp` dispatch.

What *is* pinned is the carrier view: `CrepInlineFmap.lookup` is HOL `FLOOKUP`
(`toFiniteMap`), `remove` is HOL `DOMSUB` (`toFiniteMap_remove`), `card` equals
the domain cardinality (`card_eq_domain_cardinality`), so the termination
measure `(fs.card, sizeOf prog)` mirrors HOL `(CARD (FDOM fs), prog_size prog)`.

No `@[hol]` tag is attached: the Lean carrier is the canonical entry-list model
rather than the fmap quotient (same `FLOOKUP` view, not the same type), the
binders carry `[BEq FunName]` / `[LawfulBEq FunName]` where HOL uses
propositional equality, and the recursive helper cross-system correspondence
remains open. -/

theorem crepInlineProgFmap_call_hol {α : Type} [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1] (fs : CrepInlineFmap α) (name : FunName)
    (args : List (CrepExp α)) :
    crepInlineProgFmap fs (.call none name args) =
      (match fs.lookup name with
       | none => .call none name args
       | some (argsVname, body) =>
           let inlined := (crepUnreachElim (crepInlineProgFmap (fs.remove name) body)).1
           let tmp := crepInlineTmpNames (args.flatMap crepExpVars) argsVname
           crepInlineTail (crepArgLoad tmp args argsVname inlined)) := by
  simp only [crepInlineProgFmap]
  cases h : fs.lookup name <;> rfl

theorem crepInlineProgFmap_call_some_none_hol {α : Type} [BEq FunName]
    [LawfulBEq FunName] [OfNat α 0] [OfNat α 1] (fs : CrepInlineFmap α)
    (rts : List Nat) (name : FunName) (args : List (CrepExp α)) :
    crepInlineProgFmap fs (.call (some (rts, none)) name args) =
      (if !crepAllDistinct rts then .call (some (rts, none)) name args
       else match fs.lookup name with
       | none => .call (some (rts, none)) name args
       | some (argsVname, body) =>
           let inlined := (crepUnreachElim (crepInlineProgFmap (fs.remove name) body)).1
           let tmp := crepInlineTmpNames (args.flatMap crepExpVars) argsVname
           let returnMaximum := rts.foldl max 0
           let bodyMaximum := crepVmaxProg inlined
           let temporaryMaximum := tmp.foldl max 0
           let returnStart := max returnMaximum (max bodyMaximum temporaryMaximum) + 1
           let temporaryReturns := (List.range rts.length).map (fun offset => offset + returnStart)
           let transformed :=
             if crepNotBranchRet inlined then .seq .tick (crepTransformEoc temporaryReturns inlined)
             else .while (.const 1) (crepTransformBranch 0 temporaryReturns inlined)
           crepInlineNontail transformed rts temporaryReturns tmp args argsVname) := by
  simp only [crepInlineProgFmap]
  cases crepAllDistinct rts with
  | true =>
      simp only [Bool.not_true]
      cases h : fs.lookup name <;> rfl
  | false => simp only [Bool.not_false, if_true]

theorem crepInlineProgFmap_call_some_handler_hol {α : Type} [BEq FunName]
    [LawfulBEq FunName] [OfNat α 0] [OfNat α 1] (fs : CrepInlineFmap α)
    (rts : List Nat) (w : α) (handler : CrepProg α) (name : FunName)
    (args : List (CrepExp α)) :
    crepInlineProgFmap fs (.call (some (rts, some (w, handler))) name args) =
      .call (some (rts, some (w, crepInlineProgFmap fs handler))) name args := by
  simp only [crepInlineProgFmap]

theorem crepInlineProgFmap_dec_hol {α : Type} [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1] (fs : CrepInlineFmap α) (v : Nat)
    (e : CrepExp α) (p : CrepProg α) :
    crepInlineProgFmap fs (.dec v e p) = .dec v e (crepInlineProgFmap fs p) := by
  simp [crepInlineProgFmap]

theorem crepInlineProgFmap_seq_hol {α : Type} [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1] (fs : CrepInlineFmap α) (a b : CrepProg α) :
    crepInlineProgFmap fs (.seq a b) =
      .seq (crepInlineProgFmap fs a) (crepInlineProgFmap fs b) := by
  simp [crepInlineProgFmap]

theorem crepInlineProgFmap_ite_hol {α : Type} [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1] (fs : CrepInlineFmap α) (e : CrepExp α)
    (a b : CrepProg α) :
    crepInlineProgFmap fs (.ite e a b) =
      .ite e (crepInlineProgFmap fs a) (crepInlineProgFmap fs b) := by
  simp [crepInlineProgFmap]

theorem crepInlineProgFmap_while_hol {α : Type} [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1] (fs : CrepInlineFmap α) (e : CrepExp α)
    (p : CrepProg α) :
    crepInlineProgFmap fs (.while e p) = .while e (crepInlineProgFmap fs p) := by
  simp [crepInlineProgFmap]

def crepInlineActiveNames [BEq FunName]
    (inlineable : List (CrepInlineEntry α)) :
    Std.HashSet FunName :=
  inlineable.foldl (fun names entry => names.insert entry.1) ∅

def crepInlineProgRecursive [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α)) (active : Std.HashSet FunName) :
    CrepProg α → CrepProg α
  | .dec name value body =>
      .dec name value (crepInlineProgRecursive inlineable active body)
  | .seq first second =>
      .seq (crepInlineProgRecursive inlineable active first)
        (crepInlineProgRecursive inlineable active second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (crepInlineProgRecursive inlineable active thenBranch)
        (crepInlineProgRecursive inlineable active elseBranch)
  | .while condition body =>
      .while condition (crepInlineProgRecursive inlineable active body)
  | .call none name arguments =>
      if _hactive : name ∈ active then
        match crepInlineLookup name inlineable with
        | none => .call none name arguments
        | some (argumentNames, body) =>
            let (body', _) := crepUnreachElim
              (crepInlineProgRecursive inlineable (active.erase name) body)
            crepInlineCallBody none name arguments argumentNames
              body'
      else .call none name arguments
  | .call (some (returnNames, none)) name arguments =>
      if _hactive : name ∈ active then
        match crepInlineLookup name inlineable with
        | none => .call (some (returnNames, none)) name arguments
        | some (argumentNames, body) =>
            let (body', _) := crepUnreachElim
              (crepInlineProgRecursive inlineable (active.erase name) body)
            crepInlineCallBody (some (returnNames, none)) name arguments
              argumentNames
              body'
      else .call (some (returnNames, none)) name arguments
  | .call (some (returnNames, some (handler, body))) name arguments =>
      .call (some (returnNames, some (handler,
        crepInlineProgRecursive inlineable active body))) name arguments
  | program => program
termination_by program => (active.size, sizeOf program)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right
      decreasing_trivial
    | apply Prod.Lex.left
      rw [Std.HashSet.size_erase]
      simp [_hactive]
      have hsize : 0 < active.size := by
        have hne : active.size ≠ 0 := by
          intro hzero
          have hempty : active.isEmpty = true := by
            rw [Std.HashSet.isEmpty_eq_size_eq_zero]
            simp [hzero]
          exact (Std.HashSet.not_mem_of_isEmpty hempty) _hactive
        omega
      omega

def crepInlineFunctionsRecursive [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α))
    (active : Std.HashSet FunName) :
    List (CompiledFunction α) → List (CompiledFunction α)
  | [] => []
  | function :: functions =>
      let transformedBody := crepInlineProgRecursive inlineable
        (active.erase function.name) function.body
      { function with body := transformedBody } ::
        crepInlineFunctionsRecursive inlineable active functions

def crepInlineTopRecursive [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α))
    (functions : List (CompiledFunction α)) : List (CompiledFunction α) :=
  crepInlineFunctionsRecursive inlineable (crepInlineActiveNames inlineable)
    functions

def crepInlineTopRecursiveByNames [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1]
    (inlineNames : List FunName) (functions : List (CompiledFunction α)) :
    List (CompiledFunction α) :=
  let inlineable := (functions.filter (fun function =>
      inlineNames.contains function.name)).map (fun function =>
        (function.name, (function.params, function.body)))
  crepInlineTopRecursive inlineable functions

/-- Flapjack-specific source-shaped counterpart (NOT an exact HOL port) of
    `crep_inline$compile_inl_top`: filter the compiled Crep function triples by
    the source inline-name set, then inline each body with its own name removed
    from the finite active set. HOL's `alist_to_fmap` uses the first binding
    for duplicate function names; the retained ordered list and
    `crepInlineLookup`'s first-match lookup have that same lookup behavior. The
    direct duplicate-name oracle is in `Test/CompileProgParity.lean`.

    This declaration has two carrier gaps, so it has no `@[hol]` tag. Its
    names use `FunName = String`, whereas HOL `funname` is `mlstring`; the exact
    name carrier work is tracked by `flapjack-pxn.18.3.5.8`. Its body is
    generic `CrepProg α`, whereas HOL's `crepLang$prog` is indexed by the word
    type; the exact width-indexed syntax is `CrepProgHOL width` with payloads
    in `CrepExpHOL width` (`CrepLang/Prog.lean`). A `names_as_string` qualifier
    can record the name representation difference when it is the only gap, but
    it cannot bridge the generic program carrier. The exact `compile_inl_top`
    boundary over both carriers remains open. `flapjack-e7w.1` covers only the
    faithful inline-map carrier prerequisite; recursive exact `inline_prog`,
    the `compile_inl_top` wrapper, and production-path routing remain separate
    follow-up work. This declaration is a proof-side analogue; the executed
    `panToCrepCompileInlTop` currently calls the production record-based
    traversal instead. -/
def compileInlTopHOL [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1]
    (inlineNames : List FunName)
    (functions : List (FunName × List Nat × CrepProg α)) :
    List (FunName × List Nat × CrepProg α) :=
  let inlineable : List (CrepInlineEntry α) :=
    (functions.filter (fun function => inlineNames.contains function.1)).map
      fun (name, parameters, body) => (name, (parameters, body))
  let active := crepInlineActiveNames inlineable
  functions.map fun (name, parameters, body) =>
    (name, parameters,
      crepInlineProgRecursive inlineable (active.erase name) body)

/-- Flapjack-only downstream adapter: run HOL's triple-list inline pass, then
    reattach the source return-shape metadata needed by later executable
    passes. This adapter has no HOL original because HOL keeps triples. -/
def compileInlTopHOLWithMetadata [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1]
    (inlineNames : List FunName)
    (functions : List (CompiledFunction α)) : List (CompiledFunction α) :=
  let triples := functions.map fun function =>
    (function.name, function.params, function.body)
  let inlined := compileInlTopHOL inlineNames triples
  functions.zipWith (fun original (_, _, body) => { original with body }) inlined

/-! Production traversal corresponding to CakeML Pancake's
    `compile_inl_top_def` (`crep_inlineScript.sml:264`), via
    `compile_inl_prog`/`inline_prog`. This wrapper consumes the generic
    `CompiledFunction α` record and returns records carrying Flapjack's
    `returnShape` metadata; HOL operates on `(funname, params, prog)` triples
    and its `prog` is indexed by a word type. It also uses String function
    names rather than HOL `mlstring`. It is therefore not the tagged HOL
    boundary; see `compileInlTopHOL` and open bead `flapjack-e7w.1` for the
    exact-carrier port. -/
def panToCrepCompileInlTop [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat α 0] [OfNat α 1]
    (inlineNames : List FunName) (functions : List (CompiledFunction α)) :
    List (CompiledFunction α) :=
  crepInlineTopRecursiveByNames inlineNames functions

/-! Cake's `first_compile_prog_all_distinct`
    (`pan_to_crepProofScript.sml:4556-4564`): the recursive inline pass
    rewrites function bodies but preserves the function-name table.  This
    invariant is used by the top-level `pc_compile_correct` assembly and is
    kept separate from the body-transformation proof. -/
theorem crepInlineFunctionsRecursive_map_name
    [BEq FunName] [LawfulBEq FunName] [LawfulHashable FunName]
    [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α))
    (active : Std.HashSet FunName)
    (functions : List (CompiledFunction α)) :
    (crepInlineFunctionsRecursive inlineable active functions).map
        CompiledFunction.name = functions.map CompiledFunction.name := by
  induction functions with
  | nil => rfl
  | cons function functions ih =>
      simp only [crepInlineFunctionsRecursive, List.map_cons]
      exact congrArg (fun names => function.name :: names) ih

theorem panToCrepCompileInlTop_names_nodup
    [BEq FunName] [LawfulBEq FunName] [LawfulHashable FunName]
    [OfNat α 0] [OfNat α 1]
    (inlineNames : List FunName)
    (functions : List (CompiledFunction α))
    (hnodup : (functions.map CompiledFunction.name).Nodup) :
    (panToCrepCompileInlTop inlineNames functions).map
        CompiledFunction.name |>.Nodup := by
  rw [panToCrepCompileInlTop, crepInlineTopRecursiveByNames,
    crepInlineTopRecursive]
  rw [crepInlineFunctionsRecursive_map_name]
  exact hnodup

/-! Cake's `compile_prog_distinct_params`
    (`pan_to_crepProofScript.sml:4684-4688`): recursive inlining rewrites
    function bodies only, so the flattened parameter slots of every function
    remain distinct. -/
theorem crepInlineFunctionsRecursive_params_nodup
    [BEq FunName] [LawfulBEq FunName] [LawfulHashable FunName]
    [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α))
    (active : Std.HashSet FunName)
    (functions : List (CompiledFunction α))
    (hparams : ∀ function ∈ functions, function.params.Nodup) :
    ∀ function ∈ crepInlineFunctionsRecursive inlineable active functions,
      function.params.Nodup := by
  induction functions with
  | nil => simp [crepInlineFunctionsRecursive]
  | cons function functions ih =>
      intro target htarget
      simp only [crepInlineFunctionsRecursive, List.mem_cons] at htarget
      rcases htarget with hhead | htail
      · subst target
        simpa using hparams function (by simp)
      · apply ih
        · intro candidate hcandidate
          exact hparams candidate (by simp [hcandidate])
        · exact htail

theorem panToCrepCompileInlTop_params_nodup
    [BEq FunName] [LawfulBEq FunName] [LawfulHashable FunName]
    [OfNat α 0] [OfNat α 1]
    (inlineNames : List FunName)
    (functions : List (CompiledFunction α))
    (hparams : ∀ function ∈ functions, function.params.Nodup) :
    ∀ function ∈ panToCrepCompileInlTop inlineNames functions,
      function.params.Nodup := by
  unfold panToCrepCompileInlTop crepInlineTopRecursiveByNames
    crepInlineTopRecursive
  apply crepInlineFunctionsRecursive_params_nodup
  exact hparams

def crepInlineFunctions [BEq FunName] [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α)) :
    List (CompiledFunction α) → List (CompiledFunction α)
  | [] => []
  | function :: functions =>
      { function with body :=
          crepInlineProg (crepInlineRemove function.name inlineable) function.body } ::
        crepInlineFunctions inlineable functions

def crepInlineTop [BEq FunName] [OfNat α 0] [OfNat α 1]
    (inlineNames : List FunName) (functions : List (CompiledFunction α)) :
    List (CompiledFunction α) :=
  let inlineable := (functions.filter (fun function =>
      inlineNames.contains function.name)).map (fun function =>
        (function.name, (function.params, function.body)))
  crepInlineFunctions inlineable functions

end Flapjack
