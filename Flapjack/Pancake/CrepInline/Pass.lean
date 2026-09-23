import Flapjack.HolRef
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.CrepInline
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

end CrepInlineFmap

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
    `CrepInlineFmap.toFiniteMap` connects lookup and submap, and `card` counts
    distinct keys. HOL defines `inline_prog` over a finite sptree; this Lean
    function recurses over duplicate-free entries. A proof that the two
    recursive functions agree under the carrier bridge is still missing.
    The direct HOL oracle in
    `scripts/hol-probes/crep_inline_code_inl_probe.out` checks representative
    cases, but does not establish that universal correspondence. -/
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

/-- HOL `crep_inline$compile_inl_top`: filter the compiled Crep function
    triples by the source inline-name set, then inline each body with its own
    name removed from the finite active set. The source finite map's first
    duplicate binding is represented by `crepInlineLookup`'s first-match
    lookup on the filtered list. -/
@[hol "cakeml/pancake/crep_inlineScript.sml" "compile_inl_top_def"]
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

/-! Source-named port of CakeML Pancake's `compile_inl_top_def`
    (`crep_inlineScript.sml:264`).  The production recursive traversal is the
    executable form of Cake's `compile_inl_prog`/`inline_prog` composition;
    keeping this boundary named makes the pass correspondence explicit. -/
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
