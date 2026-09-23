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
finite sptree.  Lean's `Flapjack.FiniteMap` is the function `α → Option β`,
whose domain need not be finite, so its `FDOM` has no cardinality and HOL's
termination argument does not transfer.  The datatype below is a genuine
finite map with HOL-shaped `FLOOKUP`/`DOMSUB`/`SUBMAP` and a `card`, so that
removing a bound key strictly decreases the termination measure.  This is the
finite-map representation required for the exact `code_inl_rel_def` port and
is deliberately not the rejected list/first-match analogue. -/

inductive CrepInlineFmap (α : Type u) where
  | empty : CrepInlineFmap α
  | insert (key : FunName) (value : List Nat × CrepProg α)
      (rest : CrepInlineFmap α) : CrepInlineFmap α

namespace CrepInlineFmap

/-- HOL `FLOOKUP` on the finite map. -/
def lookup [BEq FunName] (name : FunName) :
    CrepInlineFmap α → Option (List Nat × CrepProg α)
  | .empty => none
  | .insert key value rest =>
      if key == name then some value else lookup name rest

/-- HOL DOMSUB `fs \\ name`. -/
def remove [BEq FunName] (name : FunName) :
    CrepInlineFmap α → CrepInlineFmap α
  | .empty => .empty
  | .insert key value rest =>
      if key == name then remove name rest
      else .insert key value (remove name rest)

/-- HOL finite-map `SUBMAP`: every binding of `a` is a binding of `b`. -/
def submap (a b : CrepInlineFmap α) : Prop :=
  ∀ name value, a.lookup name = some value → b.lookup name = some value

/-- Number of bindings; the first component of HOL's termination measure. -/
def card : CrepInlineFmap α → Nat
  | .empty => 0
  | .insert _ _ rest => card rest + 1

@[simp] theorem card_empty : (empty : CrepInlineFmap α).card = 0 := rfl

@[simp] theorem card_insert (key : FunName) (value : List Nat × CrepProg α)
    (rest : CrepInlineFmap α) :
    (insert key value rest).card = rest.card + 1 := rfl

theorem lookup_insert_self [BEq FunName] [LawfulBEq FunName]
    (name : FunName) (value : List Nat × CrepProg α) (rest : CrepInlineFmap α) :
    (insert name value rest).lookup name = some value := by
  simp [lookup]

theorem lookup_remove_none [BEq FunName] [LawfulBEq FunName]
    (name : FunName) (fs : CrepInlineFmap α) :
    (fs.remove name).lookup name = none := by
  induction fs with
  | empty => rfl
  | insert key value rest ih =>
      cases hk : key == name with
      | true => simpa [remove, hk] using ih
      | false => simp [lookup, remove, hk, ih]

theorem card_remove_le [BEq FunName] (name : FunName)
    (fs : CrepInlineFmap α) : (fs.remove name).card ≤ fs.card := by
  induction fs with
  | empty => simp [remove, card]
  | insert key value rest ih =>
      cases hk : key == name with
      | true => simp [remove, hk]; exact Nat.le_succ_of_le ih
      | false => simp [remove, hk]; exact ih

theorem card_remove_lt [BEq FunName] [LawfulBEq FunName] (name : FunName)
    (fs : CrepInlineFmap α) {value : List Nat × CrepProg α}
    (h : fs.lookup name = some value) : (fs.remove name).card < fs.card := by
  induction fs with
  | empty => simp [lookup] at h
  | insert key v rest ih =>
      cases hk : key == name with
      | true =>
          have hle : (rest.remove name).card ≤ rest.card := card_remove_le name rest
          simp only [remove, hk, card_insert]
          exact Nat.lt_succ_of_le hle
      | false =>
          have hrest : rest.lookup name = some value := by
            simpa [lookup, hk] using h
          have hlt := ih hrest
          simp only [remove, hk, card_insert]
          exact Nat.succ_lt_succ hlt

theorem submap_refl (fs : CrepInlineFmap α) : submap fs fs :=
  fun _ _ h => h

end CrepInlineFmap

/-- Exact shape of Cake `crep_inline$inline_prog`
    (`cakeml/pancake/crep_inlineScript.sml:203-257`) over the genuine
    finite-map representation above.  The recursion follows the source script
    equation by equation: `Dec`/`Seq`/`If`/`While` recurse structurally; the
    `Call` equation inlines the recursively-inlined handler, removes the
    callee name from the finite map before recursing into the looked-up callee
    body, and dispatches on the (possibly handler-inlined) call type.
    Termination uses HOL's measure `CARD (FDOM fs) LEX prog_size`, supplied
    here by `CrepInlineFmap.card` and `CrepInlineFmap.card_remove_lt`. -/
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
