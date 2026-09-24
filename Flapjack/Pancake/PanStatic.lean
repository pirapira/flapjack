import Flapjack.Pancake.PanLang

/-!
Static-checker data and shape-context operations.

This module is the executable front-end checker. It ports the reusable
pieces of CakeML's `panStatic` theory together with declaration-level
context construction and function-body validation.
-/

namespace Flapjack

inductive Based where
  | based
  | notBased
  | trusted
  | notTrusted
  deriving BEq, Repr

inductive ShapedBased where
  | word (basedness : Based)
  | struct (fields : List ShapedBased)
  | named (name : StructName) (fields : List (FieldName × ShapedBased))
  deriving BEq, Repr

structure StructInfo where
  fields : List (FieldName × Shape)
  size : Nat
  shapedFields : List (FieldName × ShapedBased) := []
  deriving Repr

abbrev StructContext := List (StructName × StructInfo)
abbrev InfoMap (α : Type u) := List (String × α)

/-- Projection of the production cache-augmented `StructContext` onto the
    HOL-shaped `StructContextHOL`, keeping the HOL `struct_info` fields `fields`
    and `size` and dropping the production-only `StructInfo.shapedFields`
    cache. This is the context adapter used to relate the exact HOL-shaped
    predicates (`panValueFldsOk`, `panIsWfShapeValueHOL`) to the production
    predicates over `StructContext`. Because both lookups are first-match, the
    projection preserves shadowing of duplicate struct names. -/
def StructContext.toHOL (context : StructContext) : StructContextHOL :=
  context.map (fun entry => (entry.1, { fields := entry.2.fields, size := entry.2.size }))

/-- Lookup commutes with the `StructContext.toHOL` projection: the projected
    context yields the same first-match entry, with its `struct_info` viewed
    through the projection. -/
theorem lookupInfo_toHOL [BEq String] (name : String) (context : StructContext) :
    lookupInfo name context.toHOL =
      (lookupInfo name context).map
        (fun info => { fields := info.fields, size := info.size }) := by
  induction context with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨structName, info⟩ := entry
      by_cases h : structName == name
      · simp [StructContext.toHOL, lookupInfo, h]
      · rw [show StructContext.toHOL ((structName, info) :: entries) =
            ((structName, { fields := info.fields, size := info.size }) : StructName × StructInfoHOL)
              :: StructContext.toHOL entries from rfl]
        simp only [lookupInfo]
        simp only [if_neg h]
        exact ih

/-- The `isSome` corollary of `lookupInfo_toHOL`: the HOL `ALOOKUP sctxt nm <>
    NONE` condition is projection-invariant. -/
@[simp] theorem lookupInfo_toHOL_isSome [BEq String] (name : String) (context : StructContext) :
    (lookupInfo name context.toHOL).isSome = (lookupInfo name context).isSome := by
  rw [lookupInfo_toHOL]
  cases lookupInfo name context <;> rfl

/-- Cake's `ALOOKUP_MAP3` (`pan_globalsProofScript.sml:2841`): mapping a
    function over the value component of every entry commutes with the
    lookup. -/
theorem lookupInfo_map3 [BEq κ] (f : γ → δ) (name : κ)
    (entries : List (κ × (β × γ))) :
    lookupInfo name (entries.map (fun entry => (entry.1, entry.2.1, f entry.2.2))) =
      (lookupInfo name entries).map (fun value => (value.1, f value.2)) := by
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      simp only [List.map_cons, lookupInfo]
      by_cases h : (entry.1 == name) = true
      · rw [if_pos h, if_pos h]
        rfl
      · rw [if_neg h, if_neg h]
        exact ih

/-- Cake's `ALOOKUP_MAP4` (`pan_globalsProofScript.sml:2851`): mapping a
    function over the middle component of every entry commutes with the
    lookup. -/
theorem lookupInfo_map4 [BEq κ] (f : γ → δ) (name : κ)
    (entries : List (κ × (β × γ × ε))) :
    lookupInfo name
        (entries.map (fun entry => (entry.1, entry.2.1, f entry.2.2.1, entry.2.2.2))) =
      (lookupInfo name entries).map (fun value => (value.1, f value.2.1, value.2.2)) := by
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      simp only [List.map_cons, lookupInfo]
      by_cases h : (entry.1 == name) = true
      · rw [if_pos h, if_pos h]
        rfl
      · rw [if_neg h, if_neg h]
        exact ih

/-! The original Pancake `mem_load` uses `dropWhile` to find a named
    structure and then evaluates its fields against the remaining context.
    Keeping the suffix is important: declarations only make earlier context
    entries available to their fields. -/
def lookupInfoWithRest [BEq String] (name : String) : StructContext →
    Option (StructInfo × StructContext)
  | [] => none
  | (candidate, info) :: context =>
      if candidate == name then some (info, context)
      else lookupInfoWithRest name context

/-- Production shape well-formedness. This is the executable counterpart of HOL
    `is_wf_shape` (`cakeml/pancake/panLangScript.sml:139`). The two leaf clauses
    are delegated to the exact HOL-shaped, `@[hol panLangScript.sml
    is_wf_shape_def]`-tagged `isWfShapeHOL` over `StructContextHOL` (in
    `PanLang.lean`), projecting the production `StructContext` through
    `StructContext.toHOL`; the `Comb` clause is the HOL `EVERY is_wf_shape`
    recursion, kept as the executable `isWfShapeList` fold so the function
    retains its well-founded induction principle. `isWfShapeHOL_toHOL` below
    records the clause-by-clause agreement. Direct HOL oracle rows are in
    `scripts/hol-probes/pan_lang_wf_shape_probe.out`. -/
@[simp] theorem isWfShapeHOL_one (context : StructContextHOL) :
    isWfShapeHOL context .one = true := by
  rw [isWfShapeHOL.eq_def]

/-- The `Named` clause of the exact port, exposed as a `simp` bridge so the
    production delegation reduces to the production `lookupInfo` result. -/
@[simp] theorem isWfShapeHOL_named (context : StructContextHOL) (name : StructName) :
    isWfShapeHOL context (.named name) = (lookupInfo name context).isSome := by
  rw [isWfShapeHOL.eq_def]

def isWfShape (context : StructContext) : Shape → Bool
  | .one => isWfShapeHOL context.toHOL .one
  | .comb shapes => isWfShapeList context shapes
  | .named name => isWfShapeHOL context.toHOL (.named name)

termination_by shape => sizeOf shape
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  isWfShapeList (context : StructContext) : List Shape → Bool
    | [] => true
    | shape :: shapes => isWfShape context shape && isWfShapeList context shapes
  termination_by shapes => sizeOf shapes
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

/-
Clause-by-clause relation between the exact HOL-shaped `is_wf_shape` port
    `isWfShapeHOL` over `StructContextHOL` and the production `isWfShape` over
    the cache-augmented `StructContext`, through the context projection
    `StructContext.toHOL`. Both predicates agree on every shape. -/
mutual
  theorem isWfShapeHOL_toHOL (context : StructContext) :
      ∀ (shape : Shape), isWfShapeHOL context.toHOL shape = isWfShape context shape
    | .one => by simp only [isWfShapeHOL.eq_def, isWfShape.eq_def]
    | .comb shapes => by
        simp only [isWfShapeHOL.eq_def, isWfShape.eq_def]
        exact isWfShapeListHOL_toHOL context shapes
    | .named name => by
        simp only [isWfShapeHOL.eq_def, isWfShape.eq_def]

  theorem isWfShapeListHOL_toHOL (context : StructContext) :
      ∀ (shapes : List Shape),
        isWfShapeListHOL context.toHOL shapes = isWfShape.isWfShapeList context shapes
    | [] => by simp only [isWfShapeListHOL.eq_def, isWfShape.isWfShapeList.eq_def]
    | shape :: shapes => by
        rw [isWfShapeListHOL.eq_def, isWfShape.isWfShapeList.eq_def]
        simp only []
        rw [isWfShapeHOL_toHOL context shape, isWfShapeListHOL_toHOL context shapes]
end

def isWfFields (context : StructContext) : List (FieldName × Shape) → Bool
  | [] => true
  | (_, shape) :: fields => isWfShape context shape && isWfFields context fields

def isWfContext : StructContext → Bool
  | [] => true
  | (name, info) :: context =>
      (lookupInfo name context).isNone &&
        isWfFields context info.fields && isWfContext context

def shapeSizeWithContext (context : StructContext) : Shape → Nat
  | .one => 1
  | .comb shapes => shapes.foldl (fun total shape => total + shapeSizeWithContext context shape) 0
  | .named name => ((lookupInfo name context).map StructInfo.size).getD 1

/-- Counterpart of Cake's `size_of_sh_with_ctxt_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:184`): for a shape that is
    well formed against the empty context, the context-sensitive size agrees
    with the context-free `shapeSize`. -/
theorem shapeSizeWithContext_eq_shapeSize_of_isWfShape :
    ∀ (shape : Shape), isWfShape ([] : StructContext) shape = true →
      ∀ (context : StructContext), shapeSizeWithContext context shape = Shape.shapeSize shape := by
  intro shape
  induction shape using shapeSizeWithContext.induct with
  | case1 =>
      intro _ context
      simp [shapeSizeWithContext]
  | case2 shapes ih =>
      intro hwf context
      simp only [isWfShape.eq_def] at hwf
      simp only [shapeSizeWithContext, Shape.shapeSize]
      exact foldl_shapeSizeWithContext_eq_shapeSize context shapes
        (fun shape hmem h => ih shape hmem h context) hwf 0
  | case3 name =>
      intro hwf context
      simp only [isWfShape.eq_def, isWfShapeHOL_named, StructContext.toHOL,
        List.map_nil, lookupInfo, Option.isSome_none] at hwf
      exact (Bool.false_ne_true hwf).elim
where
  /-- Fold form of `shapeSizeWithContext_eq_shapeSize_of_isWfShape`, needed for
      the `comb` case. -/
  foldl_shapeSizeWithContext_eq_shapeSize (context : StructContext) (shapes : List Shape)
      (hshape : ∀ shape ∈ shapes, isWfShape ([] : StructContext) shape = true →
        shapeSizeWithContext context shape = Shape.shapeSize shape)
      (hwf : isWfShape.isWfShapeList ([] : StructContext) shapes = true) (acc : Nat) :
      shapes.foldl (fun total shape => total + shapeSizeWithContext context shape) acc =
        shapes.foldl (fun total shape => total + Shape.shapeSize shape) acc := by
    induction shapes generalizing acc with
    | nil => rfl
    | cons shape shapes ih =>
        rw [isWfShape.isWfShapeList.eq_def] at hwf
        rw [Bool.and_eq_true] at hwf
        obtain ⟨hhead, htail⟩ := hwf
        simp only [List.foldl_cons]
        rw [hshape shape (by simp) hhead]
        exact ih (fun s hs => hshape s (by simp [hs])) htail (acc + Shape.shapeSize shape)


inductive StatErr where
  | scope (message : String)
  | warning (message : String)
  | general (message : String)
  | shape (message : String)
  deriving Repr

abbrev StaticResult (α : Type u) := Except StatErr α × List StatErr

def staticResultOk (result : StaticResult α) : Bool :=
  match result.1 with
  | Except.ok _ => true
  | Except.error _ => false

def statErrMessage : StatErr → String
  | .scope message => message
  | .warning message => message
  | .general message => message
  | .shape message => message

def staticResultErrorMessage (result : StaticResult α) : Option String :=
  match result.1 with
  | Except.ok _ => none
  | Except.error error => some (statErrMessage error)

inductive Reachable where
  | isReach
  | notReach
  | warnReach
  deriving DecidableEq, Repr

inductive LastStmt where
  | retLast
  | raiseLast
  | tailLast
  | breakLast
  | contLast
  | condExitLast
  | invisLast
  | otherLast
  deriving DecidableEq, Repr

structure FuncInfo where
  returnShape : Shape
  params : List (VarName × Shape)
  deriving Repr

structure LocalInfo where
  shapedBased : ShapedBased
  deriving Repr

structure GlobalInfo where
  shape : Shape
  deriving Repr

inductive Scope where
  | funScope (function : FunName) (location : String)
  | declScope (name : VarName)
  | structScope (struct : StructName) (field : FieldName)
  | topLevel
  deriving Repr

structure Context where
  locals : InfoMap LocalInfo
  globals : InfoMap GlobalInfo
  functions : InfoMap FuncInfo
  expectedReturn : Option Shape
  exceptions : InfoMap Shape
  structs : StructContext
  scope : Scope
  inLoop : Bool
  reachable : Reachable
  last : LastStmt
  location : String
  deriving Repr

structure ExpReturn where
  shapedBased : ShapedBased
  deriving Repr

structure ExpsReturn where
  shapedBased : List ShapedBased
  deriving Repr

structure ProgReturn where
  exitsFunction : Bool
  exitsLoop : Bool
  last : LastStmt
  variableDelta : InfoMap LocalInfo
  currentLocation : String
  deriving Repr

def staticResultLocation (result : StaticResult ProgReturn) : Option String :=
  match result.1 with
  | Except.ok value => some value.currentLocation
  | Except.error _ => none

inductive ScopedId where
  | variable
  | function
  | struct
  deriving DecidableEq, Repr

def validateDecl (context : StructContext) : Decl α → Bool
  | .function declaration =>
      declaration.params.all (fun (_, shape) => isWfShape context shape) &&
        isWfShape context declaration.returnShape
  | .decl shape _ _ => isWfShape context shape
  | .exnDecl _ shape => isWfShape context shape
  | .name name fields =>
      (lookupInfo name context).isNone && isWfFields context fields

def staticOk (value : α) : StaticResult α := (Except.ok value, [])

def staticError (error : StatErr) : StaticResult α := (Except.error error, [])

/-- Emit a warning without aborting the static check.  The original CakeML
    `panStatic` logs a `WarningErr` for a redeclared top-level variable and
    continues checking, so the port must accept the program too. -/
def staticWarn (warning : StatErr) : StaticResult Unit := (Except.ok (), [warning])

def staticBind (result : StaticResult α) (continuation : α → StaticResult β) :
    StaticResult β :=
  match result with
  | (Except.error error, warnings) => (Except.error error, warnings)
  | (Except.ok value, warnings) =>
      let next := continuation value
      (next.1, warnings ++ next.2)

/-! Cake's `sh_bd_from_bd` changes the basedness of every word while preserving
    the already-validated shape tree.  The named-structure case of
    `sh_bd_from_sh` is equivalent to applying it to the stored field tree; the
    static checker has already validated that tree when the structure entered
    the context. -/
mutual
  def shapedBasedWithBase : Based → ShapedBased → ShapedBased
    | basedness, .word _ => .word basedness
    | basedness, .struct fields =>
        .struct (shapedBasedWithBaseList basedness fields)
    | basedness, .named name fields =>
        .named name (shapedBasedWithBaseFields basedness fields)
  termination_by _ shaped => sizeOf shaped
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  def shapedBasedWithBaseList (basedness : Based) : List ShapedBased → List ShapedBased
    | [] => []
    | shaped :: shapedRest =>
        shapedBasedWithBase basedness shaped ::
          shapedBasedWithBaseList basedness shapedRest
  termination_by shapedRest => sizeOf shapedRest
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def shapedBasedWithBaseFields (basedness : Based) :
      List (FieldName × ShapedBased) → List (FieldName × ShapedBased)
    | [] => []
    | (field, shaped) :: fieldRest =>
        (field, shapedBasedWithBase basedness shaped) ::
          shapedBasedWithBaseFields basedness fieldRest
  termination_by fieldRest => sizeOf fieldRest
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-! Cake's `sh_bd_branch` retains a complete value only when the two shaped
    values are equal, including their basedness.  A shape-only comparison is
    insufficient here: differing WordB states must become NotTrusted. -/
def shapedBasedBranch (left right : ShapedBased) : ShapedBased :=
  if left == right then left else shapedBasedWithBase .notTrusted left

/-! List-backed counterparts of Cake's `mapWithKey` and `unionWith` used by
    `branch_loc_inf`.  `InfoMap` is the executable association-list view of
    Cake's finite map; retaining the left map's order also preserves the
    first-match lookup convention used by the checker. -/
def infoMapMapWithKey (f : String → α → β) : InfoMap α → InfoMap β
  | [] => []
  | (name, value) :: entries =>
      (name, f name value) :: infoMapMapWithKey f entries

def infoMapDelete [BEq String] (name : String) : InfoMap α → InfoMap α
  | [] => []
  | (candidate, value) :: entries =>
      if candidate == name then infoMapDelete name entries
      else (candidate, value) :: infoMapDelete name entries

def infoMapUnionWith [BEq String] (combine : α → α → α) :
    InfoMap α → InfoMap α → InfoMap α
  | [], right => right
  | (name, value) :: left, right =>
      match lookupInfo name right with
      | some rightValue =>
          (name, combine value rightValue) ::
            infoMapUnionWith combine left (infoMapDelete name right)
      | none => (name, value) :: infoMapUnionWith combine left right

/-! Source-shaped port of Cake `branch_loc_inf_def` (`panStaticScript.sml:311`
    onward).  A variable present in only one branch is compared against the
    incoming context; variables present in both branches are merged directly. -/
def branchLocInf [BEq String] (context : InfoMap LocalInfo)
    (left right : InfoMap LocalInfo) : InfoMap LocalInfo :=
  let left' := infoMapMapWithKey (fun name info =>
    if (lookupInfo name right).isNone then
      match lookupInfo name context with
      | some prior =>
          { info with shapedBased :=
              shapedBasedBranch info.shapedBased prior.shapedBased }
      | none =>
          { info with shapedBased :=
              shapedBasedWithBase .notTrusted info.shapedBased }
    else info) left
  let right' := infoMapMapWithKey (fun name info =>
    if (lookupInfo name left).isNone then
      match lookupInfo name context with
      | some prior =>
          { info with shapedBased :=
              shapedBasedBranch info.shapedBased prior.shapedBased }
      | none =>
          { info with shapedBased :=
              shapedBasedWithBase .notTrusted info.shapedBased }
    else info) right
  infoMapUnionWith (fun leftInfo rightInfo =>
    { leftInfo with shapedBased :=
        shapedBasedBranch leftInfo.shapedBased rightInfo.shapedBased }) left' right'

/-! Cake's sequential local-info composition is `union y x`: the later
    delta (`y`) takes precedence over the incoming map (`x`). -/
def seqLocInf [BEq String] (previous delta : InfoMap LocalInfo) :
    InfoMap LocalInfo :=
  infoMapUnionWith (fun newer _older => newer) delta previous

/-! Exact source-shaped port of Cake `sh_bd_to_str_def`
    (`panStaticScript.sml:342-350`).  Basedness is intentionally erased for
    words, while named structures print only their declared name. -/
def shapedBasedToString : ShapedBased → String
  | .word _ => "1"
  | .struct [] => "{}"
  | .struct (head :: tail) =>
      "{" ++ shapedBasedToString head ++
        tail.foldl (fun result field =>
          result ++ "," ++ shapedBasedToString field) "" ++ "}"
  | .named name _ => name

def shapedBasedFromShapeWith (context : StructContext) (basedness : Based) :
    Shape → Option ShapedBased
  | .one => some (.word basedness)
  | .comb shapes =>
      match shapedBasedFromShapes context basedness shapes with
      | some fields => some (.struct fields)
      | none => none
  | .named name =>
      match lookupInfoWithRest name context with
      | some (info, _) =>
          some (.named name
            (info.shapedFields.map (fun (field, shaped) =>
              (field, shapedBasedWithBase basedness shaped))))
      | none => none
termination_by shape => sizeOf shape
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  shapedBasedFromShapes (context : StructContext) (basedness : Based) :
      List Shape → Option (List ShapedBased)
    | [] => some []
    | shape :: shapes => do
        let shaped ← shapedBasedFromShapeWith context basedness shape
        let rest ← shapedBasedFromShapes context basedness shapes
        pure (shaped :: rest)
  termination_by shapes => sizeOf shapes
    decreasing_by
      all_goals first | sizeOf_list_dec | decreasing_trivial

def shapedBasedFromShape (context : StructContext) : Shape → Option ShapedBased
  | .one => some (.word .trusted)
  | .comb shapes =>
      match shapedBasedFromShapes context shapes with
      | some fields => some (.struct fields)
      | none => none
  | .named name =>
      match lookupInfo name context with
      | some info => some (.named name info.shapedFields)
      | none => none
termination_by shape => sizeOf shape
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  shapedBasedFromShapes (context : StructContext) : List Shape → Option (List ShapedBased)
    | [] => some []
    | shape :: shapes => do
        let shaped ← shapedBasedFromShape context shape
        let rest ← shapedBasedFromShapes context shapes
        pure (shaped :: rest)
  termination_by shapes => sizeOf shapes
    decreasing_by
      all_goals first | sizeOf_list_dec | decreasing_trivial

def shapedBasedFieldAt : Nat → ShapedBased → Option ShapedBased
  | index, .struct fields => shapedBasedFieldAtList index fields
  | _, _ => none
where
  shapedBasedFieldAtList : Nat → List ShapedBased → Option ShapedBased
    | _, [] => none
    | 0, field :: _ => some field
    | index + 1, _ :: fields => shapedBasedFieldAtList index fields

def shapedBasedFieldNamed (name : FieldName) : ShapedBased → Option ShapedBased
  | .named _ fields => lookupInfo name fields
  | _ => none

def shapedBasedIsWord : ShapedBased → Bool
  | .word _ => true
  | _ => false

/-! Priority order for Cake's `based_merge`: `Based` dominates, followed by
    `NotTrusted`, `Trusted`, and finally `NotBased`. -/
def basedMerge : Based → Based → Based
  | .based, _ => .based
  | _, .based => .based
  | .notTrusted, _ => .notTrusted
  | _, .notTrusted => .notTrusted
  | .trusted, _ => .trusted
  | _, .trusted => .trusted
  | .notBased, .notBased => .notBased

def shapedBasedMerge : List ShapedBased → Based
  | [] => .notBased
  | .word basedness :: rest => basedMerge basedness (shapedBasedMerge rest)
  | _ :: rest => shapedBasedMerge rest

def shapedBasedSameShape : ShapedBased → ShapedBased → Bool
  | .word _, .word _ => true
  | .struct left, .struct right => shapedBasedSameShapes left right
  | .named left _, .named right _ => left == right
  | _, _ => false
where
  shapedBasedSameShapes : List ShapedBased → List ShapedBased → Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        shapedBasedSameShape left right && shapedBasedSameShapes lefts rights
    | _, _ => false

@[simp] theorem shapedBasedSameShape_struct_words :
    shapedBasedSameShape
      (.struct [.word .notBased, .word .notBased])
      (.struct [.word .notBased, .word .notBased]) = true := by
  rfl

/-! Direct source-shaped port of Cake's `sh_bd_has_shape_def`. -/
def shapedBasedHasShape : Shape → ShapedBased → Bool
  | .one, .word _ => true
  | .comb shapes, .struct shaped => shapedBasedHasShapeList shapes shaped
  | .named name, .named other _ => name == other
  | _, _ => false
where
  shapedBasedHasShapeList : List Shape → List ShapedBased → Bool
    | [], [] => true
    | [], _ :: _ => false
    | _ :: _, [] => false
    | shape :: shapes, shaped :: shapeds =>
        shapedBasedHasShape shape shaped && shapedBasedHasShapeList shapes shapeds

def shapesSame : Shape → Shape → Bool
  | .one, .one => true
  | .comb left, .comb right => shapesSameList left right
  | .named left, .named right => left == right
  | _, _ => false
where
  shapesSameList : List Shape → List Shape → Bool
    | [], [] => true
    | left :: lefts, right :: rights => shapesSame left right && shapesSameList lefts rights
    | _, _ => false

def shapedBasedFieldsMatch (context : StructContext)
    : List (FieldName × Shape) → List (FieldName × ShapedBased) → Bool
  | [], [] => true
  | (expectedName, expectedShape) :: expected,
      (actualName, actualShape) :: actual =>
      (expectedName == actualName) &&
        (match shapedBasedFromShape context expectedShape with
        | some shape => shapedBasedSameShape shape actualShape
        | none => false) &&
        shapedBasedFieldsMatch context expected actual
  | _, _ => false

def staticScopeDescription : Scope → String
  | .funScope name suffix => "function " ++ name ++ suffix
  | .declScope name => "initialisation of global variable " ++ name
  | .structScope name field => "declaration of field " ++ field ++
      " in named struct " ++ name
  | .topLevel => "top-level declaration"

def staticScopedIdDescription : ScopedId → String
  | .variable => "variable "
  | .function => "function "
  | .struct => "struct name "

/-! Source-shaped port of CakeML's `get_scope_msg_def`
    (`cakeml/pancake/panStaticScript.sml:442-451`). -/
def staticScopeMessage (idType : ScopedId) (location id : String) (scope : Scope) : String :=
  location ++ staticScopedIdDescription idType ++ id ++
    " is not in scope in " ++ staticScopeDescription scope ++ "\n"

/-! Source-shaped port of CakeML's `check_global_var_def`
    (`cakeml/pancake/panStaticScript.sml:625-630`).  Keeping the lookup and
    diagnostic boundary explicit prevents callers from silently replacing
    Cake's location- and scope-sensitive error with a generic message. -/
def checkGlobalVar [BEq String] (context : Context) (name : VarName) :
    StaticResult GlobalInfo :=
  match lookupInfo name context.globals with
  | some info => staticOk info
  | none =>
      staticError (.scope
        (staticScopeMessage .variable context.location name context.scope))

/-! Source-shaped port of CakeML's `check_local_var_def`
    (`cakeml/pancake/panStaticScript.sml:633-638`). -/
def checkLocalVar [BEq String] (context : Context) (name : VarName) :
    StaticResult LocalInfo :=
  match lookupInfo name context.locals with
  | some info => staticOk info
  | none =>
      staticError (.scope
        (staticScopeMessage .variable context.location name context.scope))

/-! Source-shaped port of CakeML's `get_redec_msg_def`
    (`cakeml/pancake/panStaticScript.sml:478-489`). -/
def getRedecMessage (idType : ScopedId) (location id : String) (scope : Scope) : String :=
  location ++ staticScopedIdDescription idType ++ id ++
    " is redeclared in " ++ staticScopeDescription scope ++ "\n"

/-! Source-shaped port of CakeML's `primitive_idents_def`
    (`cakeml/pancake/panStaticScript.sml:457-459`). -/
def primitiveIdents : List String := ["__add_with_carry__"]

/-! Source-shaped port of CakeML's `add_primitive_hint_def`
    (`cakeml/pancake/panStaticScript.sml:464-473`). -/
def addPrimitiveHint (functionName message : String) : String :=
  if functionName ∈ primitiveIdents then
    message ++ "  note: " ++ functionName ++
      " is a built-in primitive only available in declaration or assignment RHS positions\n"
  else message

/-! Source-shaped port of CakeML's `get_memop_msg_def`
    (`cakeml/pancake/panStaticScript.sml:497-511`). -/
def getMemopMessage (isLocal isLoad isUntrusted : Bool)
    (location : String) (scope : Scope) : String :=
  let memoryType := if isLocal then "local " else "shared "
  let operationType := if isLoad then "load " else "store "
  let issue :=
    if isLocal then
      if isUntrusted then "may not be " else "is not "
    else
      if isUntrusted then "may be " else "is "
  location ++ memoryType ++ operationType ++ "address " ++ issue ++
    "calculated from base in " ++ staticScopeDescription scope ++ "\n"

/-! Source-shaped port of CakeML's `get_oparg_msg_def`
    (`cakeml/pancake/panStaticScript.sml:517-527`). -/
def getOpargMessage (isExact : Bool) (expected given location operation : String)
    (scope : Scope) : String :=
  location ++ "operation " ++ operation ++
    (if isExact then " only accepts " else " requires at least ") ++
    expected ++ " operands, " ++ given ++ " provided in " ++
    staticScopeDescription scope ++ "\n"

/-! Cake's memory-operation diagnostics distinguish local addresses, which
    should not be based on `@base`, from shared addresses, which should.  A
    `NotTrusted` address is reported as a possibility in either direction;
    `Trusted` is exempt from both warnings. -/
def staticMemoryWarning (context : Context) (isLocal isLoad : Bool)
    (address : ShapedBased) : Option StatErr :=
  match address with
  | .word basedness =>
      let untrusted : Option Bool :=
        if isLocal then
          match basedness with
          | .notBased => some false
          | .notTrusted => some true
          | _ => none
        else
          match basedness with
          | .based => some false
          | .notTrusted => some true
          | _ => none
      untrusted.map (fun isUntrusted =>
        .warning (getMemopMessage isLocal isLoad isUntrusted
          context.location context.scope))
  | _ => none

def staticAddWarning (result : StaticResult α) (warning : Option StatErr) :
    StaticResult α :=
  match warning with
  | none => result
  | some warning => (result.1, result.2 ++ [warning])

/-! Source-shaped port of CakeML's `check_redec_var_def`
    (`cakeml/pancake/panStaticScript.sml:641-647`).  Cake returns unit and logs
    a warning when either local or global lookup finds the name. -/
def checkRedecVar [BEq String] (context : Context) (name : VarName) :
    StaticResult Unit :=
  if (lookupInfo name context.locals).isSome ||
      (lookupInfo name context.globals).isSome then
    staticWarn (.warning (getRedecMessage .variable context.location name context.scope))
  else staticOk ()

/-! Compatibility view used by callers that only need the optional warning. -/
def staticRedeclarationWarning [BEq String] (context : Context)
    (name : VarName) : Option StatErr :=
  (checkRedecVar context name).2.head?

def staticPrependWarning (warning : Option StatErr) (result : StaticResult α) :
    StaticResult α :=
  match warning with
  | none => result
  | some warning => (result.1, warning :: result.2)

/-! Source-shaped port of CakeML's `check_struct_fields_def`
    (`cakeml/pancake/panStaticScript.sml:717-765`). -/
def checkStructFields [BEq String] (context : Context) (structName : StructName) :
    List (FieldName × Shape) → List (FieldName × ShapedBased) → StaticResult Unit
  | [], [] => staticOk ()
  | [], (field, _) :: _ =>
      staticError (.general (context.location ++ "unexpected field " ++ field ++
        " given to named struct " ++ structName ++ " in " ++
        staticScopeDescription context.scope ++ "\n"))
  | (field, shape) :: fields, actual =>
      match actual.filter (fun (candidate, _) => candidate == field) with
      | [] =>
          staticError (.shape (context.location ++ "missing field " ++ field ++
            " in named struct " ++ structName ++ " constant in " ++
            staticScopeDescription context.scope ++ "\n"))
      | [(_, shaped)] =>
          if shapedBasedHasShape shape shaped then
            checkStructFields context structName fields
              (actual.filter (fun (candidate, _) => candidate != field))
          else
            staticError (.shape (context.location ++
              "value for field " ++ field ++ " given to named struct " ++ structName ++
              " has shape " ++ shapedBasedToString shaped ++
              " instead of declared shape " ++ Shape.shapeToString shape ++ " in " ++
              staticScopeDescription context.scope ++ "\n"))
      | _ =>
          staticError (.shape (context.location ++ "multiple values for field " ++ field ++
            " in named struct " ++ structName ++ " constant in " ++
            staticScopeDescription context.scope ++ "\n"))

/-! Source-shaped port of CakeML's `get_non_word_msg_def`
    (`cakeml/pancake/panStaticScript.sml:552-557`). -/
def getNonWordMessage (description shapeString location : String)
    (scope : Scope) : String :=
  location ++ description ++ " has shape " ++ shapeString ++
    " instead of a word in " ++ staticScopeDescription scope ++ "\n"

/-! Source-shaped port of CakeML's `get_implementation_err_msg_def`
    (`cakeml/pancake/panStaticScript.sml:568-572`). -/
def getImplementationErrorMessage (description location : String)
    (scope : Scope) : String :=
  location ++ description ++ " in " ++ staticScopeDescription scope ++ "\n" ++
    "this should never happen. please report to a compiler developer\n"

/-! Source-shaped port of CakeML's `check_shape_def`
    (`cakeml/pancake/panStaticScript.sml:759-773`).  The location and scope
    are part of the observable error, so they must not be discarded in favour
    of the earlier generic validity check. -/
def checkShape [BEq String] (context : StructContext) (location : String)
    (scope : Scope) : Shape → StaticResult Unit
  | .one => staticOk ()
  | .comb shapes => checkShapes shapes
  | .named name =>
      if (lookupInfo name context).isSome then
        staticOk ()
      else
        staticError (.scope (staticScopeMessage .struct location name scope))
termination_by shape => sizeOf shape
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  checkShapes : List Shape → StaticResult Unit
    | [] => staticOk ()
    | shape :: rest =>
        staticBind (checkShape context location scope shape) (fun _ =>
          checkShapes rest)
  termination_by shapes => sizeOf shapes
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

/-! Source-shaped port of CakeML's `check_operands_def`
    (`cakeml/pancake/panStaticScript.sml:660-671`). -/
def checkOperands [BEq String] (context : Context) (opString : String) :
    List ShapedBased → StaticResult Based
  | [] => staticOk .notBased
  | .word basedness :: arguments =>
      staticBind (checkOperands context opString arguments) (fun restBasedness =>
        staticOk (basedMerge basedness restBasedness))
  | shaped :: _ =>
      staticError (.shape (getNonWordMessage
        ("operation " ++ opString ++ " operand")
        (shapedBasedToString shaped) context.location context.scope))

def checkExp [BEq String] (context : Context) : Exp α → StaticResult ExpReturn
  | .const _ => staticOk { shapedBased := .word .notBased }
  | .var .local name =>
      staticBind (checkLocalVar context name) (fun info =>
        staticOk { shapedBased := info.shapedBased })
  | .var .global name =>
      staticBind (checkGlobalVar context name) (fun info =>
        match shapedBasedFromShape context.structs info.shape with
        | some shaped => staticOk { shapedBased := shaped }
        | none => staticError (.scope (getImplementationErrorMessage
            "static analysis failed to convert in-scope shape"
            context.location context.scope)))
  | .rStruct expressions =>
      staticBind (checkExps context expressions) (fun result =>
        staticOk { shapedBased := .struct result.shapedBased })
  | .rField index value =>
      staticBind (checkExp context value) (fun result =>
        match shapedBasedFieldAt index result.shapedBased with
        | some shaped => staticOk { shapedBased := shaped }
        | none => staticError (.shape (context.location ++ "expression shape " ++
            shapedBasedToString result.shapedBased ++ " has no field at index " ++
            toString index ++ " in " ++ staticScopeDescription context.scope ++ "\n")))
  | .nStruct name fields =>
      match lookupInfo name context.structs with
      | none => staticError (.scope
          (staticScopeMessage .struct context.location name context.scope))
      | some info =>
          staticBind (checkNamedExps context fields) (fun actual =>
            staticBind (checkStructFields context name info.fields actual) (fun _ =>
              staticOk { shapedBased := .named name actual }))
  | .nField name value =>
      staticBind (checkExp context value) (fun result =>
        match shapedBasedFieldNamed name result.shapedBased with
        | some shaped => staticOk { shapedBased := shaped }
        | none => staticError (.shape (context.location ++ "expression shape " ++
            shapedBasedToString result.shapedBased ++ " has no field " ++ name ++
            " in " ++ staticScopeDescription context.scope ++ "\n")))
  | .load shape address =>
      let checkLoadResult : ExpReturn → StaticResult ExpReturn :=
        fun result =>
          if shapedBasedIsWord result.shapedBased then
            match shapedBasedFromShape context.structs shape with
            | some shaped =>
                staticAddWarning (staticOk { shapedBased := shaped })
                  (staticMemoryWarning context true true result.shapedBased)
            | none => staticError (.scope (getImplementationErrorMessage
                "static analysis failed to convert in-scope shape"
                context.location context.scope))
          else
            staticError (.shape (getNonWordMessage "load address"
              (shapedBasedToString result.shapedBased)
              context.location context.scope))
      staticBind (checkShape context.structs context.location context.scope shape)
        (fun _ => staticBind (checkExp context address) checkLoadResult)
  | .load32 address =>
      staticBind (checkExp context address) (fun result =>
        if shapedBasedIsWord result.shapedBased then
          staticAddWarning (staticOk { shapedBased := .word .trusted })
            (staticMemoryWarning context true true result.shapedBased)
        else
          staticError (.shape (getNonWordMessage "load address"
            (shapedBasedToString result.shapedBased)
            context.location context.scope)))
  | .loadByte address =>
      staticBind (checkExp context address) (fun result =>
        if shapedBasedIsWord result.shapedBased then
          staticAddWarning (staticOk { shapedBased := .word .trusted })
            (staticMemoryWarning context true true result.shapedBased)
        else
          staticError (.shape (getNonWordMessage "load address"
            (shapedBasedToString result.shapedBased)
            context.location context.scope)))
  | .op operator expressions =>
      let operation := binopToString operator
      let isExact :=
        match operator with
        | .sub => true
        | _ => false
      let arityOk := if isExact then expressions.length == 2 else expressions.length >= 2
      if !arityOk then
        staticError (.general (getOpargMessage isExact (if isExact then "2" else "2")
          (toString expressions.length) context.location operation context.scope))
      else
        staticBind (checkExps context expressions) (fun result =>
          staticBind (checkOperands context operation result.shapedBased) (fun basedness =>
            staticOk { shapedBased := .word basedness }))
  | .panOp operator expressions =>
      let operation := panopToString operator
      if expressions.length != 2 then
        staticError (.general (getOpargMessage true "2"
          (toString expressions.length) context.location operation context.scope))
      else
        staticBind (checkExps context expressions) (fun result =>
          staticBind (checkOperands context operation result.shapedBased) (fun basedness =>
            staticOk { shapedBased := .word basedness }))
  | .cmp _ left right =>
      staticBind (checkExp context left) (fun leftResult =>
        staticBind (checkExp context right) (fun rightResult =>
          if shapedBasedSameShape leftResult.shapedBased rightResult.shapedBased then
            staticOk { shapedBased := .word .notBased }
          else staticError (.shape (context.location ++
            "comparison given operands of different shapes in " ++
            staticScopeDescription context.scope ++ "\n"))))
  | .shift _ left right =>
      staticBind (checkExp context left) (fun leftResult =>
        staticBind (checkExp context right) (fun rightResult =>
          if shapedBasedHasShape .one leftResult.shapedBased then
            if shapedBasedHasShape .one rightResult.shapedBased then
              staticOk { shapedBased := rightResult.shapedBased }
            else staticError (.shape (getNonWordMessage "shift expression"
              (shapedBasedToString rightResult.shapedBased)
              context.location context.scope))
          else staticError (.shape (getNonWordMessage "shifted expression"
            (shapedBasedToString leftResult.shapedBased)
            context.location context.scope))))
  | .baseAddr => staticOk { shapedBased := .word .based }
  | .topAddr => staticOk { shapedBased := .word .based }
  | .bytesInWord => staticOk { shapedBased := .word .notBased }
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  checkExps [BEq String] (context : Context) : List (Exp α) → StaticResult ExpsReturn
    | [] => staticOk { shapedBased := [] }
    | expression :: expressions =>
        staticBind (checkExp context expression) (fun result =>
          staticBind (checkExps context expressions) (fun rest =>
            staticOk { shapedBased := result.shapedBased :: rest.shapedBased }))
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  checkNamedExps [BEq String] (context : Context) :
      List (FieldName × Exp α) → StaticResult (List (FieldName × ShapedBased))
    | [] => staticOk []
    | (name, expression) :: fields =>
        staticBind (checkExp context expression) (fun result =>
          staticBind (checkNamedExps context fields) (fun rest =>
            staticOk ((name, result.shapedBased) :: rest)))
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def shapedBasedMatchesShape (context : StructContext) (shape : Shape)
    (shaped : ShapedBased) : Bool :=
  match shapedBasedFromShape context shape with
  | some expected => shapedBasedSameShape expected shaped
  | none => false

def functionArgumentsMatch (context : StructContext) :
    List (VarName × Shape) → List ShapedBased → Bool
  | [], [] => true
  | (_, shape) :: parameters, argument :: arguments =>
      shapedBasedMatchesShape context shape argument &&
        functionArgumentsMatch context parameters arguments
  | _, _ => false

/-! Source-shaped port of CakeML's `check_fun_name_def`
    (`panStaticScript.sml:616-621`).  In particular, an unknown function uses
    the normal scope diagnostic and the primitive hint, rather than a separate
    implementation-specific error string. -/
def checkFunctionName [BEq String] (context : Context) (name : FunName) :
    StaticResult FuncInfo :=
  match lookupInfo name context.functions with
  | none =>
      staticError (.scope
        (addPrimitiveHint name
          (staticScopeMessage .function context.location name context.scope)))
  | some info => staticOk info

def checkPrimitiveArgs [BEq String] (context : Context) (operator : PrimOp)
    (arguments : List ShapedBased) : StaticResult ShapedBased :=
  match operator with
  | .addCarry =>
      if arguments.length != 3 then
        staticError (.general (getOpargMessage true "3" (toString arguments.length)
          context.location (primopToString operator) context.scope))
      else
        staticBind (checkOperands context (primopToString operator) arguments)
          (fun basedness =>
            staticOk (.struct [.word basedness, .word .notBased]))

def progOk (last : LastStmt) (exitsFunction exitsLoop : Bool) (location : String) :
    StaticResult ProgReturn :=
  staticOk
    { exitsFunction := exitsFunction, exitsLoop := exitsLoop, last := last,
      variableDelta := [], currentLocation := location }

/-! A local assignment/call/load updates the basedness tracked for the local
    variable.  CakeML's `sh_bd_from_bd Trusted` preserves the shape tree while
    making every word trusted; `shapedBasedWithBase` is its executable
    counterpart. -/
def localVariableDelta (name : VarName) (info : LocalInfo) : InfoMap LocalInfo :=
  [(name, { info with shapedBased := shapedBasedWithBase .trusted info.shapedBased })]

def removeLocalVariableDelta (name : VarName) (result : ProgReturn) : ProgReturn :=
  { result with variableDelta := infoMapDelete name result.variableDelta }

/-! Source-shaped port of CakeML's `get_shape_mismatch_msg_def`
    (`cakeml/pancake/panStaticScript.sml:560-566`). -/
def getShapeMismatchMessage (description actualShape expectedShape location : String)
    (scope : Scope) : String :=
  location ++ description ++ " has shape " ++ actualShape ++
    " instead of declared shape " ++ expectedShape ++ " in " ++
    staticScopeDescription scope ++ "\n"

def checkCallDestination [BEq String] (context : Context) (functionName : FunName)
    (returnShape : Shape)
    : Option (VarKind × VarName) → StaticResult ProgReturn
  | none => progOk .otherLast false false context.location
  | some (kind, name) =>
      match kind with
      | .local =>
          staticBind (checkLocalVar context name) (fun localInfo =>
            if shapedBasedHasShape returnShape localInfo.shapedBased then
              staticOk
                { exitsFunction := false, exitsLoop := false, last := .otherLast,
                  variableDelta := localVariableDelta name localInfo,
                  currentLocation := context.location }
            else
              staticError (.shape (getShapeMismatchMessage
                ("result of function call " ++ functionName ++
                  " assigned to local variable " ++ name)
                (Shape.shapeToString returnShape)
                (shapedBasedToString localInfo.shapedBased)
                context.location context.scope)))
      | .global =>
          staticBind (checkGlobalVar context name) (fun globalInfo =>
            if shapesSame globalInfo.shape returnShape then
              progOk .otherLast false false context.location
            else
              staticError (.shape (getShapeMismatchMessage
                ("result of function call " ++ functionName ++
                  " assigned to global variable " ++ name)
                (Shape.shapeToString returnShape)
                (Shape.shapeToString globalInfo.shape)
                context.location context.scope)))

/-! Cake checks a call destination's scope before resolving the callee.  The
    later destination check validates its return shape after the callee and
    arguments have been checked; keeping these phases separate preserves both
    the diagnostics and their ordering. -/
def checkCallDestinationScope [BEq String] (context : Context) :
    Option (VarKind × VarName) → StaticResult Unit
  | none => staticOk ()
  | some (kind, name) =>
      match kind with
      | .local => staticBind (checkLocalVar context name) (fun _ => staticOk ())
      | .global => staticBind (checkGlobalVar context name) (fun _ => staticOk ())

/-! These helpers are the executable counterparts of CakeML's
    `next_is_reachable`, `next_now_unreachable`, and `reached_warnable`.
    Reachability is deliberately kept in the checker context: a sequence may
    contain transparent nodes (`Seq`, `Tick`, and `Annot`) before the first
    statement which can actually trigger the warning. -/
def staticLastStmtString : LastStmt → String
  | .retLast => "return"
  | .raiseLast => "raise"
  | .tailLast => "tail call"
  | .breakLast => "break"
  | .contLast => "continue"
  | .condExitLast => "exiting conditional"
  | _ => ""

/-! Source-shaped port of CakeML's `get_unreach_msg_def`
    (`cakeml/pancake/panStaticScript.sml:530-536`). -/
def getUnreachMessage (location last : String) (scope : Scope) : String :=
  location ++ "unreachable statement(s) after " ++ last ++ " in " ++
    staticScopeDescription scope ++ "\n"

/-! Source-shaped port of CakeML's `get_rogue_msg_def`
    (`cakeml/pancake/panStaticScript.sml:542-549`). -/
def getRogueMessage (isBreak : Bool) (location : String) (scope : Scope) : String :=
  location ++ (if isBreak then "break " else "continue ") ++
    "statement outside loop in " ++ staticScopeDescription scope ++ "\n"

/-! Source-shaped port of CakeML's `check_func_args_def`
    (`cakeml/pancake/panStaticScript.sml:690-718`). -/
def checkFuncArgs [BEq String] (context : Context) (functionName : FunName) :
    List (VarName × Shape) → List ShapedBased → StaticResult Unit
  | (parameter, shape) :: parameters, argument :: arguments =>
      if shapedBasedMatchesShape context.structs shape argument then
        checkFuncArgs context functionName parameters arguments
      else
        staticError (.shape (getShapeMismatchMessage
          ("value for argument " ++ parameter ++ " given to function " ++ functionName)
          (shapedBasedToString argument) (Shape.shapeToString shape)
          context.location context.scope))
  | (parameter, _) :: _, [] =>
      staticError (.general (context.location ++ "argument " ++ parameter ++
        " for call to function " ++ functionName ++ " is missing in " ++
        staticScopeDescription context.scope ++ "\n"))
  | [], _ :: _ =>
      staticError (.general (context.location ++ "extra arguments given to function " ++
        functionName ++ " in " ++ staticScopeDescription context.scope ++ "\n"))
  | [], [] => staticOk ()

def staticUnreachableWarning (context : Context) (last : LastStmt) : StatErr :=
  .warning (getUnreachMessage context.location (staticLastStmtString last) context.scope)

def nextIsReachable : Reachable → LastStmt → Reachable
  | .isReach, last =>
      if last == .invisLast || last == .otherLast then .isReach else .warnReach
  | reachable, _ => reachable

def nextNowUnreachable (reachable next : Reachable) : Bool :=
  reachable == .isReach && next != .isReach

/-! Source-shaped port of CakeML's `branch_last_stmt_def`
    (`cakeml/pancake/panStaticScript.sml:409-412`). -/
def branchLastStmt (doubleRet doubleLoopExit : Bool) : LastStmt :=
  if doubleRet || doubleLoopExit then .condExitLast else .otherLast

def reachedWarnable (program : Prog α) (context : Context) :
    Option LastStmt × Context :=
  match program with
  | .seq _ _ | .tick | .annot _ _ => (none, context)
  | _ =>
      if context.reachable == .warnReach then
        (some context.last, { context with reachable := .notReach })
      else
        (none, context)

def seqLastStmt (first second : LastStmt) : LastStmt :=
  if second == .invisLast then first else second

def checkProg [BEq String] (context : Context) : Prog α → StaticResult ProgReturn
  | .skip => progOk .otherLast false false context.location
  | .dec name shape value body =>
      let checkInitialValue : ExpReturn → StaticResult ProgReturn :=
        fun result =>
          if shapedBasedHasShape shape result.shapedBased then
            let nextContext := { context with
              locals := (name, { shapedBased := result.shapedBased }) :: context.locals
              last := .otherLast }
            staticBind (checkProg nextContext body) (fun bodyResult =>
              staticOk { bodyResult with
                variableDelta := infoMapDelete name bodyResult.variableDelta })
          else
            staticError (.shape (getShapeMismatchMessage
              ("expression to initialise local variable " ++ name)
              (shapedBasedToString result.shapedBased)
              (Shape.shapeToString shape)
              context.location context.scope))
      staticBind (checkRedecVar context name) (fun _ =>
        staticBind (checkShape context.structs context.location context.scope shape) (fun _ =>
          staticBind (checkExp context value) checkInitialValue))
  | .assign .local name value =>
      staticBind (checkLocalVar context name) (fun info =>
        let checkValue : ExpReturn → StaticResult ProgReturn :=
          fun result =>
            if shapedBasedSameShape info.shapedBased result.shapedBased then
              staticOk
                { exitsFunction := false, exitsLoop := false, last := .otherLast,
                  variableDelta := [(name, { shapedBased := result.shapedBased })],
                  currentLocation := context.location }
            else
              staticError (.shape (getShapeMismatchMessage
                ("expression assigned to local variable " ++ name)
                (shapedBasedToString result.shapedBased)
                (shapedBasedToString info.shapedBased)
                context.location context.scope))
        staticBind (checkExp context value) checkValue)
  | .assign .global name value =>
      staticBind (checkGlobalVar context name) (fun info =>
        let checkValue : ExpReturn → StaticResult ProgReturn :=
          fun result =>
            if shapedBasedHasShape info.shape result.shapedBased then
              progOk .otherLast false false context.location
            else
              staticError (.shape (getShapeMismatchMessage
                ("expression assigned to global variable " ++ name)
                (shapedBasedToString result.shapedBased)
                (Shape.shapeToString info.shape)
                context.location context.scope))
        staticBind (checkExp context value) checkValue)
  | .primitive name operator arguments =>
      staticBind (checkLocalVar context name) (fun destinationInfo =>
        let checkResult : ShapedBased → StaticResult ProgReturn :=
          fun resultShape =>
            if shapedBasedSameShape destinationInfo.shapedBased resultShape then
              staticOk
                { exitsFunction := false, exitsLoop := false, last := .otherLast,
                  variableDelta := [(name, { shapedBased := resultShape })],
                  currentLocation := context.location }
            else
              staticError (.shape (getShapeMismatchMessage
                ("result of primitive " ++ primopToString operator ++
                  " assigned to local variable " ++ name)
                (shapedBasedToString resultShape)
                (shapedBasedToString destinationInfo.shapedBased)
                context.location context.scope))
        staticBind (checkCallArgs context arguments) (fun argumentResult =>
          staticBind (checkPrimitiveArgs context operator argumentResult.shapedBased)
            checkResult))
  | .store address value =>
      staticBind (checkExp context address) (fun addressResult =>
        staticBind (checkExp context value) (fun _valueResult =>
          if shapedBasedHasShape .one addressResult.shapedBased then
            staticAddWarning (progOk .otherLast false false context.location)
              (staticMemoryWarning context true false addressResult.shapedBased)
          else
            staticError (.shape (getNonWordMessage "store address"
              (shapedBasedToString addressResult.shapedBased)
              context.location context.scope))))
  | .store32 address value =>
      staticBind (checkExp context address) (fun addressResult =>
        staticBind (checkExp context value) (fun valueResult =>
          if shapedBasedHasShape .one addressResult.shapedBased then
            let warning :=
              staticMemoryWarning context true false addressResult.shapedBased
            if shapedBasedHasShape .one valueResult.shapedBased then
              staticAddWarning (progOk .otherLast false false context.location)
                warning
            else
              staticAddWarning
                (staticError (.shape (getNonWordMessage "store value"
                  (shapedBasedToString valueResult.shapedBased)
                  context.location context.scope)))
                warning
          else
            staticError (.shape (getNonWordMessage "store address"
              (shapedBasedToString addressResult.shapedBased)
              context.location context.scope))))
  | .storeByte address value =>
      staticBind (checkExp context address) (fun addressResult =>
        staticBind (checkExp context value) (fun valueResult =>
          if shapedBasedHasShape .one addressResult.shapedBased then
            let warning :=
              staticMemoryWarning context true false addressResult.shapedBased
            if shapedBasedHasShape .one valueResult.shapedBased then
              staticAddWarning (progOk .otherLast false false context.location)
                warning
            else
              staticAddWarning
                (staticError (.shape (getNonWordMessage "store value"
                  (shapedBasedToString valueResult.shapedBased)
                  context.location context.scope)))
                warning
          else
            staticError (.shape (getNonWordMessage "store address"
              (shapedBasedToString addressResult.shapedBased)
              context.location context.scope))))
  | .seq first second =>
      /- Cake checks both sides even after an exit. It updates reachability
         before each side and emits a warning only when the current node is
         warnable; Seq/Tick/Annot themselves are transparent. -/
      let (firstWarning, context1) := reachedWarnable first context
      let firstResult := checkProg context1 first
      let warningBeforeFirst := match firstWarning with
        | some last => [staticUnreachableWarning context1 last]
        | none => []
      match firstResult with
      | (Except.error error, warnings) =>
          (Except.error error, warningBeforeFirst ++ warnings)
      | (Except.ok firstInfo, firstWarnings) =>
          let nextReach := nextIsReachable context1.reachable firstInfo.last
          let context2 := { context1 with
            locals := seqLocInf context1.locals firstInfo.variableDelta
            reachable := nextReach
            last := if nextNowUnreachable context1.reachable nextReach then
              firstInfo.last else context1.last
            location := firstInfo.currentLocation }
          let (secondWarning, context3) := reachedWarnable second context2
          let warningBeforeSecond := match secondWarning with
            | some last => [staticUnreachableWarning context3 last]
            | none => []
          match checkProg context3 second with
          | (Except.error error, warnings) =>
              (Except.error error,
                warningBeforeFirst ++ firstWarnings ++ warningBeforeSecond ++ warnings)
          | (Except.ok secondInfo, secondWarnings) =>
              (Except.ok { secondInfo with
                  exitsFunction := firstInfo.exitsFunction || secondInfo.exitsFunction
                  exitsLoop := firstInfo.exitsLoop || secondInfo.exitsLoop
                  last := seqLastStmt firstInfo.last secondInfo.last
                  variableDelta := seqLocInf firstInfo.variableDelta
                    secondInfo.variableDelta },
                warningBeforeFirst ++ firstWarnings ++ warningBeforeSecond ++ secondWarnings)
  | .ite condition thenBranch elseBranch =>
      staticBind (checkExp context condition) (fun conditionResult =>
        if shapedBasedHasShape .one conditionResult.shapedBased then
          staticBind (checkProg context thenBranch) (fun thenResult =>
            staticBind (checkProg
              { context with location := thenResult.currentLocation } elseBranch) (fun elseResult =>
              let doubleRet := thenResult.exitsFunction && elseResult.exitsFunction
              let doubleLoopExit := thenResult.exitsLoop && elseResult.exitsLoop
              staticOk
                { exitsFunction := doubleRet, exitsLoop := doubleLoopExit,
                  last := branchLastStmt doubleRet doubleLoopExit,
                  variableDelta := branchLocInf context.locals
                    thenResult.variableDelta elseResult.variableDelta,
                  currentLocation := elseResult.currentLocation }))
        else
          staticError (.shape (getNonWordMessage "if condition"
            (shapedBasedToString conditionResult.shapedBased)
            context.location context.scope)))
  | .while condition body =>
      staticBind (checkExp context condition) (fun conditionResult =>
        if shapedBasedHasShape .one conditionResult.shapedBased then
          let loopContext := { context with inLoop := true }
          staticBind (checkProg loopContext body) (fun bodyResult =>
            staticOk {
              exitsFunction := false
              exitsLoop := false
              last := .otherLast
              variableDelta := branchLocInf context.locals bodyResult.variableDelta []
              currentLocation := context.location })
        else
          staticError (.shape (getNonWordMessage "while condition"
            (shapedBasedToString conditionResult.shapedBased)
            context.location context.scope)))
  | .break =>
      if context.inLoop then progOk .breakLast false true context.location
      else staticError (.general (getRogueMessage true context.location context.scope))
  | .continue =>
      if context.inLoop then progOk .contLast false true context.location
      else staticError (.general (getRogueMessage false context.location context.scope))
  | .call none function arguments =>
      /- Cake's `TailCall` checks the caller scope and declaration before the
         callee, arguments, and return-shape agreement. -/
      match context.scope with
      | .funScope callerName _ =>
          staticBind (checkFunctionName context callerName) (fun callerInfo =>
            staticBind (checkFunctionName context function) (fun functionInfo =>
              staticBind (checkCallArgs context arguments) (fun argumentResult =>
                if !shapesSame callerInfo.returnShape functionInfo.returnShape then
                  staticError (.shape (getShapeMismatchMessage
                    ("result of function call " ++ function ++ " to return")
                    (Shape.shapeToString functionInfo.returnShape)
                    (Shape.shapeToString callerInfo.returnShape)
                    context.location context.scope))
                else
                  staticBind (checkFuncArgs context function functionInfo.params
                      argumentResult.shapedBased) (fun _ =>
                    progOk .tailLast true false context.location))))
      | _ =>
          staticError (.general (getImplementationErrorMessage
            "tail call found outside function scope"
            context.location context.scope))
  | .call (some (destination, handler)) function arguments =>
      staticBind (checkCallDestinationScope context destination) (fun _ =>
        staticBind (checkFunctionName context function) (fun functionInfo =>
          let returnShape := functionInfo.returnShape
          staticBind (checkCallArgs context arguments) (fun argumentResult =>
            staticBind (checkFuncArgs context function functionInfo.params
                argumentResult.shapedBased) (fun _ =>
              match handler with
            | none => checkCallDestination context function returnShape destination
            | some (exception, handlerVariable, handlerProgram) =>
                staticBind (checkCallDestination context function returnShape destination)
                  (fun destinationResult =>
                    match destination with
                    | some (.global, _) =>
                        -- CakeML `panStaticScript.sml:1256-1264`: a handled call
                        -- assigning to a global only requires the handler variable
                        -- to be a local; the exception need not be declared and
                        -- the handler variable's shape is not checked.
                        match lookupInfo handlerVariable context.locals with
                        | none => staticError (.scope
                            (staticScopeMessage .variable context.location
                              handlerVariable context.scope))
                        | some handlerInfo =>
                            let handlerContext := { context with locals :=
                              (handlerVariable,
                                { handlerInfo with shapedBased :=
                                    shapedBasedWithBase .trusted handlerInfo.shapedBased }) ::
                                context.locals }
                            staticBind (checkProg handlerContext handlerProgram) (fun _ =>
                              staticOk destinationResult)
                    | _ =>
                        match lookupInfo exception context.exceptions,
                            lookupInfo handlerVariable context.locals with
                        | none, _ => staticError (.scope ("exception " ++ exception ++
                            " is not declared\n"))
                        | _, none => staticError (.scope
                            (staticScopeMessage .variable context.location
                              handlerVariable context.scope))
                        | some exceptionShape, some handlerInfo =>
                            if !shapedBasedHasShape exceptionShape handlerInfo.shapedBased then
                              staticError (.shape ("handler variable " ++ handlerVariable ++
                                " does not match shape of exception " ++ exception ++ "\n"))
                            else
                              match shapedBasedFromShape context.structs exceptionShape with
                              | none => staticError (.scope (getImplementationErrorMessage
                                  "static analysis failed to convert in-scope shape"
                                  context.location context.scope))
                              | some handlerShaped =>
                                  let handlerContext := { context with locals :=
                                    (handlerVariable, { shapedBased := handlerShaped }) :: context.locals }
                                  staticBind (checkProg handlerContext handlerProgram) (fun _ =>
                                    staticOk destinationResult))))))
  | .decCall name shape function arguments body =>
      staticBind (checkRedecVar context name) (fun _ =>
        staticBind (checkShape context.structs context.location context.scope shape) (fun _ =>
          staticBind (checkFunctionName context function) (fun functionInfo =>
            staticBind (checkCallArgs context arguments) (fun argumentResult =>
              staticBind (checkFuncArgs context function functionInfo.params
                  argumentResult.shapedBased) (fun _ =>
                if !shapesSame shape functionInfo.returnShape then
                  staticError (.shape (getShapeMismatchMessage
                    ("result of function call " ++ function ++
                      " to initialise local variable " ++ name)
                    (Shape.shapeToString functionInfo.returnShape)
                    (Shape.shapeToString shape)
                    context.location context.scope))
                else
                  match shapedBasedFromShape context.structs shape with
                  | none => staticError (.scope (getImplementationErrorMessage
                      "static analysis failed to convert in-scope shape"
                      context.location context.scope))
                  | some shaped =>
                      let nextContext := { context with
                        locals := (name, { shapedBased := shaped }) :: context.locals
                        last := .otherLast }
                      staticBind (checkProg nextContext body) (fun result =>
                        staticOk (removeLocalVariableDelta name result)))))))
  | .extCall function configuration configurationLength array arrayLength =>
      staticBind (checkCallArgs context
        [configuration, configurationLength, array, arrayLength])
        (fun argumentResult =>
          if argumentResult.shapedBased.all (shapedBasedHasShape .one) then
            progOk .otherLast false false context.location
          else
            staticError (.shape (getNonWordMessage
              ("value for argument given to FFI " ++ function)
              (match argumentResult.shapedBased.find? (fun shaped =>
                !shapedBasedHasShape .one shaped) with
              | some shaped => shapedBasedToString shaped
              | none => "")
              context.location context.scope)))
  | .raise exception value =>
      match lookupInfo exception context.exceptions with
      | none => staticError (.scope ("exception " ++ exception ++
          " is not declared\n"))
      | some shape =>
          staticBind (checkExp context value) (fun result =>
            if shapedBasedHasShape shape result.shapedBased then
              progOk .raiseLast true false context.location
            else staticError (.shape ("raised exception " ++ exception ++
              " has wrong value shape\n")))
  | .return value =>
      staticBind (checkExp context value) (fun result =>
        match context.scope with
        | .funScope functionName _ =>
            staticBind (checkFunctionName context functionName) (fun functionInfo =>
              if shapedBasedHasShape functionInfo.returnShape result.shapedBased then
                progOk .retLast true false context.location
              else
                staticError (.shape (getShapeMismatchMessage
                  "expression to return" (shapedBasedToString result.shapedBased)
                  (Shape.shapeToString functionInfo.returnShape)
                  context.location context.scope)))
        | _ =>
            staticError (.general (getImplementationErrorMessage
              "return found outside function scope" context.location context.scope)))
  | .shMemLoad _ varKind name address =>
      /- CakeML looks the destination up in locals only for `Local` and in
         globals only for `Global` (`panStaticScript.sml:1642,1676`). -/
      /- Cake checks the address before checking the destination shape.  This
         retains an address warning even when a later non-word destination
         error aborts the check (`panStaticScript.sml:1642-1706`). -/
      let checkAddress : StaticResult ExpReturn :=
        staticBind (checkExp context address) (fun result =>
          if shapedBasedHasShape .one result.shapedBased then
            staticAddWarning (staticOk result)
              (staticMemoryWarning context false true result.shapedBased)
          else
            staticError (.shape (getNonWordMessage "load address"
              (shapedBasedToString result.shapedBased)
              context.location context.scope)))
      match varKind with
      | .local =>
          staticBind (checkLocalVar context name) (fun info =>
            staticBind checkAddress (fun _ =>
              if !shapedBasedHasShape .one info.shapedBased then
                staticError (.shape (getNonWordMessage "load variable"
                  (shapedBasedToString info.shapedBased)
                  context.location context.scope))
              else
                staticOk {
                  exitsFunction := false
                  exitsLoop := false
                  last := .otherLast
                  variableDelta := localVariableDelta name info
                  currentLocation := context.location }))
      | .global =>
          staticBind (checkGlobalVar context name) (fun info =>
            staticBind checkAddress (fun _ =>
              if !shapesSame info.shape .one then
                staticError (.shape (getNonWordMessage "load variable"
                  (Shape.shapeToString info.shape)
                  context.location context.scope))
              else
                progOk .otherLast false false context.location))
  | .shMemStore _ address value =>
      staticBind (checkExp context address) (fun addressResult =>
        staticBind (checkExp context value) (fun valueResult =>
          if shapedBasedHasShape .one addressResult.shapedBased then
            let warning :=
              staticMemoryWarning context false false addressResult.shapedBased
            if shapedBasedHasShape .one valueResult.shapedBased then
              staticAddWarning (progOk .otherLast false false context.location)
                warning
            else
              staticAddWarning
                (staticError (.shape (getNonWordMessage "store value"
                  (shapedBasedToString valueResult.shapedBased)
                  context.location context.scope)))
                warning
          else
            staticError (.shape (getNonWordMessage "store address"
              (shapedBasedToString addressResult.shapedBased)
              context.location context.scope))))
  | .tick => progOk .otherLast false false context.location
  | .annot tag text =>
      let location := if tag == "location" then "AT " ++ text ++ ": " else context.location
      progOk .invisLast false false location
termination_by program => sizeOf program
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  checkCallArgs [BEq String] (context : Context) :
      List (Exp α) → StaticResult ExpsReturn
    | [] => staticOk { shapedBased := [] }
    | expression :: expressions =>
        staticBind (checkExp context expression) (fun result =>
          staticBind (checkCallArgs context expressions) (fun rest =>
            staticOk { shapedBased := result.shapedBased :: rest.shapedBased }))
  termination_by expressions => sizeOf expressions
    decreasing_by
      all_goals first | sizeOf_list_dec | decreasing_trivial

def firstRepeat [BEq α] : List α → Option α
  | value1 :: value2 :: values =>
      if value1 == value2 then some value1
      else firstRepeat (value2 :: values)
  | _ => none

/-! Source-shaped port of CakeML's `check_id_shapes_def`
    (`cakeml/pancake/panStaticScript.sml:776-797`).  Each identifier gets its
    identifier-specific scope before its shape is checked, which preserves the
    diagnostics for both function parameters and structure fields. -/
def checkIdShapes [BEq String] (context : StructContext) (location : String)
    (scope : Scope) : List (String × Shape) → StaticResult Unit
  | [] => staticOk ()
  | (name, shape) :: identifiers =>
      let scopedResult : StaticResult Scope :=
        match scope with
        | .funScope function _ =>
            staticOk (.funScope function (" parameter " ++ name))
        | .structScope structName _ =>
            staticOk (.structScope structName name)
        | _ =>
            staticError (.general (getImplementationErrorMessage
              "parameter or field found in unexpected scope" location scope))
      staticBind scopedResult (fun scopedShape =>
        staticBind (checkShape context location scopedShape shape) (fun _ =>
          checkIdShapes context location scope identifiers))
termination_by identifiers => sizeOf identifiers
decreasing_by
  all_goals decreasing_trivial

def checkShapeFields [BEq String] (context : StructContext)
    (fields : List (FieldName × Shape)) : StaticResult Unit :=
  if isWfFields context fields then
    staticOk ()
  else
    staticError (.scope "structure field has an unknown or invalid shape")

def localInfosFromParams [BEq String] (context : StructContext) :
    List (VarName × Shape) → InfoMap LocalInfo
  | [] => []
  | (name, shape) :: params =>
      let shaped := (shapedBasedFromShape context shape).getD (.word .trusted)
      (name, { shapedBased := shaped }) :: localInfosFromParams context params

structure StaticDeclContext where
  functions : InfoMap FuncInfo
  globals : InfoMap GlobalInfo
  exceptions : InfoMap Shape
  deriving Repr

def staticCheckNames [BEq String] (context : StructContext) :
    List (Decl α) → StaticResult StructContext
  | [] => staticOk context
  | .name name fields :: declarations =>
      if (lookupInfo name context).isSome then
        staticError (.scope (getRedecMessage .struct "" name .topLevel))
      else
        -- CakeML sorts (`panStaticScript.sml:578-585`) so `first_repeat`
        -- reports the lexicographically smallest duplicate.
        match firstRepeat ((fields.map Prod.fst).mergeSort (· ≤ ·)) with
        | some field =>
            staticError (.scope ("field " ++ field ++
              " is redeclared in struct name " ++ name ++ "\n"))
        | none =>
            staticBind (checkIdShapes context "" (.structScope name "") fields) (fun _ =>
              let shapedFields :=
                fields.map (fun (fieldName, shape) =>
                  (fieldName, (shapedBasedFromShape context shape).getD (.word .trusted)))
              let info : StructInfo :=
                { fields := fields
                  size := shapeSizeWithContext context (.comb (fields.map Prod.snd))
                  shapedFields := shapedFields }
              staticBind (staticCheckNames ((name, info) :: context) declarations)
                (fun result => staticOk result))
  | _ :: declarations => staticCheckNames context declarations
termination_by declarations => sizeOf declarations

/-! Source-shaped port of CakeML's `check_export_params_def`
    (`cakeml/pancake/panStaticScript.sml:649-658`).  Exported parameters are
    required to have exactly the scalar `One` shape, and Cake reports the
    offending parameter's name and shape. -/
def checkExportParams (location : String) (scope : Scope) :
    List (VarName × Shape) → StaticResult Unit
  | [] => staticOk ()
  | (name, shape) :: params =>
      if shapesSame shape .one then
        checkExportParams location scope params
      else
        staticError (.shape (getNonWordMessage
          ("exported function parameter " ++ name)
          (Shape.shapeToString shape) location scope))

def staticCheckFunctionHeader [BEq String] (context : StructContext)
    (declaration : FunDecl α) : StaticResult Unit :=
  if declaration.name = "main" then
    if !declaration.params.isEmpty then
      staticError (.general "main function has arguments\n")
    else if declaration.exported then
      staticError (.general "main function is exported\n")
    else if !shapesSame declaration.returnShape .one then
      staticError (.shape (getNonWordMessage "main function return"
        (Shape.shapeToString declaration.returnShape) ""
        (.funScope declaration.name "")))
    else
      staticOk ()
  else
    match firstRepeat ((declaration.params.map Prod.fst).mergeSort (· ≤ ·)) with
    | some parameter =>
        staticError (.scope ("parameter " ++ parameter ++
          " is redeclared in function " ++ declaration.name ++ "\n"))
    | none =>
      if declaration.exported && declaration.params.length > 4 then
        staticError (.general ("exported function " ++ declaration.name ++
          " has more than 4 arguments\n"))
      else if declaration.exported then
        staticBind (checkExportParams "" (.funScope declaration.name "") declaration.params)
          (fun _ =>
            if !shapesSame declaration.returnShape .one then
              staticError (.shape (getNonWordMessage "exported function return"
                (Shape.shapeToString declaration.returnShape) ""
                (.funScope declaration.name "")))
            else staticOk ())
      else
        staticBind (checkIdShapes context "" (.funScope declaration.name "")
          declaration.params) (fun _ =>
          staticBind (checkShape context ""
            (.funScope declaration.name " return") declaration.returnShape) (fun _ =>
            if shapeSizeWithContext context declaration.returnShape > 32 then
              staticError (.shape ("function " ++ declaration.name ++
                " returns a shape bigger than 32 words\n"))
            else
              staticOk ()))

def staticCheckDecls [BEq String] (structs : StructContext) :
    StaticDeclContext → List (Decl α) → StaticResult StaticDeclContext
  | context, [] => staticOk context
  | context, .name _ _ :: declarations =>
      staticCheckDecls structs context declarations
  | context, .exnDecl exception shape :: declarations =>
      if (lookupInfo exception context.exceptions).isSome then
        staticError (.scope ("exception " ++ exception ++ " is redeclared\n"))
      else
        /- CakeML only checks for redeclaration here; the exception shape
           itself is not validated (`panStaticScript.sml:1858-1868`). -/
        staticCheckDecls structs
          { context with exceptions := (exception, shape) :: context.exceptions }
          declarations
  | context, .decl shape name value :: declarations =>
      let checkingContext : Context :=
        { locals := []
          globals := context.globals
          functions := []
          expectedReturn := none
          exceptions := context.exceptions
          structs := structs
          scope := .declScope name
          inLoop := false
          reachable := .isReach
          last := .invisLast
          location := "" }
      staticBind (checkRedecVar { checkingContext with scope := .topLevel } name) (fun _ =>
        staticBind (checkShape structs "" (.declScope name) shape) (fun _ =>
          staticBind (checkExp checkingContext value) (fun result =>
            if shapedBasedMatchesShape structs shape result.shapedBased then
              staticCheckDecls structs
                { context with globals := (name, { shape := shape }) :: context.globals }
                declarations
            else
              staticError (.shape (getShapeMismatchMessage
                ("expression to initialise global variable " ++ name)
                (shapedBasedToString result.shapedBased)
                (Shape.shapeToString shape) "" (.declScope name))))))
  | context, .function declaration :: declarations =>
      if (lookupInfo declaration.name context.functions).isSome then
        staticError (.scope (getRedecMessage .function "" declaration.name .topLevel))
      else
        staticBind (staticCheckFunctionHeader structs declaration) (fun _ =>
          staticCheckDecls structs
            { context with functions :=
                (declaration.name,
                  { returnShape := declaration.returnShape
                    params := declaration.params }) :: context.functions }
            declarations)
termination_by _ declarations => declarations.length
decreasing_by
  all_goals decreasing_trivial

def staticCheckProgs [BEq String] (structs : StructContext)
    (context : StaticDeclContext) : List (Decl α) → StaticResult Unit
  | [] => staticOk ()
  | .function declaration :: declarations =>
      let rec addParams : List (VarName × Shape) → StaticResult (InfoMap LocalInfo)
        | [] => staticOk []
        | (name, shape) :: params =>
            match shapedBasedFromShape structs shape with
            | none => staticError (.scope (getImplementationErrorMessage
                "static analysis failed to convert in-scope shape" ""
                (.funScope declaration.name "")))
            | some shaped =>
                staticBind (addParams params) (fun rest =>
                  staticOk ((name, { shapedBased := shaped }) :: rest))
      staticBind (addParams declaration.params) (fun locals =>
        let checkingContext : Context :=
          { locals := locals
            globals := context.globals
            functions := context.functions
            expectedReturn := some declaration.returnShape
            exceptions := context.exceptions
            structs := structs
            scope := .funScope declaration.name ""
            inLoop := false
            reachable := .isReach
            last := .invisLast
            location := "" }
        staticBind (checkProg checkingContext declaration.body) (fun result =>
          if result.exitsFunction then
            staticCheckProgs structs context declarations
          else
            staticError (.general ("branches missing return statement in " ++
              staticScopeDescription (.funScope declaration.name "") ++ "\n"))))
  | _ :: declarations => staticCheckProgs structs context declarations
termination_by declarations => declarations.length

def staticCheck [BEq String] (declarations : List (Decl α)) : StaticResult Unit :=
  staticBind (staticCheckNames (α := α) [] declarations) (fun structs =>
    staticBind (staticCheckDecls structs
      { functions := [], globals := [], exceptions := [] } declarations)
      (fun context => staticCheckProgs structs context declarations))

end Flapjack
