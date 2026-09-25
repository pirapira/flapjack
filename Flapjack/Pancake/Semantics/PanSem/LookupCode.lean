import Flapjack.Pancake.Semantics.PanSem

/-!
# Exact PanSem `lookup_code`

This module ports `panSem$lookup_code_def` from
`cakeml/pancake/semantics/panSemScript.sml:458-467`. The tagged definition uses
the width-indexed HOL value carrier and the same finite-map interface as the
source. `lookupPanSemStateCodeHOL` adapts the finite-support production
`PanSemState.code` through its extensional lookup view.
-/

namespace Flapjack

/-- Recursive HOL `LIST_REL` counterpart for `lookup_code`'s formal/argument
    shape test. -/
def panSemLookupCodeShapeRel {width : Nat} [NeZero width] [LawfulBEq String] :
    List (VarName × Shape) → List (HolValue width) → Bool
  | [], [] => true
  | parameter :: parameters, argument :: arguments =>
      panShapeMatches parameter.2 (panSemShapeOf argument.toPanValue) &&
        panSemLookupCodeShapeRel parameters arguments
  | _, _ => false

/-- Statement-shaped HOL `lookup_code` validity for its formal-name list and
    argument shapes. `panSemLookupCodeShapeRel` is the recursive HOL
    `LIST_REL`; `holShapeOf` is the width-indexed `shape_of` port. -/
def panSemLookupCodeArgumentsValid {width : Nat} [NeZero width] [LawfulBEq String]
    (parameters : List (VarName × Shape)) (arguments : List (HolValue width)) : Bool :=
  decide (parameters.map Prod.fst).Nodup &&
    panSemLookupCodeShapeRel parameters arguments

/-- Exact width-indexed port of HOL `panSem$lookup_code_def` over the finite
    map view. It rejects duplicate formal names or any argument list that does
    not satisfy HOL's pointwise `shape_of` relation, and on success returns the
    body, `FEMPTY |++ ZIP (MAP FST vshapes,args)`, and declared return shape. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "lookup_code_def"]
def panSemLookupCodeHOL {width : Nat} [NeZero width]
    [LawfulBEq String] (code : FiniteMap FunName
      (List (VarName × Shape) × Prog (BitVec width) × Shape))
    (function : FunName) (arguments : List (HolValue width)) :
    Option (Prog (BitVec width) × FiniteMap VarName (HolValue width) × Shape) :=
  match FLOOKUP code function with
  | none => none
  | some (parameters, body, returnShape) =>
      if panSemLookupCodeArgumentsValid parameters arguments then
        some (body,
          FUPDATE_LIST FEMPTY ((parameters.map Prod.fst).zip arguments),
          returnShape)
      else none

/-- Apply the exact `lookup_code` port to the finite-support code map owned by
    a production source state. Arguments are converted to the exact HOL `v`
    carrier before the tagged lookup is called. -/
def panSemLookupStateCodeHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemState (BitVec width) ffi) (function : FunName)
    (arguments : List (PanValue (BitVec width))) :
    Option (Prog (BitVec width) × FiniteMap VarName (HolValue width) × Shape) :=
  panSemLookupCodeHOL (panSemCodeAsLookup state.code) function
    (arguments.map PanValue.toHolValue)

/-- The exact HOL argument-shape relation is the state evaluator's recursive
    shape check rendered through the `PanValue`/`HolValue` isomorphism. -/
theorem panSemCodeArgumentsMatch_eq_holLookupValidity {width : Nat}
    [NeZero width] [LawfulBEq String]
    (structs : StructContext) (parameters : List (VarName × Shape))
    (arguments : List (PanValue (BitVec width))) :
    panSemCodeArgumentsMatch structs parameters arguments =
      panSemLookupCodeShapeRel parameters (arguments.map PanValue.toHolValue) := by
  induction parameters generalizing arguments with
  | nil => cases arguments <;> rfl
  | cons parameter parameters ih =>
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          simp only [panSemCodeArgumentsMatch, panSemLookupCodeShapeRel,
            List.map_cons, ih arguments]
          have hhead :
            panShapeMatches (panValueShape structs argument) parameter.2 =
                panShapeMatches parameter.2
                  (panSemShapeOf argument.toHolValue.toPanValue) := by
            rw [panShapeMatches_comm, panValueShape_eq_panSemShapeOf_tagged]
            rw [PanValue.toHolValue_toPanValue]
          rw [hhead]

/-- A successful HOL `LIST_REL` pairs every formal with one argument, so the
    state evaluator's length-checked local binder cannot reject that same list. -/
theorem panSemLookupCodeShapeRel_length {width : Nat} [NeZero width]
    [LawfulBEq String] (parameters : List (VarName × Shape))
    (arguments : List (HolValue width))
    (hmatch : panSemLookupCodeShapeRel parameters arguments = true) :
    parameters.length = arguments.length := by
  induction parameters generalizing arguments with
  | nil =>
      cases arguments with
      | nil => rfl
      | cons argument arguments => simp [panSemLookupCodeShapeRel] at hmatch
  | cons parameter parameters ih =>
      cases arguments with
      | nil => simp [panSemLookupCodeShapeRel] at hmatch
      | cons argument arguments =>
          have htail : panSemLookupCodeShapeRel parameters arguments = true := by
            have hstep :
                panShapeMatches parameter.2 (panSemShapeOf argument.toPanValue) &&
                  panSemLookupCodeShapeRel parameters arguments = true := by
              simpa [panSemLookupCodeShapeRel] using hmatch
            cases hhead : panShapeMatches parameter.2 (panSemShapeOf argument.toPanValue) with
            | false => simp [hhead] at hstep
            | true => simpa [hhead] using hstep
          simp [ih arguments htail]

/-- Folding production parameter bindings and then converting each looked-up
    value to the HOL carrier is extensionally the same operation as HOL's
    `FUPDATE_LIST` over the converted entries. This is the result-side bridge
    needed to relate a successful `lookup_code`, not only its success bit. -/
private theorem foldlUpdatePanMap_eq_FUPDATE_LIST_toHol {width : Nat}
    [LawfulBEq String]
    (entries : List (VarName × PanValue (BitVec width))) :
    ∀ (locals : VarName → Option (PanValue (BitVec width)))
      (holLocals : FiniteMap VarName (HolValue width)),
      (∀ name, locals name = (FLOOKUP holLocals name).map HolValue.toPanValue) →
      ∀ name,
        entries.foldl
            (fun current (binding : VarName × PanValue (BitVec width)) =>
              updatePanValueMap current binding.1 binding.2)
            locals name =
          (FLOOKUP (FUPDATE_LIST holLocals
            (entries.map fun binding => (binding.1, binding.2.toHolValue))) name).map
              HolValue.toPanValue := by
  induction entries with
  | nil =>
      intro locals holLocals hrel name
      simpa [FUPDATE_LIST] using hrel name
  | cons entry entries ih =>
      intro locals holLocals hrel name
      have hrel' : ∀ key,
          updatePanValueMap locals entry.1 entry.2 key =
            (FLOOKUP (FUPDATE holLocals (entry.1, entry.2.toHolValue)) key).map
              HolValue.toPanValue := by
        intro key
        by_cases heq : key == entry.1
        · have hkey : key = entry.1 := beq_iff_eq.mp heq
          subst key
          simp [FLOOKUP, FUPDATE, updatePanValueMap,
            PanValue.toHolValue_toPanValue]
        · have hne : ¬ (entry.1 == key) := by
            intro hreverse
            have hEq : entry.1 = key := beq_iff_eq.mp hreverse
            have hforward : (key == entry.1) = true :=
              beq_iff_eq.mpr hEq.symm
            simp [hforward] at heq
          have hreverse : (entry.1 == key) = false := by
            cases hbeq : entry.1 == key with
            | false => rfl
            | true => exact absurd hbeq hne
          simp [FLOOKUP, FUPDATE, updatePanValueMap, heq, hreverse, hrel key]
      simpa [List.foldl_cons, FUPDATE_LIST_cons, List.map_cons] using
        (ih (updatePanValueMap locals entry.1 entry.2)
          (FUPDATE holLocals (entry.1, entry.2.toHolValue)) hrel' name)

/-- For equal-length parameter and argument lists, the production fresh-local
    binder agrees pointwise with the exact HOL `FEMPTY |++ ZIP` map after the
    `PanValue`/`HolValue` isomorphism. -/
theorem bindPanValueParameters_eq_holFupdateList {width : Nat}
    [LawfulBEq String]
    (parameters : List VarName) (arguments : List (PanValue (BitVec width)))
    (hlen : parameters.length = arguments.length) :
    bindPanValueParameters parameters arguments =
      some (fun name =>
        (FLOOKUP (FUPDATE_LIST (FEMPTY : FiniteMap VarName (HolValue width))
          (parameters.zip (arguments.map PanValue.toHolValue))) name).map
            HolValue.toPanValue) := by
  unfold bindPanValueParameters
  simp [hlen]
  have hzip :
      (parameters.zip arguments).map
          (fun binding => (binding.1, binding.2.toHolValue)) =
        parameters.zip (arguments.map PanValue.toHolValue) := by
    induction parameters generalizing arguments with
    | nil =>
        cases arguments with
        | nil => rfl
        | cons _ _ => simp at hlen
    | cons parameter parameters ih =>
        cases arguments with
        | nil => simp at hlen
        | cons argument arguments =>
            simp only [List.zip_cons_cons, List.map_cons]
            congr 1
            exact ih arguments (Nat.succ.inj hlen)
  funext name
  have hfold := foldlUpdatePanMap_eq_FUPDATE_LIST_toHol
    (parameters.zip arguments) (fun _ => none) FEMPTY (by intro key; rfl) name
  simpa [hzip] using hfold

/-- A valid production state-code entry has the same body, return shape, and
    freshly bound locals as the exact HOL `lookup_code` result. This bridges
    the complete successful lookup result; `lookup_code` itself retains its
    original HOL signature and does not depend on production lookup inputs. -/
theorem panSemLookupStateCodeHOL_matches_production_entry {width : Nat}
    [NeZero width] [LawfulBEq String]
    (state : PanSemState (BitVec width) ffi) (function : FunName)
    (arguments : List (PanValue (BitVec width)))
    (parameters : List (VarName × Shape)) (body : Prog (BitVec width))
    (returnShape : Shape)
    (hentry : panSemCodeLookup state.code function =
      some (parameters, body, returnShape))
    (hnames : (parameters.map Prod.fst).Nodup)
    (hshape : panSemCodeArgumentsMatch state.structs parameters arguments = true) :
    ∃ (holLocals : FiniteMap VarName (HolValue width))
      (productionLocals : VarName → Option (PanValue (BitVec width))),
      panSemLookupStateCodeHOL state function arguments =
        some (body, holLocals, returnShape) ∧
      lookupPanSemCodeCall state.structs state.code function arguments =
        some (body, returnShape, productionLocals) ∧
      ∀ name, productionLocals name =
        (FLOOKUP holLocals name).map HolValue.toPanValue := by
  have hshapeHOL : panSemLookupCodeShapeRel parameters
      (arguments.map PanValue.toHolValue) = true := by
    rw [← panSemCodeArgumentsMatch_eq_holLookupValidity]
    exact hshape
  have hlength := panSemLookupCodeShapeRel_length parameters
    (arguments.map PanValue.toHolValue) hshapeHOL
  have hnamesBool : decide (parameters.map Prod.fst).Nodup = true := by
    simp [hnames]
  have hvalid : panSemLookupCodeArgumentsValid parameters
      (arguments.map PanValue.toHolValue) = true := by
    unfold panSemLookupCodeArgumentsValid
    rw [hnamesBool, hshapeHOL]
    rfl
  let holLocals : FiniteMap VarName (HolValue width) :=
    FUPDATE_LIST FEMPTY
      ((parameters.map Prod.fst).zip (arguments.map PanValue.toHolValue))
  let productionLocals : VarName → Option (PanValue (BitVec width)) :=
    fun name => (FLOOKUP holLocals name).map HolValue.toPanValue
  have hparametersLength : (parameters.map Prod.fst).length = arguments.length := by
    calc
      (parameters.map Prod.fst).length = parameters.length := by simp
      _ = (arguments.map PanValue.toHolValue).length := hlength
      _ = arguments.length := by simp
  have hbind : bindPanValueParameters (parameters.map Prod.fst) arguments =
      some productionLocals := by
    simpa [productionLocals, holLocals] using
      (bindPanValueParameters_eq_holFupdateList
        (parameters.map Prod.fst) arguments hparametersLength)
  have hholLookup : panSemLookupStateCodeHOL state function arguments =
      some (body, holLocals, returnShape) := by
    unfold panSemLookupStateCodeHOL panSemLookupCodeHOL
    simp [FLOOKUP, panSemCodeAsLookup, hentry,
      panSemLookupCodeArgumentsValid, hnamesBool, hshapeHOL, holLocals]
  have hproductionLookup : lookupPanSemCodeCall state.structs state.code
      function arguments = some (body, returnShape, productionLocals) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [hnames, hshape, hbind]
  exact ⟨holLocals, productionLocals, hholLookup, hproductionLookup, fun _ => rfl⟩

/-- The state-owned wrapper is definitionally the tagged lookup over exactly
    the finite `state.code` support view; this bridge does not introduce a
    detached function table. -/
theorem panSemLookupStateCodeHOL_eq_lookupView {width : Nat} [NeZero width]
    [LawfulBEq String] (state : PanSemState (BitVec width) ffi)
    (function : FunName) (arguments : List (PanValue (BitVec width))) :
    panSemLookupStateCodeHOL state function arguments =
      panSemLookupCodeHOL (panSemCodeAsLookup state.code) function
        (arguments.map PanValue.toHolValue) := rfl

/-- Exact and production state-code lookups agree on whether a call can be
    entered. This boundary covers the shared `FLOOKUP`, duplicate-name guard,
    parameter/argument shape relation, and the production binder's length
    check; payload representation conversion is kept explicit in each result. -/
theorem panSemLookupStateCodeHOL_isSome_iff_production {width : Nat} [NeZero width]
    [LawfulBEq String] (state : PanSemState (BitVec width) ffi)
    (function : FunName) (arguments : List (PanValue (BitVec width))) :
    (panSemLookupStateCodeHOL state function arguments).isSome =
      (lookupPanSemCodeCall state.structs state.code function arguments).isSome := by
  unfold panSemLookupStateCodeHOL lookupPanSemCodeCall
  cases hlookup : panSemCodeLookup state.code function with
  | none =>
      change lookupInfo function state.code = none at hlookup
      simp [FLOOKUP, panSemCodeAsLookup, panSemCodeLookup,
        panSemLookupCodeHOL, hlookup]
  | some entry =>
      rcases entry with ⟨parameters, body, returnShape⟩
      change lookupInfo function state.code =
        some (parameters, body, returnShape) at hlookup
      have hargumentMatch := panSemCodeArgumentsMatch_eq_holLookupValidity
        state.structs parameters arguments
      by_cases hnames : (parameters.map Prod.fst).Nodup
      · cases hshape : panSemLookupCodeShapeRel parameters
            (arguments.map PanValue.toHolValue) with
        | false =>
            simp [FLOOKUP, panSemCodeAsLookup, panSemCodeLookup, panSemLookupCodeHOL,
              panSemLookupCodeArgumentsValid, hlookup,
              hnames, hshape, hargumentMatch]
        | true =>
            have hlength := panSemLookupCodeShapeRel_length parameters
              (arguments.map PanValue.toHolValue) hshape
            simp [FLOOKUP, panSemCodeAsLookup, panSemCodeLookup, panSemLookupCodeHOL,
              panSemLookupCodeArgumentsValid, hlookup,
              hnames, hshape, hargumentMatch, bindPanValueParameters,
              hlength]
      · simp [FLOOKUP, panSemCodeAsLookup, panSemCodeLookup, panSemLookupCodeHOL,
          panSemLookupCodeArgumentsValid, hlookup, hnames]

end Flapjack
