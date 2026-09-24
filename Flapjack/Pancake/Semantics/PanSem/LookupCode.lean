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
