import Flapjack.PanValues

/-!
# Pancake `bst`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:692-708`.

`bst_def` projects the ordinary Pancake state into the `bstate` consumed by
the interaction-tree semantics.  Every semantic field is copied exactly;
the source clock and FFI state are deliberately absent from the projection.
-/

namespace Flapjack

/-- Finite, state-owned representation of Cake's `state.code` finite map.
    `lookupInfo` is the observable HOL `FLOOKUP`; storing entries here, rather
    than accepting an arbitrary function, makes the support available for
    recursive source evaluation. -/
abbrev PanSemCodeMap (α : Type u) :=
  InfoMap (List (VarName × Shape) × Prog α × Shape)

/-- HOL `FLOOKUP` view of the finite source code entries. -/
def panSemCodeLookup [BEq String] (code : PanSemCodeMap α) (name : FunName) :=
  lookupInfo name code

/-- Function view used where existing HOL relations are stated over
    `FLOOKUP` functions. The entries remain the authoritative finite map. -/
def panSemCodeAsLookup [BEq String] (code : PanSemCodeMap α) :
    FunName → Option (List (VarName × Shape) × Prog α × Shape) :=
  fun name => panSemCodeLookup code name

@[simp] theorem panSemCodeAsLookup_apply [BEq String]
    (code : PanSemCodeMap α) (name : FunName) :
    panSemCodeAsLookup code name = lookupInfo name code := rfl

/-- Every present code binding is supported by a key stored in the state. -/
theorem panSemCodeLookup_mem_support [BEq String] [LawfulBEq String]
    (code : PanSemCodeMap α) (name : FunName)
    (hlookup : panSemCodeLookup code name ≠ none) :
    name ∈ code.map Prod.fst := by
  induction code with
  | nil => simp [panSemCodeLookup, lookupInfo] at hlookup
  | cons entry entries ih =>
      rcases entry with ⟨candidate, value⟩
      by_cases hname : candidate == name
      · have hkey : candidate = name := beq_iff_eq.mp hname
        subst name
        simp
      · have htail : lookupInfo name entries ≠ none := by
          simpa [panSemCodeLookup, lookupInfo, hname] using hlookup
        have hmem := ih htail
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr hmem

/-- A successful state-code lookup is backed by the corresponding stored
    association. This connects the observable first-match lookup to the finite
    support used for recursive fuel bounds. -/
theorem panSemCodeLookup_mem_binding [BEq String] [LawfulBEq String]
    (code : PanSemCodeMap α) (name : FunName)
    (value : List (VarName × Shape) × Prog α × Shape)
    (hlookup : panSemCodeLookup code name = some value) :
    (name, value) ∈ code := by
  induction code with
  | nil => simp [panSemCodeLookup, lookupInfo] at hlookup
  | cons entry entries ih =>
      rcases entry with ⟨candidate, stored⟩
      by_cases hname : candidate == name
      · have hkey : candidate = name := beq_iff_eq.mp hname
        have hstored : stored = value := by
          simpa [panSemCodeLookup, lookupInfo, hname] using hlookup
        subst candidate
        subst stored
        simp
      · have htail : panSemCodeLookup entries name = some value := by
          simpa [panSemCodeLookup, lookupInfo, hname] using hlookup
        have hmem := ih htail
        simp only [List.mem_cons]
        exact Or.inr hmem

/-! `panSemCodeUpdate` is the finite-support counterpart of Cake `FUPDATE`:
    it removes old occurrences and stores the updated binding at the head. -/
def panSemCodeUpdate [BEq String] (code : PanSemCodeMap α)
    (name : FunName) (entry : List (VarName × Shape) × Prog α × Shape) :
    PanSemCodeMap α :=
  (name, entry) :: code.filter (fun binding => !(binding.1 == name))

@[simp] theorem panSemCodeLookup_update [BEq String] [LawfulBEq String]
    (code : PanSemCodeMap α) (name : FunName)
    (entry : List (VarName × Shape) × Prog α × Shape) :
    panSemCodeLookup (panSemCodeUpdate code name entry) name = some entry := by
  simp [panSemCodeLookup, panSemCodeUpdate, lookupInfo]

/-- HOL `lookup_code` argument-shape check over the finite state code map. -/
def panSemCodeArgumentsMatch :
    StructContext → List (VarName × Shape) → List (PanValue α) → Bool
  | _, [], [] => true
  | structs, (_, shape) :: parameters, value :: values =>
      panShapeMatches (panValueShape structs value) shape &&
        panSemCodeArgumentsMatch structs parameters values
  | _, _, _ => false

/-- State-owned counterpart of HOL `lookup_code`: require distinct formal
    names and shape-matched arguments, then build the fresh callee locals from
    the same finite-map entry that supplies the body and return shape. -/
def lookupPanSemCodeCall [BEq String] (structs : StructContext)
    (code : PanSemCodeMap α)
    (function : FunName) (values : List (PanValue α)) :
    Option (Prog α × Shape × (VarName → Option (PanValue α))) := do
  let (parameters, body, returnShape) ← panSemCodeLookup code function
  if decide (parameters.map Prod.fst).Nodup &&
      panSemCodeArgumentsMatch structs parameters values then
    let locals ← bindPanValueParameters (parameters.map Prod.fst) values
    pure (body, returnShape, locals)
  else none

structure PanSemState (α : Type u) (ffi : Type v) where
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  structs : StructContext
  code : PanSemCodeMap α
  exceptionShapes : ExceptionId → Option Shape
  memory : α → Option (PanValue α)
  memaddrs : α → Bool
  sharedMemaddrs : α → Bool
  clock : Nat
  be : Bool
  ffi : ffi
  baseAddress : α
  topAddress : α

structure PanBState (α : Type u) where
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  structs : StructContext
  code : PanSemCodeMap α
  exceptionShapes : ExceptionId → Option Shape
  memory : α → Option (PanValue α)
  memaddrs : α → Bool
  sharedMemaddrs : α → Bool
  be : Bool
  baseAddress : α
  topAddress : α

def panBst (state : PanSemState α ffi) : PanBState α where
  locals := state.locals
  globals := state.globals
  structs := state.structs
  code := state.code
  exceptionShapes := state.exceptionShapes
  memory := state.memory
  memaddrs := state.memaddrs
  sharedMemaddrs := state.sharedMemaddrs
  be := state.be
  baseAddress := state.baseAddress
  topAddress := state.topAddress

@[simp] theorem panBst_locals (state : PanSemState α ffi) :
    (panBst state).locals = state.locals := by rfl

@[simp] theorem panBst_globals (state : PanSemState α ffi) :
    (panBst state).globals = state.globals := by rfl

@[simp] theorem panBst_structs (state : PanSemState α ffi) :
    (panBst state).structs = state.structs := by rfl

@[simp] theorem panBst_code (state : PanSemState α ffi) :
    (panBst state).code = state.code := by rfl

@[simp] theorem panBst_exceptionShapes (state : PanSemState α ffi) :
    (panBst state).exceptionShapes = state.exceptionShapes := by rfl

@[simp] theorem panBst_memory (state : PanSemState α ffi) :
    (panBst state).memory = state.memory := by rfl

@[simp] theorem panBst_memaddrs (state : PanSemState α ffi) :
    (panBst state).memaddrs = state.memaddrs := by rfl

@[simp] theorem panBst_sharedMemaddrs (state : PanSemState α ffi) :
    (panBst state).sharedMemaddrs = state.sharedMemaddrs := by rfl

@[simp] theorem panBst_be (state : PanSemState α ffi) :
    (panBst state).be = state.be := by rfl

@[simp] theorem panBst_baseAddress (state : PanSemState α ffi) :
    (panBst state).baseAddress = state.baseAddress := by rfl

@[simp] theorem panBst_topAddress (state : PanSemState α ffi) :
    (panBst state).topAddress = state.topAddress := by rfl

theorem panBst_clock_irrel (state : PanSemState α ffi) (clock : Nat) :
    panBst { state with clock := clock } = panBst state := by
  rfl

theorem panBst_ffi_irrel (state : PanSemState α ffi) (value : ffi) :
    panBst { state with ffi := value } = panBst state := by
  rfl

end Flapjack
