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

structure PanSemState (α : Type u) (ffi : Type v) where
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  structs : StructContext
  code : FunName → Option (List (VarName × Shape) × Prog α × Shape)
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
  code : FunName → Option (List (VarName × Shape) × Prog α × Shape)
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
