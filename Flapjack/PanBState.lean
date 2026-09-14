import Flapjack.PanValues
import Flapjack.Ffi

/-!
# Pancake `bst_def`

Source reference: `cakeml/pancake/semantics/pan_itreeSemScript.sml:692-705`.

`panSem.state` carries the clock and FFI state used by the clocked evaluator.
The interaction-tree semantics keeps the same source components but removes
those two fields.  This record mirrors CakeML's `bstate`; in particular, code
entries retain parameter shapes, bodies, and return shapes, while memory and
the two address domains remain explicit.
-/

namespace Flapjack

abbrev PanFunctionCode (α : Type u) :=
  (List (VarName × Shape) × Prog α × Shape)

structure PanBState (α : Type u) where
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  structs : StructContext
  code : InfoMap (PanFunctionCode α)
  eshapes : InfoMap Shape
  memory : α → PanWordLab α
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  be : Bool
  baseAddress : α
  topAddress : α

structure PanState (α : Type u) (σ : Type v) where
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  structs : StructContext
  code : InfoMap (PanFunctionCode α)
  eshapes : InfoMap Shape
  memory : α → PanWordLab α
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  clock : Nat
  be : Bool
  ffi : FfiState σ
  baseAddress : α
  topAddress : α

def panBst (state : PanState α σ) : PanBState α :=
  { locals := state.locals
    globals := state.globals
    structs := state.structs
    code := state.code
    eshapes := state.eshapes
    memory := state.memory
    memaddrs := state.memaddrs
    shMemaddrs := state.shMemaddrs
    be := state.be
    baseAddress := state.baseAddress
    topAddress := state.topAddress }

@[simp] theorem panBst_locals (state : PanState α σ) :
    (panBst state).locals = state.locals := by rfl

@[simp] theorem panBst_globals (state : PanState α σ) :
    (panBst state).globals = state.globals := by rfl

@[simp] theorem panBst_structs (state : PanState α σ) :
    (panBst state).structs = state.structs := by rfl

@[simp] theorem panBst_code (state : PanState α σ) :
    (panBst state).code = state.code := by rfl

@[simp] theorem panBst_eshapes (state : PanState α σ) :
    (panBst state).eshapes = state.eshapes := by rfl

@[simp] theorem panBst_memory (state : PanState α σ) :
    (panBst state).memory = state.memory := by rfl

@[simp] theorem panBst_memaddrs (state : PanState α σ) :
    (panBst state).memaddrs = state.memaddrs := by rfl

@[simp] theorem panBst_shMemaddrs (state : PanState α σ) :
    (panBst state).shMemaddrs = state.shMemaddrs := by rfl

@[simp] theorem panBst_be (state : PanState α σ) :
    (panBst state).be = state.be := by rfl

@[simp] theorem panBst_baseAddress (state : PanState α σ) :
    (panBst state).baseAddress = state.baseAddress := by rfl

@[simp] theorem panBst_topAddress (state : PanState α σ) :
    (panBst state).topAddress = state.topAddress := by rfl

end Flapjack
