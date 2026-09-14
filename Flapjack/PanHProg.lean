import Flapjack.PanHProgStore

/-!
# Pancake `h_prog`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:555-577`.

`h_prog_def` is the source dispatcher: terminal program forms return a
`Ret` immediately, while every computation-bearing form delegates to its
corresponding `h_prog_*` definition.  The child definitions have separate
source-port beads, so this boundary keeps those computations explicit as
handlers rather than replacing them with an approximate evaluator.  The
handler result carries the source state, matching Pancake's `(result,s)`
return convention.
-/

namespace Flapjack

inductive PanHProgResult (σ : Type u) where
  | normal (sourceState : σ)
  | break (sourceState : σ)
  | continue (sourceState : σ)
  | error (sourceState : σ)
  | finalFfi (sourceState : σ) (event : FfiFinalEvent)
  deriving Repr

abbrev PanHProgTree (σ : Type u) := PanFfiTree (PanHProgResult σ)

structure PanHProgHandlers (α : Type u) (σ : Type v) where
  dec : VarName → Shape → Exp α → Prog α → σ → PanHProgTree σ
  assign : VarKind → VarName → Exp α → σ → PanHProgTree σ
  primitive : VarName → PrimOp → List (Exp α) → σ → PanHProgTree σ
  store : Exp α → Exp α → σ → PanHProgTree σ
  store32 : Exp α → Exp α → σ → PanHProgTree σ
  storeByte : Exp α → Exp α → σ → PanHProgTree σ
  shMemLoad : OpSize → VarKind → VarName → Exp α → σ → PanHProgTree σ
  shMemStore : OpSize → Exp α → Exp α → σ → PanHProgTree σ
  seq : Prog α → Prog α → σ → PanHProgTree σ
  cond : Exp α → Prog α → Prog α → σ → PanHProgTree σ
  whileProg : Exp α → Prog α → σ → PanHProgTree σ
  callProg : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
      σ → PanHProgTree σ
  decCallProg : VarName → Shape → FunName → List (Exp α) → Prog α → σ → PanHProgTree σ
  extCallProg : FunName → Exp α → Exp α → Exp α → Exp α → σ → PanHProgTree σ
  raiseProg : ExceptionId → Exp α → σ → PanHProgTree σ
  returnProg : Exp α → σ → PanHProgTree σ

def panHProgDefaultHandlers (α : Type u) (σ : Type v) : PanHProgHandlers α σ where
  dec := fun _ _ _ _ sourceState => .ret (.error sourceState)
  assign := fun _ _ _ sourceState => .ret (.error sourceState)
  primitive := fun _ _ _ sourceState => .ret (.error sourceState)
  store := fun _ _ sourceState => .ret (.error sourceState)
  store32 := fun _ _ sourceState => .ret (.error sourceState)
  storeByte := fun _ _ sourceState => .ret (.error sourceState)
  shMemLoad := fun _ _ _ _ sourceState => .ret (.error sourceState)
  shMemStore := fun _ _ _ sourceState => .ret (.error sourceState)
  seq := fun _ _ sourceState => .ret (.error sourceState)
  cond := fun _ _ _ sourceState => .ret (.error sourceState)
  whileProg := fun _ _ sourceState => .ret (.error sourceState)
  callProg := fun _ _ _ sourceState => .ret (.error sourceState)
  decCallProg := fun _ _ _ _ _ sourceState => .ret (.error sourceState)
  extCallProg := fun _ _ _ _ _ sourceState => .ret (.error sourceState)
  raiseProg := fun _ _ sourceState => .ret (.error sourceState)
  returnProg := fun _ sourceState => .ret (.error sourceState)

def panHProg (handlers : PanHProgHandlers α σ) : Prog α → σ → PanHProgTree σ
  | .skip, sourceState => .ret (.normal sourceState)
  | .annot _ _, sourceState => .ret (.normal sourceState)
  | .dec name shape value body, sourceState =>
      handlers.dec name shape value body sourceState
  | .assign kind name value, sourceState =>
      handlers.assign kind name value sourceState
  | .primitive name operator args, sourceState =>
      handlers.primitive name operator args sourceState
  | .store address value, sourceState =>
      handlers.store address value sourceState
  | .store32 address value, sourceState =>
      handlers.store32 address value sourceState
  | .storeByte address value, sourceState =>
      handlers.storeByte address value sourceState
  | .shMemLoad size kind name address, sourceState =>
      handlers.shMemLoad size kind name address sourceState
  | .shMemStore size address value, sourceState =>
      handlers.shMemStore size address value sourceState
  | .seq first second, sourceState =>
      handlers.seq first second sourceState
  | .ite condition thenBranch elseBranch, sourceState =>
      handlers.cond condition thenBranch elseBranch sourceState
  | .while condition body, sourceState =>
      handlers.whileProg condition body sourceState
  | .break, sourceState => .ret (.break sourceState)
  | .continue, sourceState => .ret (.continue sourceState)
  | .call info name args, sourceState =>
      handlers.callProg info name args sourceState
  | .decCall name shape function args body, sourceState =>
      handlers.decCallProg name shape function args body sourceState
  | .extCall function configuration configurationLength array arrayLength, sourceState =>
      handlers.extCallProg function configuration configurationLength array arrayLength sourceState
  | .raise exception value, sourceState =>
      handlers.raiseProg exception value sourceState
  | .return value, sourceState =>
      handlers.returnProg value sourceState
  | .tick, sourceState => .ret (.normal sourceState)

@[simp] theorem panHProg_skip (handlers : PanHProgHandlers α σ) (sourceState : σ) :
    panHProg handlers .skip sourceState = .ret (.normal sourceState) := by
  rfl

@[simp] theorem panHProg_break (handlers : PanHProgHandlers α σ) (sourceState : σ) :
    panHProg handlers .break sourceState = .ret (.break sourceState) := by
  rfl

@[simp] theorem panHProg_continue (handlers : PanHProgHandlers α σ) (sourceState : σ) :
    panHProg handlers .continue sourceState = .ret (.continue sourceState) := by
  rfl

@[simp] theorem panHProg_tick (handlers : PanHProgHandlers α σ) (sourceState : σ) :
    panHProg handlers .tick sourceState = .ret (.normal sourceState) := by
  rfl

end Flapjack
