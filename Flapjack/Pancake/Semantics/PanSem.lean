import Flapjack.HolRef
import Flapjack.PanBst
import Flapjack.PanValueFfiClockSemantics

/-!
# Pancake `evaluate`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:556-736`
(`evaluate_def`). The HOL source evaluates one `panLang$prog` against a state
whose `code` field is a finite map. `PanSemEvaluateState` is the existing
list-backed executable compatibility boundary. `panSemEvaluateCodeState` is
the production source-state entry point: it resolves every recursive Call and
DecCall from the finite-support `PanSemState.code` map.

The fuel is only Lean's termination guard. The compatibility entry point uses
its legacy function list; the source-state entry point derives fuel from the
code map and source clock. Observable clock transitions remain those of the
source semantics.
-/

namespace Flapjack

/-- HOL `panSem$empty_locals`: clear only the source state's local map. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "empty_locals_def"]
def panEmptyLocals (state : PanSemState α ffi) : PanSemState α ffi :=
  { state with locals := fun _ => none }

/-- Faithful context-free port of Cake `panSem$shape_of`
    (`cakeml/pancake/semantics/panSemScript.sml:80`). The source `v` cases
    correspond exhaustively to `PanValue`: `.word w` represents
    `Val (Word w)` because HOL `word_lab` has only its `Word` constructor;
    `.rStruct vs` maps recursively to `Comb (MAP shape_of vs)`; `.nStruct nm
    fields` maps to `Named nm`, with fields ignored on both sides. The HOL
    definition has no premises or side conditions, and these three Lean cases
    have exactly the same behavior. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "shape_of_def"]
def panSemShapeOf : PanValue α → Shape
  | .word _ => .one
  | .rStruct values => .comb (values.map panSemShapeOf)
  | .nStruct name _ => .named name
termination_by value => sizeOf value

structure PanSemEvaluateState (α : Type u) (σ : Type v) where
  structs : StructContext
  /-- Compatibility function table. This list cannot stand in for the
      HOL-finite `PanSemState.code` map in a source Call/DecCall proof. -/
  functions : List (FunName × List VarName × Prog α)
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  memory : α → Option (PanValue α)
  ffi : FfiState σ
  clock : Nat
  baseAddress : α
  topAddress : α
  bytesInWord : α
  memoryAccess : Option (PanValueMemoryAccess α) := none
  contracts : Option PanValueCallContracts := none
  memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none

/-! Source-faithful callers carry the Cake memory operations as a required
    field.  The legacy state remains optional for executable compatibility;
    this wrapper is the typed boundary used by exact evaluator proofs. -/
structure PanSemExactState (α : Type u) (σ : Type v) where
  legacy : PanSemEvaluateState α σ
  memoryAccess : PanValueMemoryAccess α

def PanSemExactState.toEvaluateState (state : PanSemExactState α σ) :
    PanSemEvaluateState α σ :=
  { state.legacy with memoryAccess := some state.memoryAccess }

/-- One source `panSem$state.code` entry: typed parameters, function body, and
    return shape. This full entry is kept separately from the legacy runtime
    state's function-name/parameter-name/body triples. -/
structure PanSemFunctionEntry (α : Type u) where
  params : List (VarName × Shape)
  body : Prog α
  returnShape : Shape

/-- State boundary for the source `evaluate_decls` definition. `runtime`
    carries the expression-evaluation fields and preserves all runtime state;
    `code` and `eshapes` model the source finite maps directly, and the
    required `memoryAccess` supplies the source memory-domain/byte behavior;
    declaration evaluation cannot fall back to the permissive legacy memory
    path. In particular, the lossy `runtime.functions` compatibility field is
    not used as `code`. -/
structure PanSemDeclarationState (α : Type u) (σ : Type v) where
  runtime : PanSemEvaluateState α σ
  code : InfoMap (PanSemFunctionEntry α)
  eshapes : InfoMap Shape
  memoryAccess : PanValueMemoryAccess α

mutual
  def panSemExpFuel : Exp α → Nat
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => 1
    | .rStruct fields => 1 + panSemExpListFuel fields
    | .rField _ value | .nField _ value | .load32 value | .loadByte value =>
        1 + panSemExpFuel value
    | .nStruct _ fields => 1 + panSemFieldFuel fields
    | .load _ address => 1 + panSemExpFuel address
    | .op _ arguments | .panOp _ arguments => 1 + panSemExpListFuel arguments
    | .cmp _ left right | .shift _ left right =>
        1 + panSemExpFuel left + panSemExpFuel right

  def panSemExpListFuel : List (Exp α) → Nat
    | [] => 0
    | expression :: expressions =>
        panSemExpFuel expression + panSemExpListFuel expressions

  def panSemFieldFuel : List (FieldName × Exp α) → Nat
    | [] => 0
    | (_, expression) :: fields => panSemExpFuel expression + panSemFieldFuel fields

  def panSemCallInfoFuel :
      Option (Option (VarKind × VarName) ×
        Option (ExceptionId × VarName × Prog α)) → Nat
    | none => 0
    | some (_, none) => 0
    | some (_, some (_, _, handler)) => panSemProgFuel handler

  def panSemProgFuel : Prog α → Nat
    | .skip => 1
    | .dec _ _ value body => 1 + panSemExpFuel value + panSemProgFuel body
    | .assign _ _ value => 1 + panSemExpFuel value
    | .primitive _ _ arguments => 1 + panSemExpListFuel arguments
    | .store address value | .store32 address value | .storeByte address value =>
        1 + panSemExpFuel address + panSemExpFuel value
    | .seq first second => 1 + panSemProgFuel first + panSemProgFuel second
    | .ite condition thenBranch elseBranch =>
        1 + panSemExpFuel condition + panSemProgFuel thenBranch +
          panSemProgFuel elseBranch
    | .while condition body => 1 + panSemExpFuel condition + panSemProgFuel body
    | .break | .continue | .tick => 1
    | .call info _ arguments => 1 + panSemCallInfoFuel info + panSemExpListFuel arguments
    | .decCall _ _ _ arguments body =>
        1 + panSemExpListFuel arguments + panSemProgFuel body
    | .extCall _ configuration configurationLength array arrayLength =>
        1 + panSemExpFuel configuration + panSemExpFuel configurationLength +
          panSemExpFuel array + panSemExpFuel arrayLength
    | .raise _ value | .return value => 1 + panSemExpFuel value
    | .shMemLoad _ _ _ address => 1 + panSemExpFuel address
    | .shMemStore _ address value =>
        1 + panSemExpFuel address + panSemExpFuel value
    | .annot _ _ => 1

  def panSemFunctionFuel : List (FunName × List VarName × Prog α) → Nat
    | [] => 0
    | (_, _, body) :: functions =>
        max (panSemProgFuel body) (panSemFunctionFuel functions)
end

def panSemEvaluateFuel (state : PanSemEvaluateState α σ)
  (program : Prog α) : Nat :=
  state.clock + max (panSemProgFuel program) (panSemFunctionFuel state.functions) + 1

def panSemEvaluateWithFuel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (state : PanSemEvaluateState α σ) (program : Prog α) :
    Option (PanValueFfiClockResult α σ) :=
  evalPanValueFfiClockProg context primitive handler state.structs state.functions
    state.baseAddress state.topAddress state.bytesInWord fuel state.locals state.globals
    state.memory state.ffi state.clock program
    (memoryAccess := state.memoryAccess) (contracts := state.contracts)
    (memoryHandler := state.memoryHandler)

def panSemEvaluate
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ) (program : Prog α) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluateWithFuel context primitive handler
    (panSemEvaluateFuel state program) state program

/-- Maximum structural evaluation cost of a body stored in the finite source
    code map. The evaluator's internal fuel is derived from the state-owned
    map, never from a detached function list. -/
def panSemCodeBodyFuel (code : PanSemCodeMap α) : Nat :=
  code.foldl (fun fuel binding => max fuel (panSemProgFuel binding.2.2.1)) 0

/-- Conservative structural bound for source-state evaluation. Every executed
    source call and every repeated while iteration consumes source clock, so at
    most `state.clock` such phases execute; each phase is bounded by the larger
    of the entry program and every state-owned function body. -/
def panSemCodeEvaluateFuel (state : PanSemState α ffi)
    (program : Prog α) : Nat :=
  (state.clock + 1) * (max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 1) + 1

theorem panSemCodeEvaluateFuel_covers_clocked_bodies
    (state : PanSemState α ffi) (program : Prog α) :
    state.clock * panSemCodeBodyFuel state.code + panSemProgFuel program <
      panSemCodeEvaluateFuel state program := by
  unfold panSemCodeEvaluateFuel
  have hbody := Nat.le_max_right (panSemProgFuel program)
    (panSemCodeBodyFuel state.code)
  have hprogram := Nat.le_max_left (panSemProgFuel program)
    (panSemCodeBodyFuel state.code)
  calc
    state.clock * panSemCodeBodyFuel state.code + panSemProgFuel program ≤
        state.clock * max (panSemProgFuel program) (panSemCodeBodyFuel state.code) +
          max (panSemProgFuel program) (panSemCodeBodyFuel state.code) := by
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hbody) hprogram
    _ < state.clock * max (panSemProgFuel program) (panSemCodeBodyFuel state.code) +
          state.clock + max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 2 := by
      omega
    _ = (state.clock + 1) *
          (max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 1) + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      omega

/-- Clocked production evaluator whose recursive Call and DecCall clauses read
    each callee from `state.code`. The compatibility function list is empty;
    code lookup and the fuel bound both remain tied to the source state. -/
def panSemEvaluateCodeStateWithFuel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat)
    (state : PanSemState α (FfiState σ)) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ) :=
  evalPanValueFfiClockCodeProg context primitive handler state.structs state.code
    state.exceptionShapes
    state.baseAddress state.topAddress bytesInWord fuel state.locals state.globals
    state.memory state.ffi state.clock program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)

/-- Production source-state entry point with a finite-map-derived fuel bound. -/
def panSemEvaluateCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord
    (panSemCodeEvaluateFuel state program) state program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)

/-- Evaluate a production source state using Cake's `memaddrs`,
    `sh_memaddrs`, and `be` fields. The supplied word model describes the
    source word operations; every memory domain and endianness input is
    derived from `state`, while `bytesInWord` is source word-type metadata.
    This boundary must be used for HOL-facing proofs instead of the optional
    no-access compatibility path or a width read from the target state. -/
def panSemEvaluateCodeStateWithMemoryModel
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (model : PanMemoryModel α) (bytesInWord : α)
    (state : PanSemState α (FfiState σ)) (program : Prog α)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluateCodeState context primitive handler bytesInWord state program
    (memoryAccess := some (panValueMemoryAccessOfModel model state.memaddrs
      state.sharedMemaddrs state.be))
    (contracts := contracts) (memoryHandler := memoryHandler)

/-- Materialise the observable post-state of code-map evaluation. The source
    semantics never updates `state.code`; it is carried verbatim while the
    evaluator updates locals, globals, memory, FFI state, and clock. -/
def panSemCodeStateAfter (state : PanSemState α (FfiState σ))
    (result : PanValueFfiClockResult α σ) : PanSemState α (FfiState σ) :=
  let update (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :=
    { state with
      locals := locals
      globals := globals
      memory := memory
      ffi := ffi
      clock := clock }
  match result with
  | (.timeout locals globals memory ffi, clock) => update locals globals memory ffi clock
  | (.control control, clock) =>
      match control with
      | .normal locals globals memory ffi
      | .error locals globals memory ffi
      | .returned locals globals memory ffi _
      | .raised locals globals memory ffi _ _
      | .broke locals globals memory ffi
      | .continued locals globals memory ffi
      | .finalFfi locals globals memory ffi _ => update locals globals memory ffi clock

theorem panSemCodeStateAfter_preserves_code
    (state : PanSemState α (FfiState σ)) (result : PanValueFfiClockResult α σ) :
    (panSemCodeStateAfter state result).code = state.code := by
  cases result with
  | mk outcome clock =>
    cases outcome with
    | timeout _ _ _ _ => rfl
    | control control => cases control <;> rfl

/-- Source-state entry point paired with its post-state projection. -/
def panSemEvaluateCodeStateWithPostState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ × PanSemState α (FfiState σ)) := do
  let result ← panSemEvaluateCodeState context primitive handler bytesInWord state program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)
  pure (result, panSemCodeStateAfter state result)

theorem panSemEvaluateCodeStateWithPostState_eq_map
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state program
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      (panSemEvaluateCodeState context primitive handler bytesInWord state program
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler)).map
      (fun result => (result, panSemCodeStateAfter state result)) := by
  cases hresult : panSemEvaluateCodeState context primitive handler bytesInWord state
      program (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) <;>
    simp [panSemEvaluateCodeStateWithPostState, hresult]

/-! Production-evaluator counterpart of the HOL `evaluate_def` Tick equation
    (`cakeml/pancake/semantics/panSemScript.sml:683-685`) over the production
    source-state evaluator: at clock zero the result is `TimeOut` with cleared
    locals, otherwise `NONE` with the clock decremented and every other state
    component preserved. This is an untagged boundary equation because the
    structured result is reduced rather than HOL's `(prog_result, state)` pair. -/
theorem panSemEvaluateCodeStateWithPostState_tick
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state
        (.tick : Prog α) =
      if state.clock = 0 then
        some ((.timeout (fun _ => none) state.globals state.memory state.ffi, 0),
          { state with locals := fun _ => none })
      else
        some ((.control (.normal state.locals state.globals state.memory state.ffi),
            state.clock - 1),
          { state with clock := state.clock - 1 }) := by
  by_cases hclock : state.clock = 0 <;>
    simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
      panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
      panValueFfiClockTimeout, evalPanValueFfiClockCodeProg, hclock]

/-! Production-evaluator counterpart of the HOL `evaluate_def` Skip equation
    (`cakeml/pancake/semantics/panSemScript.sml:557`) over the production
    source-state evaluator: `Skip` yields the normal control result with the
    state (including the clock) carried verbatim. This is an untagged boundary
    equation because the structured result is reduced rather than HOL's
    `(prog_result, state)` pair. -/
theorem panSemEvaluateCodeStateWithPostState_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state
        (.skip : Prog α) =
      some ((.control (.normal state.locals state.globals state.memory state.ffi),
          state.clock), state) := by
  simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

/-! Exact HOL `evaluate_def` Assign equation
    (`cakeml/pancake/semantics/panSemScript.sml:566-572`) over the production
    source-state evaluator: the source expression is evaluated, the assignment
    is accepted exactly when `is_valid_value` holds, and the accepted value is
    written to the local or global map with the clock and every other state
    component carried verbatim. When the source expression does not evaluate or
    `is_valid_value` rejects the value, the result is an explicit `.error`
    control result with the unchanged state, matching HOL's `(SOME Error, s)`
    (distinct from Lean `none`, which now denotes a missing evaluation result).
    This is an untagged boundary equation because
    the structured result is reduced rather than HOL's `(prog_result, state)`
    pair. -/
theorem panSemEvaluateCodeStateWithFuel_assign
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (vk : VarKind) (name : VarName) (value : Exp α) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.assign vk name value : Prog α) =
      match evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord value with
      | some evaluated =>
          if panValueAssignmentValid state.structs state.locals state.globals vk name evaluated then
            match vk with
            | .local =>
                some ((.control (.normal (updatePanValueMap state.locals name evaluated)
                    state.globals state.memory state.ffi), state.clock))
            | .global =>
                some ((.control (.normal state.locals
                    (updatePanValueMap state.globals name evaluated)
                    state.memory state.ffi), state.clock))
          else
            some ((.control (.error state.locals state.globals state.memory state.ffi),
              state.clock))
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock)) := by
  cases hvalue : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord value with
  | none =>
      cases vk <;>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueAssignLocalResult,
        panValueAssignGlobalResult, evalPanValueExpCounted, hvalue]
  | some evaluated =>
      cases vk <;>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueAssignLocalResult,
        panValueAssignGlobalResult, evalPanValueExpCounted, hvalue] <;>
      split <;> simp

/-- Production source-state `Dec` equation. When the initialiser evaluates to a
    value whose shape matches the declared shape, the body runs with the
    declaration bound in the local map and, on completion, the declared local is
    restored to its previous binding; a shape mismatch or a failing initialiser
    yields an explicit `Error` control result carrying the unchanged state
    (`panSem`'s `(SOME Error, s)`), distinct from a missing `none` evaluation
    result. The equation is stated over the explicit-fuel evaluator
    because the recursive body call reuses the predecessor fuel, so it cannot be
    phrased against the finite-map-derived entry point. This is an untagged
    boundary equation because the structured result is reduced rather than HOL's
    `(prog_result, state)` pair. Reference:
    cakeml/pancake/semantics/panSemScript.sml:558-565 (`Dec`). -/
theorem panSemEvaluateCodeStateWithFuel_dec
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.dec name shape value body : Prog α) =
      match evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord value with
      | some evaluated =>
          if panShapeMatches (panValueShape state.structs evaluated) shape then
            (panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel
                { state with
                  locals := updatePanValueMap state.locals name evaluated } body).map
              (fun result =>
                (panValueFfiClockRestoreLocal name (state.locals name) result.1, result.2))
          else
            some ((.control (.error state.locals state.globals state.memory state.ffi),
              state.clock))
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock)) := by
  cases hvalue : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord value with
  | none =>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        panValueDecAcceptedValue, hvalue]
  | some evaluated =>
      by_cases hshape : panShapeMatches (panValueShape state.structs evaluated) shape = true
      · simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
          panValueDecAcceptedValue, hvalue, hshape, Option.map_eq_bind]
        rfl
      · simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
          panValueDecAcceptedValue, hvalue, hshape]

/-- Production source-state `Primitive` equation. The argument expressions are
    evaluated together; when they all succeed the primitive handler is applied
    and, if the produced value has the same shape as the destination local's
    current binding, that local is updated; any failure yields an explicit
    `Error` control result carrying the unchanged state (`panSem`'s
    `(SOME Error, s)`), distinct from a missing `none` evaluation result. This is
    an untagged boundary equation because the structured result is reduced
    rather than HOL's `(prog_result, state)` pair. Reference:
    cakeml/pancake/semantics/panSemScript.sml:573-582 (`Primitive`). -/
theorem panSemEvaluateCodeStateWithFuel_primitive
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (name : VarName) (operator : PrimOp) (arguments : List (Exp α)) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.primitive name operator arguments : Prog α) =
      match evalPanValueExps state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord arguments with
      | some values =>
          match primitive operator values with
          | some evaluated =>
              match state.locals name with
              | some oldValue =>
                  if panShapeMatches (panValueShape state.structs evaluated)
                      (panValueShape state.structs oldValue) then
                    some ((.control (.normal
                        (updatePanValueMap state.locals name evaluated)
                        state.globals state.memory state.ffi), state.clock))
                  else
                    some ((.control (.error state.locals state.globals state.memory state.ffi),
                      state.clock))
              | none =>
                  some ((.control (.error state.locals state.globals state.memory state.ffi),
                    state.clock))
          | none =>
              some ((.control (.error state.locals state.globals state.memory state.ffi),
                state.clock))
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock)) := by
  cases hvalues : evalPanValueExps state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord arguments with
  | none =>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
        evalPanValueExpsCounted, hvalues]
  | some values =>
      cases hprim : primitive operator values with
      | none =>
          simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
            evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
            evalPanValueExpsCounted, hvalues, hprim]
      | some evaluated =>
          cases hlocal : state.locals name with
          | none =>
              simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
                evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
                evalPanValueExpsCounted, hvalues, hprim, hlocal]
          | some oldValue =>
              by_cases hshape : panShapeMatches (panValueShape state.structs evaluated)
                  (panValueShape state.structs oldValue) = true
              · simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
                  evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
                  evalPanValueExpsCounted, hvalues, hprim, hlocal, hshape]
              · simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
                  evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
                  evalPanValueExpsCounted, hvalues, hprim, hlocal, hshape]
/-- Production source-state `Seq` equation. The first command is evaluated and
    its clock clamped to the entry clock (`fix_clock`); a normal (`NONE`)
    outcome continues with the second command in the resulting state, while any
    other outcome (including an explicit `Error`) is returned unchanged. This is
    an untagged boundary equation because the structured result is reduced
    rather than HOL's `(prog_result, state)` pair. Reference:
    cakeml/pancake/semantics/panSemScript.sml:615-618 (`Seq`). -/
theorem panSemEvaluateCodeStateWithFuel_seq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (first second : Prog α) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.seq first second : Prog α) =
      match panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel
          state first with
      | some firstStep =>
          let fixedStep := fixPanClock state.clock firstStep
          match fixedStep.1 with
          | .control (.normal nextLocals nextGlobals nextMemory nextFfi) =>
              panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel
                { state with
                  locals := nextLocals
                  globals := nextGlobals
                  memory := nextMemory
                  ffi := nextFfi
                  clock := fixedStep.2 } second
          | _ => some fixedStep
      | none => none := by
  simp only [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg, fixPanClock]
  cases h : evalPanValueFfiClockCodeProg context primitive handler state.structs state.code
      state.exceptionShapes state.baseAddress state.topAddress bytesInWord fuel state.locals
      state.globals state.memory state.ffi state.clock first with
  | none => simp
  | some firstStep => rfl

/-- The production source evaluator exposes the `panSem` `If` equation: a
    non-word (or missing) condition yields the explicit `Error` result with the
    unchanged source state, while a word condition evaluates the selected
    branch at the unchanged clock.  The result is the reduced structured pair,
    not HOL's `(prog_result, state)`, so this stays an untagged boundary
    equation.  The condition is evaluated with the caller's `memoryAccess`
    (which the state-owned entry derives from `state.memaddrs`, `state.be`, and
    the word model), so memory-reading conditions do not fall back to the
    legacy whole-cell path.  Reference:
    `cakeml/pancake/semantics/panSemScript.sml:617-620`. -/
theorem panSemEvaluateCodeStateWithFuel_ite
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (condition : Exp α) (thenBranch elseBranch : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.ite condition thenBranch elseBranch : Prog α)
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) =
      match panValueIteConditionValue state.structs state.baseAddress state.topAddress
          bytesInWord state.locals state.globals state.memory condition memoryAccess with
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock))
      | some conditionValue =>
          panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel state
            (if conditionValue != 0 then thenBranch else elseBranch)
            (memoryAccess := memoryAccess) (contracts := contracts)
            (memoryHandler := memoryHandler) := by
  simp only [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg]
  cases h : panValueIteConditionValue state.structs state.baseAddress state.topAddress
      bytesInWord state.locals state.globals state.memory condition memoryAccess with
  | none => rfl
  | some conditionValue => rfl

/-- The `If` equation instantiated with the
    state-derived memory access: the condition reads memory through
    `state.memaddrs`, `state.sharedMemaddrs`, and `state.be` (via the word
    model), matching the state-owned `panSemEvaluateCodeStateWithMemoryModel`
    entry point.  Untagged boundary equation for the same reason as
    `panSemEvaluateCodeStateWithFuel_ite`. -/
theorem panSemEvaluateCodeStateWithFuel_ite_state_memory
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (model : PanMemoryModel α) (bytesInWord : α) (fuel : Nat)
    (state : PanSemState α (FfiState σ))
    (condition : Exp α) (thenBranch elseBranch : Prog α) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.ite condition thenBranch elseBranch : Prog α)
        (memoryAccess := some (panValueMemoryAccessOfModel model state.memaddrs
          state.sharedMemaddrs state.be)) =
      match panValueIteConditionValue state.structs state.baseAddress state.topAddress
          bytesInWord state.locals state.globals state.memory condition
          (some (panValueMemoryAccessOfModel model state.memaddrs
            state.sharedMemaddrs state.be)) with
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock))
      | some conditionValue =>
          panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel state
            (if conditionValue != 0 then thenBranch else elseBranch)
            (memoryAccess := some (panValueMemoryAccessOfModel model state.memaddrs
              state.sharedMemaddrs state.be)) :=
  panSemEvaluateCodeStateWithFuel_ite context primitive handler bytesInWord fuel state
    condition thenBranch elseBranch (some (panValueMemoryAccessOfModel model state.memaddrs
      state.sharedMemaddrs state.be))

/-!
  Exact source-memory entry point.

  CakeML's `panSem$evaluate` receives `memaddrs`, `be`, and the word-memory
  operations through its state.  The structured compatibility API keeps an
  optional access field for older callers, but this entry point requires the
  access record explicitly so `Load32`/`LoadByte` cannot silently fall back to
  whole-cell reads.
-/
def panSemEvaluateExact
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (memoryAccess : PanValueMemoryAccess α)
    (state : PanSemEvaluateState α σ) (program : Prog α) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluate context primitive handler
    { state with memoryAccess := some memoryAccess } program

/-! The exact source entrypoint is a state boundary, not a second evaluator:
    it installs the explicit Cake memory operations before evaluating.  Keeping
    this equation named makes exact correctness proofs unable to silently
    select the legacy no-access compatibility path. -/
theorem panSemEvaluateExact_uses_memory_access
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (memoryAccess : PanValueMemoryAccess α)
    (state : PanSemEvaluateState α σ) (program : Prog α) :
    panSemEvaluateExact context primitive handler memoryAccess state program =
      panSemEvaluate context primitive handler
        { state with memoryAccess := some memoryAccess } program := by
  rfl

def panSemEvaluateExactState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ) (program : Prog α) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluate context primitive handler state.toEvaluateState program

theorem panSemEvaluateExactState_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ) (program : Prog α) :
    panSemEvaluateExactState context primitive handler state program =
      panSemEvaluate context primitive handler state.toEvaluateState program := by
  rfl

/-! A generic source `Raise` equation for the exact state boundary.  The
    evaluator and payload-validity premises remain explicit so this theorem
    does not silently discharge arbitrary exception contracts. -/
theorem panSemEvaluateExactState_raise_of_eval
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (exception : ExceptionId) (expression : Exp α) (value : PanValue α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord expression
      (memoryAccess := some state.memoryAccess) = some value)
    (hvalid : panValueExceptionValid state.legacy.structs
      state.legacy.contracts exception value = true)
    (hlimit : panValuePayloadWithinLimit state.legacy.structs value = true) :
    panSemEvaluateExactState context primitive handler state
        (.raise exception expression) =
      some (.control (.raised (fun _ => none) state.legacy.globals
        state.legacy.memory state.legacy.ffi exception value), state.legacy.clock) := by
  simp [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockLeaf, evalPanValueFfiClockProg,
    evalPanValueFfiProgSteps, panValueRaiseResult, evalPanValueExpCounted,
    PanSemExactState.toEvaluateState, heval, hvalid, hlimit]

/-! Finite-map updates for the source declaration evaluator. `InfoMap` is an
    association-list representation; putting the updated binding first and
    removing older copies gives the same lookup behavior as HOL `|+`. -/
def panSemDeclUpdateInfo [BEq String] (entries : InfoMap β)
    (name : String) (value : β) : InfoMap β :=
  (name, value) :: entries.filter (fun entry => !(entry.1 == name))

def panSemDeclUpdateGlobal [BEq String]
    (globals : VarName → Option (PanValue α)) (name : VarName)
    (value : PanValue α) : VarName → Option (PanValue α) :=
  fun candidate => if candidate == name then some value else globals candidate

/-! Constructor form of the admissible-declaration premise used by Cake's
    `compile_top_shape_wf`: functions, value declarations, and exceptions are
    admitted; struct-name declarations are excluded. -/
def panSemCompileTopAdmissible : Decl α → Bool
  | .function _ | .decl _ _ _ | .exnDecl _ _ => true
  | .name _ _ => false

/-! Faithful declaration-by-declaration port of Cake
    `panSem$evaluate_decls` (`panSemScript.sml:814-835`). The dedicated
    `code` map retains parameter and return shapes, and `eshapes` retains the
    source exception map. The legacy runtime `functions` list is not used as a
    substitute for the source code map. Unlike `evalPanValueDeclarations`,
    this definition does no struct-name prepass: HOL's `Name` case is a no-op. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_decls_def"]
def evaluateDecls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [BEq String]
    (state : PanSemDeclarationState α σ) : List (Decl α) →
      Option (PanSemDeclarationState α σ)
  | [] => some state
  | .name _ _ :: declarations => evaluateDecls state declarations
  | .decl shape name expression :: declarations =>
      match evalPanValueExp state.runtime.structs (fun _ => none)
          state.runtime.globals state.runtime.memory state.runtime.baseAddress
          state.runtime.topAddress state.runtime.bytesInWord expression
          (memoryAccess := some state.memoryAccess) with
      | none => none
      | some value =>
          if panShapeMatches (panValueShape state.runtime.structs value) shape then
            evaluateDecls
              { state with runtime :=
                { state.runtime with globals :=
                    panSemDeclUpdateGlobal state.runtime.globals name value } }
              declarations
          else none
  | .function declaration :: declarations =>
      if declaration.params.all (fun parameter =>
          isWfShape state.runtime.structs parameter.2) &&
          isWfShape state.runtime.structs declaration.returnShape then
        let entry : PanSemFunctionEntry α :=
          { params := declaration.params
            body := declaration.body
            returnShape := declaration.returnShape }
        evaluateDecls
          { state with code := panSemDeclUpdateInfo state.code declaration.name entry }
          declarations
      else none
  | .exnDecl exception shape :: declarations =>
      if (lookupInfo exception state.eshapes).isSome then none
      else if isWfShape state.runtime.structs shape then
        evaluateDecls
          { state with eshapes := panSemDeclUpdateInfo state.eshapes exception shape }
          declarations
      else none
termination_by declarations => sizeOf declarations
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial

end Flapjack
