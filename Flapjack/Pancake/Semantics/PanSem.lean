import Flapjack.PanValueFfiClockSemantics

/-!
# Pancake `evaluate`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:556-736`
(`evaluate_def`).  The source evaluates one `panLang$prog` against the
clocked Pancake state, preserving all source state components and returning
the remaining clock.  `PanSemEvaluateState` is the corresponding source
boundary; `panSemEvaluate` delegates to the exact clocked evaluator, whose
constructor equations cover declarations, assignments, primitives, ordinary
and sized stores, sequencing, conditionals, loops, calls, declaration calls,
exceptions, returns, shared memory, external calls, ticks, and annotations.

The fuel is only Lean's termination guard.  It is derived from the complete
program/function tree and source clock, while the observable semantics remain
the source clock and state transitions.
-/

namespace Flapjack

structure PanSemEvaluateState (α : Type u) (σ : Type v) where
  structs : StructContext
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
    evalPanValueFfiProgSteps, evalPanValueExpCounted,
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
