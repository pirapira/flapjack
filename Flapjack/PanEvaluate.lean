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

end Flapjack
