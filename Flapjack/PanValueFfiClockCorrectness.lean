import Flapjack.PanValueFfiClockSemantics

/-!
# Named contracts for the clocked source semantics

These lemmas expose the clock and timeout behavior at the same boundaries as
CakeML's `panSem`: a `Tick` consumes one clock unit, a zero-clock tick times
out with cleared locals, a true zero-clock loop times out after evaluating its
condition, and ordinary leaf evaluation does not change the clock.
-/

namespace Flapjack

theorem panValueFfiClockTimeout_locals
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :
    (panValueFfiClockTimeout globals memory ffi clock).1 =
      .timeout (fun _ => none) globals memory ffi := by
  rfl

theorem evalPanValueFfiClockProg_tick_zero
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      .tick (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.timeout (fun _ => none) globals memory ffi, 0) := by
  simp [evalPanValueFfiClockProg, panValueFfiClockTimeout]

theorem evalPanValueFfiClockProg_tick_succ
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + 1) .tick (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockProg]

theorem evalPanValueFfiClockProg_while_zero_timeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (conditionValue : α) (condition : Exp α) (body : Prog α)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) =
        some (.word conditionValue))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) =
      some (.timeout (fun _ => none) globals memory ffi, 0) := by
  simp [evalPanValueFfiClockProg, hcondition, hconditionNonzero,
    panValueFfiClockTimeout]

theorem evalPanValueFfiClockLeaf_clock
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (_fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α) (clockValue : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none) :
    (evalPanValueFfiClockLeaf context primitive handler structs functions
      baseAddress topAddress bytesInWord clockValue locals globals memory ffi
      program (memoryAccess := memoryAccess) (contracts := contracts)).map Prod.snd =
      (evalPanValueFfiProgSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord 1 locals globals memory ffi program
        (memoryAccess := memoryAccess) (contracts := contracts)).map
        (fun _ => clockValue) := by
  simp [evalPanValueFfiClockLeaf, Function.comp_def]

/-! A normal first component passes its complete state and remaining clock to
the second component.  This is the clocked counterpart of the sequencing rule
used by the source-to-Loop and Loop-to-Word simulation proofs. -/
theorem evalPanValueFfiClockProg_seq_normal
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock firstClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (middleLocals middleGlobals : VarName → Option (PanValue α))
    (middleMemory : α → Option (PanValue α)) (middleFfi : FfiState σ)
    (first second : Prog α) (outcome : PanValueFfiClockOutcome α σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hfirst : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first
        (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal middleLocals middleGlobals middleMemory middleFfi),
        firstClock))
    (hsecond : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel middleLocals middleGlobals middleMemory
        middleFfi firstClock second (memoryAccess := memoryAccess)
        (contracts := contracts) = some (outcome, finalClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
        (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (outcome, finalClock) := by
  simp [evalPanValueFfiClockProg, hfirst, hsecond]

/-! A zero-clock call still evaluates its arguments and validates the callee
lookup/binding boundary before producing `TimeOut`.  This mirrors the order
of the corresponding `panSem` equation and prevents a timeout theorem from
silently accepting malformed calls. -/
theorem evalPanValueFfiClockCall_zero_timeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals : VarName → Option (PanValue α))
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      info function arguments (memoryAccess := memoryAccess)
      (contracts := contracts) =
      some (.timeout (fun _ => none) globals memory ffi, 0) := by
  simp [evalPanValueFfiClockCall, hargs, hlookup, hbind,
    panValueFfiClockTimeout]

end Flapjack
