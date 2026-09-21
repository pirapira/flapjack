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
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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

/-! The leaf adapter also preserves the terminal FFI branch exactly.  This is
    the source-side counterpart of the \`panSem\` ExtCall/shared-memory
    \`FinalFFI\` equations (cakeml/pancake/semantics/panSemScript.sml:716-730):
    the stepped evaluator supplies the complete post-state and event, while
    the clocked leaf only attaches the unchanged remaining clock. -/
theorem evalPanValueFfiClockLeaf_finalFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (clock : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α) (finalLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (event : FfiFinalEvent) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi program
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.finalFfi finalLocals finalGlobals finalMemory finalFfi event, steps)) :
    evalPanValueFfiClockLeaf context primitive handler structs functions
      baseAddress topAddress bytesInWord clock locals globals memory ffi program
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi finalLocals finalGlobals finalMemory finalFfi event), clock) := by
  simp [evalPanValueFfiClockLeaf, hsteps]

/-! A normal first component passes its complete state and remaining clock to
the second component.  This is the clocked counterpart of the sequencing rule
used by the source-to-Loop and Loop-to-Word simulation proofs. -/
theorem evalPanValueFfiClockProg_seq_normal
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
      if panValueParametersValid structs contracts function values then
        some (.timeout (fun _ => none) globals memory ffi, 0)
      else none := by
  simp [evalPanValueFfiClockCall, hargs, hlookup, hbind,
    panValueFfiClockTimeout]

/-! A successful nonzero-clock call returns the callee's final globals,
memory, FFI state, and remaining clock, while clearing the callee locals at
the caller boundary. -/
theorem evalPanValueFfiClockCall_returned_no_destination
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi values), finalClock))
    (hwithin : panValueValuesWithinLimit structs values = true) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi values),
        finalClock) := by
  simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hclock, hbody, hwithin]

/-! An uncaught exception from a successful nonzero-clock call preserves the
callee's state and clock while clearing the callee locals at the caller
boundary. -/
theorem evalPanValueFfiClockCall_raised_no_handler
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (exception : ExceptionId) (value : PanValue α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised bodyLocals finalGlobals finalMemory finalFfi exception value),
        finalClock))
    (hwithin : panValuePayloadWithinLimit structs value = true) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised (fun _ => none) finalGlobals finalMemory finalFfi exception value),
        finalClock) := by
  simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hclock, hbody, hwithin]

/-! Cake's `pc_compile_correct[Call_Ret_TimeOut]` propagates a callee
timeout through a direct call.  The caller-local environment is cleared, but
the callee's globals, memory, FFI state, and remaining clock are retained. -/
theorem evalPanValueFfiClockCall_timeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.timeout bodyLocals finalGlobals finalMemory finalFfi, finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) finalGlobals finalMemory finalFfi, finalClock) := by
  simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hparameters, hclock, hbody]

/-! A declaration call propagates the callee's terminal outcomes.  Cake's
    `panSem` does not turn a callee timeout or FinalFFI into an evaluator
    failure merely because the call has a local continuation. -/
theorem evalPanValueFfiClockProg_decCall_timeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.timeout (fun _ => none) nextGlobals nextMemory nextFfi, callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.timeout (fun _ => none) nextGlobals nextMemory nextFfi, callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

theorem evalPanValueFfiClockProg_decCall_finalFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! A successful `DecCall` installs the single returned value for its
    continuation, checks the declared shape, and restores the caller's old
    local binding after that continuation completes. -/
theorem evalPanValueFfiClockProg_decCall_returned
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (calleeLocals : VarName → Option (PanValue α))
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (value : PanValue α) (outcome : PanValueFfiClockOutcome α σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.returned calleeLocals nextGlobals nextMemory nextFfi [value]),
        callClock))
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
      nextGlobals nextMemory nextFfi callClock body =
      some (outcome, finalClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (panValueFfiClockRestoreLocal name (locals name) outcome, finalClock) := by
  simp [evalPanValueFfiClockProg, hcall, hshape, hbody]

/-! An uncaught exception from a clocked `DecCall` bypasses its local
    continuation and preserves the callee's post-call state and clock. -/
theorem evalPanValueFfiClockProg_decCall_raised
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (exception : ExceptionId) (value : PanValue α)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the direct `Call_Ret_FinalFFI` branch of Cake's
    `pc_compile_correct`. A direct call has no declaration continuation, so
    the callee's final FFI event is returned unchanged by the enclosing
    program evaluator. -/
theorem evalPanValueFfiClockProg_call_finalFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      info function arguments =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call info function arguments) =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the direct `Call_Ret_TimeOut` branch of Cake's
    `pc_compile_correct`: a direct call propagates the callee timeout without
    introducing a declaration continuation. -/
theorem evalPanValueFfiClockProg_call_timeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      info function arguments =
      some (.timeout nextLocals nextGlobals nextMemory nextFfi, callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call info function arguments) =
      some (.timeout nextLocals nextGlobals nextMemory nextFfi, callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the direct `ExtCall` branch of Cake's `pc_compile_correct`.
    The source leaf evaluator's terminal FFI event crosses the clocked program
    boundary unchanged, with only the remaining clock attached. -/
theorem evalPanValueFfiClockProg_extCall_finalFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (_fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName) (configuration configurationLength array arrayLength : Exp α)
    (finalLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (event : FfiFinalEvent) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi
      (.extCall function configuration configurationLength array arrayLength)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.finalFfi finalLocals finalGlobals finalMemory finalFfi event, steps)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (_fuel + 1) locals globals memory ffi clock
      (.extCall function configuration configurationLength array arrayLength)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi finalLocals finalGlobals finalMemory finalFfi event), clock) := by
  simpa [evalPanValueFfiClockProg] using
    (evalPanValueFfiClockLeaf_finalFfi context primitive handler structs functions
      baseAddress topAddress bytesInWord clock locals globals memory ffi
      (.extCall function configuration configurationLength array arrayLength)
      finalLocals finalGlobals finalMemory finalFfi event steps
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) hsteps)

/-! This is the standalone `Call_Ret_Return` branch of Cake's
    `pc_compile_correct`: with no destination or handler, a valid returned
    value crosses the program-call boundary unchanged. -/
theorem evalPanValueFfiClockProg_call_returned
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName) (arguments : List (Exp α))
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.returned (fun _ => none) nextGlobals nextMemory nextFfi values),
        callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call none function arguments) =
      some (.control (.returned (fun _ => none) nextGlobals nextMemory nextFfi values),
        callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the standalone uncaught `Call_Ret_Exception` branch of Cake's
    `pc_compile_correct`: without a handler, the callee's raised exception and
    post-call state cross the program-call boundary unchanged. -/
theorem evalPanValueFfiClockProg_call_raised
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName) (arguments : List (Exp α))
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (exception : ExceptionId) (value : PanValue α)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call none function arguments) =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the destination-bearing `Call_Ret_Return` branch of Cake's
    `pc_compile_correct`: a returned value is installed in the caller's
    destination, while the callee memory, FFI state, and clock are retained. -/
theorem evalPanValueFfiClockProg_call_returned_destination
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (destination : Option (VarKind × VarName))
    (function : FunName) (arguments : List (Exp α))
    (assignedLocals assignedGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      (some (destination, none)) function arguments =
      some (.control (.normal assignedLocals assignedGlobals nextMemory nextFfi),
        callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call (some (destination, none)) function arguments) =
      some (.control (.normal assignedLocals assignedGlobals nextMemory nextFfi),
        callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the handler-bearing `Call_Ret_Exception` branch of Cake's
    `pc_compile_correct`: a caught exception resumes the handler through the
    enclosing program-call constructor with the callee's post-call state. -/
theorem evalPanValueFfiClockProg_call_caught_handler
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (caught : ExceptionId) (handlerVariable : VarName)
    (handlerProgram : Prog α) (function : FunName) (arguments : List (Exp α))
    (outcome : PanValueFfiClockOutcome α σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      (some (none, some (caught, handlerVariable, handlerProgram))) function arguments =
      some (outcome, callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call (some (none, some (caught, handlerVariable, handlerProgram)))
        function arguments) =
      some (outcome, callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! A caught exception resumes the handler in the callee's final state and
remaining clock, rather than restoring the caller's pre-call globals or
memory. -/
theorem evalPanValueFfiClockCall_caught_handler
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals calleeGlobals : VarName → Option (PanValue α))
    (calleeMemory : α → Option (PanValue α)) (calleeFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (caught : ExceptionId) (exception : ExceptionId) (value : PanValue α)
    (handlerVariable : VarName) (handlerProgram : Prog α)
    (outcome : PanValueFfiClockOutcome α σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised bodyLocals calleeGlobals calleeMemory calleeFfi exception value),
        finalClock))
    (hcaught : caught = exception)
    (hwithin : panValuePayloadWithinLimit structs value = true)
    (hhandler : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel
      (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory calleeFfi
      finalClock handlerProgram (memoryAccess := memoryAccess) (contracts := none) =
      some (outcome, finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (some (none, some (caught, handlerVariable, handlerProgram))) function arguments
      (memoryAccess := memoryAccess) (contracts := none) =
      some (outcome, finalClock) := by
  simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hclock, hbody,
    hcaught, hhandler, hwithin]

/-! A successful returned value may be assigned to a caller local or global.
The assignment is checked by the source shape predicate and uses the
callee's final globals, while memory, FFI state, and clock are propagated. -/
theorem evalPanValueFfiClockCall_returned_destination
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (destination : Option (VarKind × VarName))
    (assignedLocals assignedGlobals : VarName → Option (PanValue α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi values), finalClock))
    (hwithin : panValueValuesWithinLimit structs values = true)
    (hassign : assignPanValueCallResult locals finalGlobals destination values
      (structs := structs) = some (assignedLocals, assignedGlobals)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (some (destination, none)) function arguments
      (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.normal assignedLocals assignedGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hclock, hbody, hwithin,
    hassign]

/-! One true loop iteration consumes one clock unit before evaluating the body
and then resumes the loop with the body's resulting state and clock. -/
theorem evalPanValueFfiClockProg_while_normal_iteration
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock bodyClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (bodyLocals bodyGlobals : VarName → Option (PanValue α))
    (bodyMemory : α → Option (PanValue α)) (bodyFfi : FfiState σ)
    (conditionValue : α) (condition : Exp α) (body : Prog α)
    (outcome : PanValueFfiClockOutcome α σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock))
    (hrest : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      bodyClock (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) = some (outcome, finalClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.while condition body) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (outcome, finalClock) := by
  simp [evalPanValueFfiClockProg, hcondition, hconditionNonzero, hclock,
    hbody, hrest]

/-! The top-level clocked evaluator preserves an explicitly raised call result.
    Declaration elaboration, generated contracts, and the remaining clock stay
    visible premises, so this bridge does not fold timeout or FinalFFI into a
    generic control case. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_raised_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (exception : ExceptionId) (value : PanValue α) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock) := by
  simp [evalPanValueFfiClockProgram, hdeclarations, hcall]

/-! The corresponding timeout bridge keeps zero-clock behavior explicit at the
    declaration/program boundary. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_timeout_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) globals memory ffi, nextClock)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) globals memory ffi, nextClock) := by
  simp [evalPanValueFfiClockProgram, hdeclarations, hcall]

/-! The top-level clocked evaluator also preserves a terminal `FinalFFI`
    outcome from the selected call.  This is the declaration-boundary form of
    Cake's `pc_compile_correct[Call_FinalFFI]` case. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_finalFfi_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (event : FfiFinalEvent) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi locals globals memory ffi event), nextClock)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi locals globals memory ffi event), nextClock) := by
  simp [evalPanValueFfiClockProgram, hdeclarations, hcall]

/-! A successful singleton return crosses the clocked declaration boundary only
    when Cake's entry shape accepts the returned value. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_returned_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α) (shape : Shape)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (value : PanValue α) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.returned locals globals memory ffi [value]), nextClock))
    (hentry : lookupInfo entry state.returnShapes = some shape)
    (hshape : panShapeMatches (panValueShape state.structs value) shape = true) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.returned locals globals memory ffi [value]), nextClock) := by
  simp [evalPanValueFfiClockProgram, hdeclarations, hcall, hentry, hshape]

end Flapjack
