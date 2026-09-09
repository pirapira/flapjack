import Flapjack.PanValueFfiClockCorrectness

/-!
# Clocked-to-stepped source projection

This file provides the first compositional bridge between the explicit-clock
stateful-FFI evaluator and the source-step evaluator.  The hypotheses expose
the agreement at the two component boundaries; the conclusion preserves both
the clocked result and the exact accumulated source-step count across `seq`.
-/

namespace Flapjack

theorem evalPanValueFfiClockProg_seq_projects_to_steps
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
    (secondResult : PanValueFfiControlResult α σ)
    (firstSteps secondSteps : Nat)
    (first second : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hfirstClock : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal middleLocals middleGlobals middleMemory middleFfi), firstClock))
    (hsecondClock : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel middleLocals middleGlobals middleMemory
      middleFfi firstClock second (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control secondResult, finalClock))
    (hfirstSteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi first
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.normal middleLocals middleGlobals middleMemory middleFfi, firstSteps))
    (hsecondSteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel middleLocals middleGlobals middleMemory
      middleFfi second (memoryAccess := memoryAccess) (contracts := contracts) =
      some (secondResult, secondSteps)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control secondResult, finalClock) ∧
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (secondResult, firstSteps + secondSteps + 1) := by
  constructor
  · simp [evalPanValueFfiClockProg, hfirstClock, hsecondClock]
  · simp [evalPanValueFfiProgSteps, hfirstSteps, hsecondSteps]

/-! The no-destination return branch has the same projection property at a
call boundary.  Argument steps and callee steps are added by the stepped
evaluator, while the clocked evaluator returns the callee's remaining clock. -/
theorem evalPanValueFfiClockCall_returned_projects_to_steps
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
    (argumentSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hreturn : panValueReturnValid structs contracts function values = true)
    (hwithin : panValueValuesWithinLimit structs values = true)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi values), finalClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.returned bodyLocals finalGlobals finalMemory finalFfi values, bodySteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi values),
        finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.returned (fun _ => none) finalGlobals finalMemory finalFfi values,
        argumentSteps + bodySteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hclock, hreturn,
      hwithin, hclockBody]
  · simp [evalPanValueFfiCallSteps, hargsSteps, hlookup, hbind, hreturn,
      hwithin, hstepBody]

/-! The uncaught-exception call branch projects in the same way: the callee
state and clock are preserved, and the source-step count includes argument
and callee evaluation. -/
theorem evalPanValueFfiClockCall_raised_projects_to_steps
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
    (argumentSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hexception : panValueExceptionValid structs contracts exception value = true)
    (hwithin : panValuePayloadWithinLimit structs value = true)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.raised bodyLocals finalGlobals finalMemory finalFfi exception value),
        finalClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.raised bodyLocals finalGlobals finalMemory finalFfi exception value, bodySteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.raised (fun _ => none) finalGlobals finalMemory finalFfi exception value),
        finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.raised (fun _ => none) finalGlobals finalMemory finalFfi exception value,
        argumentSteps + bodySteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hclock, hexception,
      hwithin, hclockBody]
  · simp [evalPanValueFfiCallSteps, hargsSteps, hlookup, hbind, hexception,
      hwithin, hstepBody]

/-! Return values assigned to an explicit caller destination project as well.
The assignment result is shared by the clocked and stepped evaluators, while
the callee memory, FFI state, and remaining clock continue to be preserved. -/
theorem evalPanValueFfiClockCall_destination_projects_to_steps
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
    (argumentSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hreturn : panValueReturnValid structs contracts function values = true)
    (hwithin : panValueValuesWithinLimit structs values = true)
    (hassign : assignPanValueCallResult locals finalGlobals destination values
      (structs := structs) = some (assignedLocals, assignedGlobals))
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi values), finalClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.returned bodyLocals finalGlobals finalMemory finalFfi values, bodySteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (some (destination, none)) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal assignedLocals assignedGlobals finalMemory finalFfi), finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (some (destination, none)) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.normal assignedLocals assignedGlobals finalMemory finalFfi,
        argumentSteps + bodySteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hclock, hreturn,
      hwithin, hassign, hclockBody]
  · simp [evalPanValueFfiCallSteps, hargsSteps, hlookup, hbind, hreturn,
      hwithin, hassign, hstepBody]

/-! A caught exception projects through the handler continuation.  The
handler's clock and step result are both threaded after the callee's state has
been transferred to it. -/
theorem evalPanValueFfiClockCall_handler_projects_to_steps
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
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals calleeGlobals : VarName → Option (PanValue α))
    (calleeMemory : α → Option (PanValue α)) (calleeFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (caught exception : ExceptionId) (value : PanValue α)
    (handlerVariable : VarName) (handlerProgram : Prog α)
    (handlerResult : PanValueFfiControlResult α σ)
    (argumentSteps calleeSteps handlerSteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hexception : panValueExceptionValid structs contracts exception value = true)
    (hwithin : panValuePayloadWithinLimit structs value = true)
    (hcaught : caught = exception)
    (hhandlerValid : panValueHandlerValid structs contracts locals handlerVariable value = true)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.raised bodyLocals calleeGlobals calleeMemory calleeFfi exception value),
        bodyClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.raised bodyLocals calleeGlobals calleeMemory calleeFfi exception value,
        calleeSteps))
    (hclockHandler : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel
      (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory calleeFfi
      bodyClock handlerProgram (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control handlerResult, finalClock))
    (hstepHandler : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel
      (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory calleeFfi
      handlerProgram (memoryAccess := memoryAccess) (contracts := contracts) =
      some (handlerResult, handlerSteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (some (none, some (caught, handlerVariable, handlerProgram))) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control handlerResult, finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (some (none, some (caught, handlerVariable, handlerProgram))) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (handlerResult, argumentSteps + calleeSteps + handlerSteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hclock, hexception,
      hwithin, hcaught, hhandlerValid, hclockBody, hclockHandler]
  · simp [evalPanValueFfiCallSteps, hargsSteps, hlookup, hbind, hexception,
      hwithin, hcaught, hhandlerValid, hstepBody, hstepHandler]

/-! One true loop iteration also projects compositionally.  The body consumes
one clock unit, and both evaluators then resume the loop from the body state. -/
theorem evalPanValueFfiClockProg_while_projects_to_steps
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
    (finalResult : PanValueFfiControlResult α σ)
    (conditionSteps bodySteps restSteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue))
    (hconditionSteps : evalPanValueExpCounted structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue, conditionSteps))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    (hclock : clock ≠ 0)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.normal bodyLocals bodyGlobals bodyMemory bodyFfi, bodySteps))
    (hclockRest : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      bodyClock (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) = some (.control finalResult, finalClock))
    (hstepRest : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      (.while condition body) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (finalResult, restSteps)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.while condition body) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control finalResult, finalClock) ∧
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.while condition body) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (finalResult, conditionSteps + bodySteps + restSteps + 1) := by
  constructor
  · simp [evalPanValueFfiClockProg, hcondition, hconditionNonzero, hclock,
      hclockBody, hclockRest]
  · simp [evalPanValueFfiProgSteps, hconditionSteps, hconditionNonzero,
      hstepBody, hstepRest]

/-! A declaration call projects through its returned-value continuation.  The
continuation receives the callee's state and clock, and the declaration's
shadowed local is restored in both result representations. -/
theorem evalPanValueFfiClockProg_decCall_projects_to_steps
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
    (callLocals callGlobals : VarName → Option (PanValue α))
    (callMemory : α → Option (PanValue α)) (callFfi : FfiState σ)
    (name : VarName) (shape : Shape) (value : PanValue α)
    (function : FunName) (arguments : List (Exp α)) (body : Prog α)
    (oldValue : Option (PanValue α))
    (clockBodyOutcome : PanValueFfiClockOutcome α σ)
    (stepBodyResult : PanValueFfiControlResult α σ)
    (callSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hcallClock : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock none function
      arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.returned callLocals callGlobals callMemory callFfi [value]), callClock))
    (hcallSteps : evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi none function
      arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.returned callLocals callGlobals callMemory callFfi [value], callSteps))
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hbodyClock : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
      callGlobals callMemory callFfi callClock body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (clockBodyOutcome, finalClock))
    (hbodySteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
      callGlobals callMemory callFfi body (memoryAccess := memoryAccess)
      (contracts := contracts) = some (stepBodyResult, bodySteps))
    (hold : locals name = oldValue) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body)
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (panValueFfiClockRestoreLocal name oldValue clockBodyOutcome, finalClock) ∧
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.decCall name shape function arguments body)
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (restorePanValueFfiLocal name oldValue stepBodyResult,
        callSteps + bodySteps + 1) := by
  constructor
  · simp [evalPanValueFfiClockProg, hcallClock, hshape, hbodyClock, hold]
  · simp [evalPanValueFfiProgSteps, hcallSteps, hshape, hbodySteps, hold]

end Flapjack
