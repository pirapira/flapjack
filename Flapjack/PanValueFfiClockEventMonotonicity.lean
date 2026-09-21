import Flapjack.PanValueFfiClockCorrectness
import Flapjack.PanObservationalSemantics

namespace Flapjack

def panValueFfiMemoryHandlerPreservesIoEvents
    (memoryHandler : PanValueMemoryFfiHandler α σ) : Prop :=
  ∀ (function : FunName) (configuration configurationLength array arrayLength : α)
    (locals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (nextLocals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ),
    memoryHandler function configuration configurationLength array arrayLength
      locals memory ffi = some (nextLocals, nextMemory, nextFfi) →
    ffi.ioEvents <+: nextFfi.ioEvents

def panValueFfiStatefulHandlerPreservesIoEvents
    (statefulHandler : PanValueStatefulFfiHandler α σ) : Prop :=
  ∀ (function : FunName) (configuration configurationLength array arrayLength : α)
    (locals : VarName → Option (PanValue α)) (ffi : FfiState σ)
    (nextLocals : VarName → Option (PanValue α)) (nextFfi : FfiState σ),
    statefulHandler function configuration configurationLength array arrayLength
      locals ffi = some (nextLocals, nextFfi) →
    ffi.ioEvents <+: nextFfi.ioEvents

theorem evalPanValueFfiClockProg_shMemStore_normal_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (size : OpSize) (address value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (steps : Nat)
    (hresult : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi
      (.shMemStore size address value) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.normal nextLocals nextGlobals nextMemory nextFfi, steps))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.shMemStore size address value) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.normal nextLocals nextGlobals nextMemory nextFfi), clock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf, hresult]
  · exact hprefix

theorem evalPanValueFfiClockProg_shMemLoad_normal_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (steps : Nat)
    (hresult : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi
      (.shMemLoad size kind name address) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.normal nextLocals nextGlobals nextMemory nextFfi, steps))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.shMemLoad size kind name address) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.normal nextLocals nextGlobals nextMemory nextFfi), clock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf, hresult]
  · exact hprefix

theorem evalPanValueFfiClockProgram_of_declarations_and_raised_call_ioEvents_prefix
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
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
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
        nextClock))
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProgram_of_declarations_and_raised_call context initial
      clock primitive handler fuel declarations entry arguments state globals memory ffi
      exception value nextClock (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) hdeclarations hcall
  · exact hprefix

theorem evalPanValueFfiClockProg_decCall_raised_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock callClock : Nat)
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
        exception value), callClock))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_decCall_raised context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock callClock locals globals
      memory ffi name shape function arguments body nextGlobals nextMemory nextFfi
      exception value hcall
  · exact hprefix

theorem evalPanValueFfiClockProg_while_normal_iteration_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock bodyClock finalClock : Nat)
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
      (contracts := contracts) = some (outcome, finalClock))
    (hbodyPrefix : ffi.ioEvents <+: bodyFfi.ioEvents)
    (hrestPrefix : bodyFfi.ioEvents <+:
      (panResultFfi (outcome, finalClock)).ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) = some (outcome, finalClock) ∧
      ffi.ioEvents <+: (panResultFfi (outcome, finalClock)).ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_while_normal_iteration context primitive handler
      structs functions baseAddress topAddress bytesInWord fuel clock bodyClock finalClock
      locals globals memory ffi bodyLocals bodyGlobals bodyMemory bodyFfi conditionValue
      condition body outcome (memoryAccess := memoryAccess) (contracts := contracts)
      hcondition hconditionNonzero hclock hbody hrest
  · exact hbodyPrefix.trans hrestPrefix

theorem evalPanValueFfiClockProg_seq_normal_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock firstClock finalClock : Nat)
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
        (contracts := contracts) = some (outcome, finalClock))
    (hfirstPrefix : ffi.ioEvents <+: middleFfi.ioEvents)
    (hsecondPrefix : middleFfi.ioEvents <+:
      (panResultFfi (outcome, finalClock)).ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.seq first second) (memoryAccess := memoryAccess)
        (contracts := contracts) = some (outcome, finalClock) ∧
      ffi.ioEvents <+: (panResultFfi (outcome, finalClock)).ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_seq_normal context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock firstClock finalClock
      locals globals memory ffi middleLocals middleGlobals middleMemory middleFfi
      first second outcome (memoryAccess := memoryAccess) (contracts := contracts)
      hfirst hsecond
  · exact hfirstPrefix.trans hsecondPrefix

theorem evalPanValueFfiProgSteps_extCall_memoryHandler_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : PanValueMemoryFfiHandler α σ)
    (nextLocals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (expressionSteps : Nat)
    (hvalues : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord
      [.const configuration, .const configurationLength,
        .const array, .const arrayLength]
      (memoryAccess := access) =
      some ([.word configuration, .word configurationLength,
        .word array, .word arrayLength], expressionSteps))
    (hhandler : memoryHandler function configuration configurationLength
      array arrayLength locals memory ffi =
      some (nextLocals, nextMemory, nextFfi))
    (hpreserves : panValueFfiMemoryHandlerPreservesIoEvents memoryHandler) :
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength))
      (memoryAccess := access) (contracts := contracts)
      (memoryHandler := some memoryHandler) =
      some (.normal nextLocals globals nextMemory nextFfi, expressionSteps + 1) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiProgSteps_extCall_memoryHandler context primitive handler
      structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
      function configuration configurationLength array arrayLength access contracts
      memoryHandler nextLocals nextMemory nextFfi expressionSteps hvalues hhandler
  · exact hpreserves function configuration configurationLength array arrayLength
      locals memory ffi nextLocals nextMemory nextFfi hhandler

theorem evalPanValueFfiProgSteps_extCall_statefulHandler_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (statefulHandler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (contracts : Option PanValueCallContracts)
    (nextLocals : VarName → Option (PanValue α)) (nextFfi : FfiState σ)
    (expressionSteps : Nat)
    (hvalues : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord
      [.const configuration, .const configurationLength,
        .const array, .const arrayLength]
      (memoryAccess := none) =
      some ([.word configuration, .word configurationLength,
        .word array, .word arrayLength], expressionSteps))
    (hhandler : statefulHandler function configuration configurationLength
      array arrayLength locals ffi = some (nextLocals, nextFfi))
    (hpreserves : panValueFfiStatefulHandlerPreservesIoEvents statefulHandler) :
    evalPanValueFfiProgSteps context primitive statefulHandler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength))
      (memoryAccess := none) (contracts := contracts) (memoryHandler := none) =
      some (.normal nextLocals globals memory nextFfi, expressionSteps + 1) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · simp [evalPanValueFfiProgSteps, hvalues, hhandler]
  · exact hpreserves function configuration configurationLength array arrayLength
      locals ffi nextLocals nextFfi hhandler

theorem evalPanValueFfiClockProg_extCall_statefulHandler_normal_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (statefulHandler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (contracts : Option PanValueCallContracts)
    (nextLocals : VarName → Option (PanValue α)) (nextFfi : FfiState σ)
    (expressionSteps : Nat)
    (hvalues : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord
      [.const configuration, .const configurationLength,
        .const array, .const arrayLength]
      (memoryAccess := none) =
      some ([.word configuration, .word configurationLength,
        .word array, .word arrayLength], expressionSteps))
    (hhandler : statefulHandler function configuration configurationLength
      array arrayLength locals ffi = some (nextLocals, nextFfi))
    (hpreserves : panValueFfiStatefulHandlerPreservesIoEvents statefulHandler) :
    evalPanValueFfiClockProg context primitive statefulHandler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength))
      (memoryAccess := none) (contracts := contracts) (memoryHandler := none) =
      some (.control (.normal nextLocals globals memory nextFfi), clock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  have hsteps := evalPanValueFfiProgSteps_extCall_statefulHandler_ioEvents_prefix
    context primitive statefulHandler structs functions baseAddress topAddress
    bytesInWord 0 locals globals memory ffi function configuration
    configurationLength array arrayLength contracts nextLocals nextFfi
    expressionSteps hvalues hhandler hpreserves
  constructor
  · simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf, hsteps.1]
  · exact hsteps.2

theorem evalPanValueFfiClockProg_call_returned_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName) (arguments : List (Exp α))
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (values : List (PanValue α))
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.returned (fun _ => none) nextGlobals nextMemory nextFfi values),
        callClock))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call none function arguments) =
      some (.control (.returned (fun _ => none) nextGlobals nextMemory nextFfi values),
        callClock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_call_returned context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock callClock locals globals
      memory ffi function arguments nextGlobals nextMemory nextFfi hcall
  · exact hprefix

theorem evalPanValueFfiClockProg_call_raised_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock callClock : Nat)
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
        exception value), callClock))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call none function arguments) =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_call_raised context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock callClock locals globals
      memory ffi function arguments nextGlobals nextMemory nextFfi exception value hcall
  · exact hprefix

end Flapjack
