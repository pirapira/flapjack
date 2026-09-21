import Flapjack.PanValueFfiClockCorrectness
import Flapjack.PanSimpEvaluate
import Flapjack.PanObservationalSemantics
import Flapjack.PanToCrepCorrectnessBoundary

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

/-! The declaration-boundary timeout case preserves the initial event prefix
    just like the normal and raised call cases. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_timeout_call_ioEvents_prefix
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
      some (.timeout (fun _ => none) globals memory ffi, nextClock))
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) globals memory ffi, nextClock) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProgram_of_declarations_and_timeout_call context
      initial clock primitive handler fuel declarations entry arguments state globals
      memory ffi nextClock (memoryAccess := memoryAccess)
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

theorem evalPanValueFfiClockProgram_of_declarations_and_returned_call_ioEvents_prefix
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
      some (.control (.returned locals globals memory ffi [value]), nextClock))
    (hentry : lookupInfo entry state.returnShapes = some shape)
    (hshape : panShapeMatches (panValueShape state.structs value) shape = true)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.returned locals globals memory ffi [value]), nextClock) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProgram_of_declarations_and_returned_call
      context initial clock primitive handler fuel declarations entry arguments
      state shape locals globals memory ffi value nextClock
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
      hdeclarations hcall hentry hshape
  · exact hprefix

theorem evalPanValueFfiClockProgram_of_declarations_and_returned_call_result_rel
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α) (targetValues : List α)
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
      some (.control (.returned locals globals memory ffi [value]), nextClock))
    (hentry : lookupInfo entry state.returnShapes = some shape)
    (hshape : panShapeMatches (panValueShape state.structs value) shape = true)
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState)
    (hvalues : panValueCrepValuesRel [value] targetValues) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.returned locals globals memory ffi [value]), nextClock) ∧
    panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
      globalsLookup
      (.returned locals globals memory [value])
      (.returned targetState targetValues) := by
  have hprogram := evalPanValueFfiClockProgram_of_declarations_and_returned_call
    context initial clock primitive handler fuel declarations entry arguments
    state shape locals globals memory ffi value nextClock
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hcall hentry hshape
  refine ⟨hprogram, ?_⟩
  simp [panValuePcResultRel, hstate, hvalues]

theorem evalPanValueFfiClockProgram_of_declarations_and_raised_call_result_rel
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
    (exception : ExceptionId) (value : PanValue α) (nextClock : Nat)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α) (targetException : α)
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
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState)
    (hresult : panValuePcExceptionResultRel state.structs pcContext exceptionRel
      exceptionCode globalsLookup globals memory exception value targetState
      targetException) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock) ∧
    panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
      globalsLookup
      (.raised locals globals memory exception value)
      (.raised targetState targetException) := by
  have hprogram := evalPanValueFfiClockProgram_of_declarations_and_raised_call
    context initial clock primitive handler fuel declarations entry arguments
    state globals memory ffi exception value nextClock
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hcall
  refine ⟨hprogram, ?_⟩
  exact (panValuePcResultRel_raised_iff state.structs pcContext exceptionRel
    exceptionCode globalsLookup locals globals memory exception value targetState
    targetException).2 ⟨hstate, hresult⟩

theorem evalPanValueFfiClockProgram_of_declarations_and_raised_call_context_code
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
    (exception : ExceptionId) (value : PanValue α) (nextClock : Nat)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α) (targetException : α)
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
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState)
    (hresult : panValuePcExceptionResultRel state.structs pcContext exceptionRel
      exceptionCode globalsLookup globals memory exception value targetState
      targetException)
    (hlookup : lookupInfo exception pcContext.exceptions = some targetException) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock) ∧
    panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
      exceptionCode globalsLookup
      (.raised locals globals memory exception value)
      (.raised targetState targetException) := by
  have hprogram := evalPanValueFfiClockProgram_of_declarations_and_raised_call
    context initial clock primitive handler fuel declarations entry arguments
    state globals memory ffi exception value nextClock
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hcall
  have hrel := (panValuePcResultRel_raised_iff state.structs pcContext exceptionRel
    exceptionCode globalsLookup locals globals memory exception value targetState
    targetException).2 ⟨hstate, hresult⟩
  refine ⟨hprogram, ?_⟩
  exact panValuePcResultRelWithContextCode_raised_of_rel_and_lookup
    state.structs pcContext exceptionRel exceptionCode globalsLookup locals globals
    memory exception value targetState targetException hrel hlookup

theorem evalPanValueFfiClockProg_decCall_returned_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock callClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (calleeLocals : VarName → Option (PanValue α))
    (value : PanValue α) (outcome : PanValueFfiClockOutcome α σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.returned calleeLocals nextGlobals nextMemory nextFfi
        [value]), callClock))
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel
      (updatePanValueMap locals name value) nextGlobals nextMemory nextFfi
      callClock body = some (outcome, finalClock))
    (hprefix : ffi.ioEvents <+: (panResultFfi
      (panValueFfiClockRestoreLocal name (locals name) outcome, finalClock)).ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (panValueFfiClockRestoreLocal name (locals name) outcome, finalClock) ∧
      ffi.ioEvents <+: (panResultFfi
        (panValueFfiClockRestoreLocal name (locals name) outcome, finalClock)).ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_decCall_returned context primitive handler
      structs functions baseAddress topAddress bytesInWord fuel clock callClock
      finalClock locals globals memory ffi name shape function arguments body
      calleeLocals nextGlobals nextMemory nextFfi value outcome hcall hshape hbody
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

theorem evalPanValueFfiClockProg_while_broke_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock bodyClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (bodyLocals bodyGlobals : VarName → Option (PanValue α))
    (bodyMemory : α → Option (PanValue α)) (bodyFfi : FfiState σ)
    (conditionValue : α) (condition : Exp α) (body : Prog α)
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
      some (.control (.broke bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock))
    (hbodyPrefix : ffi.ioEvents <+: bodyFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock) ∧
      ffi.ioEvents <+: bodyFfi.ioEvents := by
  constructor
  · simp [evalPanValueFfiClockProg, hcondition, hconditionNonzero, hclock, hbody]
  · exact hbodyPrefix

theorem evalPanValueFfiClockProg_while_continued_iteration_ioEvents_prefix
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
      some (.control (.continued bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock))
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
  · simp [evalPanValueFfiClockProg, hcondition, hconditionNonzero, hclock,
      hbody, hrest]
  · exact hbodyPrefix.trans hrestPrefix

/-! Cake's zero-clock `While` timeout is terminal and therefore preserves the
    incoming event trace unchanged. -/
theorem evalPanValueFfiClockProg_while_timeout_ioEvents_prefix
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (condition : Exp α) (body : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (conditionValue : α)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    (hclock : (clock == (0 : Nat)) = true) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) globals memory ffi, clock) ∧
      ffi.ioEvents <+: ffi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_while_timeout_some context primitive handler
      structs functions baseAddress topAddress bytesInWord fuel locals globals
      memory ffi clock condition body memoryAccess contracts memoryHandler
      conditionValue hcondition hconditionNonzero hclock
  · exact List.prefix_refl _

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

/-! A terminal first `Seq` component is returned without evaluating the second
    component, while preserving the incoming FFI event prefix. -/
theorem evalPanValueFfiClockProg_seq_terminal_ioEvents_prefix
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
    (clock : Nat) (first second : Prog α)
    (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hfirst : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (outcome, nextClock))
    (hterminal : ∀ l g m f, outcome ≠ .control (.normal l g m f))
    (hprefix : ffi.ioEvents <+: (panResultFfi (outcome, nextClock)).ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      clock (.seq first second) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, nextClock) ∧
      ffi.ioEvents <+: (panResultFfi (outcome, nextClock)).ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_seq_terminal_some context primitive handler
      structs functions baseAddress topAddress bytesInWord fuel locals globals
      memory ffi clock first second outcome nextClock memoryAccess contracts
      memoryHandler hfirst hterminal
  · exact hprefix

/-! Call-aware terminal `Seq` propagation uses the shared `progCallFuel`
    budget and still does not evaluate the second component. -/
theorem evalPanValueFfiClockProg_seq_terminal_ioEvents_prefix_progCallFuel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (callBudget : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (first second : Prog α)
    (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (hfirst : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord
      (progCallFuel callBudget first + progCallFuel callBudget second)
      locals globals memory ffi clock first (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, nextClock))
    (hterminal : ∀ l g m f, outcome ≠ .control (.normal l g m f))
    (hprefix : ffi.ioEvents <+: (panResultFfi (outcome, nextClock)).ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord
      (progCallFuel callBudget (.seq first second)) locals globals memory ffi clock
      (.seq first second) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, nextClock) ∧
      ffi.ioEvents <+: (panResultFfi (outcome, nextClock)).ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_seq_terminal_some_progCallFuel context
      primitive handler structs functions baseAddress topAddress bytesInWord
      callBudget locals globals memory ffi clock first second outcome nextClock
      memoryAccess contracts memoryHandler hfirst hterminal
  · exact hprefix

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

/-! Cake's direct-call timeout branch preserves the incoming event trace while
    retaining the callee's timeout state. -/
theorem evalPanValueFfiClockProg_call_timeout_ioEvents_prefix
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
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      info function arguments =
      some (.timeout nextLocals nextGlobals nextMemory nextFfi, callClock))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call info function arguments) =
      some (.timeout nextLocals nextGlobals nextMemory nextFfi, callClock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_call_timeout context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock callClock locals globals
      memory ffi info function arguments nextLocals nextGlobals nextMemory nextFfi hcall
  · exact hprefix

/-! Cake's direct-call terminal FFI branch preserves the incoming event trace
    and returns the callee's final event unchanged. -/
theorem evalPanValueFfiClockProg_call_finalFfi_ioEvents_prefix
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
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      info function arguments =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call info function arguments) =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_call_finalFfi context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock callClock locals globals
      memory ffi info function arguments nextLocals nextGlobals nextMemory nextFfi
      event hcall
  · exact hprefix

theorem evalPanValueFfiClockProg_extCall_memoryHandler_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat) (locals globals : VarName → Option (PanValue α))
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
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.extCall function (.const configuration) (.const configurationLength)
          (.const array) (.const arrayLength)) access contracts (some memoryHandler) =
      some (.control (.normal nextLocals globals nextMemory nextFfi), clock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  obtain ⟨hstep, hprefix⟩ :=
    evalPanValueFfiProgSteps_extCall_memoryHandler_ioEvents_prefix context
      primitive handler structs functions baseAddress topAddress bytesInWord 0 locals
      globals memory ffi function configuration configurationLength array arrayLength
      access contracts memoryHandler nextLocals nextMemory nextFfi expressionSteps
      hvalues hhandler hpreserves
  exact ⟨evalPanValueFfiClockProg_leaf_some context primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
    (.extCall function (.const configuration) (.const configurationLength)
      (.const array) (.const arrayLength)) access contracts (some memoryHandler)
    (PanValueFfiLeafProg.extCall function (.const configuration)
      (.const configurationLength) (.const array) (.const arrayLength))
    (.normal nextLocals globals nextMemory nextFfi) (expressionSteps + 1) hstep,
    hprefix⟩

theorem evalPanValueFfiClockProg_extCall_statefulHandler_ioEvents_prefix
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
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      clock (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength)) none contracts none =
      some (.control (.normal nextLocals globals memory nextFfi), clock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  obtain ⟨hstep, hprefix⟩ :=
    evalPanValueFfiProgSteps_extCall_statefulHandler_ioEvents_prefix context
      primitive statefulHandler structs functions baseAddress topAddress bytesInWord 0
      locals globals memory ffi function configuration configurationLength array arrayLength
      contracts nextLocals nextFfi expressionSteps hvalues hhandler hpreserves
  exact ⟨evalPanValueFfiClockProg_leaf_some context primitive statefulHandler structs
    functions baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
    (.extCall function (.const configuration) (.const configurationLength)
      (.const array) (.const arrayLength)) none contracts none
    (PanValueFfiLeafProg.extCall function (.const configuration)
      (.const configurationLength) (.const array) (.const arrayLength))
    (.normal nextLocals globals memory nextFfi) (expressionSteps + 1) hstep,
    hprefix⟩

end Flapjack
