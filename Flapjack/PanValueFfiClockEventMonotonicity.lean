import Flapjack.PanValueFfiClockCorrectness
import Flapjack.PanSimpEvaluate
import Flapjack.PanObservationalSemantics
import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.PanValueFfiEventMonotonicity
import Flapjack.PanProgramSimp

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

theorem evalPanValueFfiClockProgram_of_declarations_and_returned_call_result_rel_ioEvents_prefix
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
    (hvalues : panValueCrepValuesRel [value] targetValues)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.returned locals globals memory ffi [value]), nextClock) ∧
    panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
      globalsLookup
      (.returned locals globals memory [value])
      (.returned targetState targetValues) ∧
    initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hrel := evalPanValueFfiClockProgram_of_declarations_and_returned_call_result_rel
    context initial clock primitive handler fuel declarations entry arguments state shape
    locals globals memory ffi value nextClock pcContext exceptionRel exceptionCode
    globalsLookup targetState targetValues
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hcall hentry hshape hstate hvalues
  exact ⟨hrel.1, hrel.2, hprefix⟩

/-! Preserve the full Cake context relation at the returned declaration-call
    boundary.  This is the context-coded counterpart of the flattened bridge
    above: return-shape lookup, value-shape matching, evaluator evidence, and
    the FFI event prefix remain explicit while the result carries the bundled
    no-overlap/ctxt-max state relation. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_returned_call_result_rel_with_context_code_ioEvents_prefix
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
    (hstate : panValueCrepStateRelWithContext state.structs pcContext locals globals
      memory targetState)
    (hvalues : panValueCrepValuesRel [value] targetValues)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.returned locals globals memory ffi [value]), nextClock) ∧
    panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
      exceptionCode globalsLookup
      (.returned locals globals memory [value])
      (.returned targetState targetValues) ∧
    initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hrel := evalPanValueFfiClockProgram_of_declarations_and_returned_call_result_rel
    context initial clock primitive handler fuel declarations entry arguments state shape
    locals globals memory ffi value nextClock pcContext exceptionRel exceptionCode
    globalsLookup targetState targetValues
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hcall hentry hshape hstate.2.2 hvalues
  have hcontextRel :
      panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
        exceptionCode globalsLookup
        (.returned locals globals memory [value])
        (.returned targetState targetValues) := by
    exact (panValuePcResultRelWithContextCode_returned_iff state.structs pcContext
      exceptionRel exceptionCode globalsLookup locals globals memory [value]
      targetState targetValues).2 ⟨hstate.2.2, hvalues⟩
  exact ⟨hrel.1, hcontextRel, hprefix⟩

/-! The terminal-FFI branch of the declaration boundary carries the same
    state relation as the source result and preserves the final event.  This
    is the explicit `Call_FinalFFI` result-relation case needed by the Cake
    `state_rel_imp_semantics_decls_to_crep` induction. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_finalFfi_call_result_rel_ioEvents_prefix
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α) (targetEvent : FfiFinalEvent)
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
      some (.control (.finalFfi locals globals memory ffi event), nextClock))
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState)
    (hevent : event = targetEvent)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi locals globals memory ffi event), nextClock) ∧
    panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
      globalsLookup
      (.finalFfi locals globals memory event)
      (.finalFfi targetState targetEvent) ∧
    initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hprogram := evalPanValueFfiClockProgram_of_declarations_and_finalFfi_call
    context initial clock primitive handler fuel declarations entry arguments state
    locals globals memory ffi event nextClock
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hcall
  refine ⟨hprogram, ?_, hprefix⟩
  exact (panValuePcResultRel_finalFfi_iff state.structs pcContext exceptionRel
    exceptionCode globalsLookup locals globals memory event targetState targetEvent).2
    ⟨hstate, hevent⟩

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

theorem evalPanValueFfiClockProgram_of_declarations_and_raised_call_result_rel_ioEvents_prefix
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
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock) ∧
    panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
      globalsLookup
      (.raised locals globals memory exception value)
      (.raised targetState targetException) ∧
    initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hrel := evalPanValueFfiClockProgram_of_declarations_and_raised_call_result_rel
    context initial clock primitive handler fuel declarations entry arguments state
    locals globals memory ffi exception value nextClock pcContext exceptionRel
    exceptionCode globalsLookup targetState targetException
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hcall hstate hresult
  exact ⟨hrel.1, hrel.2, hprefix⟩

/-! The raised-call counterpart composes the declaration evaluator with the
    concrete raised result relation.  The target declaration state is produced
    by evaluating the Cake `pan_simp` declarations, rather than being supplied
    as an unconnected relation premise; this is the declaration/evaluator
    boundary used by `state_rel_imp_semantics_decls_to_crep`. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_raised_call_result_rel_ioEvents_prefix
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
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
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
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.raised (fun _ => none) globals memory ffi exception value),
          nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup
        (.raised locals globals memory exception value)
        (.raised targetState targetException) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel⟩ :=
    panValueProgramStateRel_evalPanValueDeclarations
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations
  have hraised :=
    evalPanValueFfiClockProgram_of_declarations_and_raised_call_result_rel
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi exception value nextClock pcContext exceptionRel
      exceptionCode globalsLookup targetState targetException
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
      hdeclarations hcall hstate hresult
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel,
    hraised.1, hraised.2, hprefix⟩

/-! The ordinary normal-call branch completes the declaration-boundary
    composition used by Cake's `state_rel_imp_semantics_decls_to_crep`.  The
    source state relation is retained at the result boundary, while the
    declaration evaluator, call evaluator, and incoming FFI-event prefix are
    all explicit premises. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_normal_call_result_rel_ioEvents_prefix
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
    (nextClock : Nat)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), nextClock))
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), nextClock) ∧
    panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
      globalsLookup
      (.normal locals globals memory)
      (.normal targetState) ∧
    initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hprogram := evalPanValueFfiClockProgram_of_declarations_and_call
    context initial clock primitive handler fuel declarations entry arguments state
    (.control (.normal locals globals memory ffi)) nextClock
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hentry hcall
  refine ⟨hprogram, ?_, ?_⟩
  · exact (panValuePcResultRel_normal_iff state.structs pcContext exceptionRel
      exceptionCode globalsLookup locals globals memory targetState).2 hstate
  · exact hprefix

/-! The declaration-state counterpart transports the initial source/target
    relation through the actual declaration evaluators before applying the
    normal-call result bridge.  The evaluator, lookup, result, and event
    premises remain explicit, matching the normal branch of Cake's
    `state_rel_imp_semantics_decls_to_crep`. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_normal_call_result_rel_ioEvents_prefix
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
    (nextClock : Nat)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), nextClock))
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupInfo entry targetDeclaration.returnShapes = none ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.normal locals globals memory ffi), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.normal locals globals memory) (.normal targetState) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel⟩ :=
    panValueProgramStateRel_evalPanValueDeclarations
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations
  rcases hpostRel with ⟨_hstructs, _hglobals, _hmemory, hreturnShapes,
    _hparameterShapes, _hexceptions, _hbaseAddress, _htopAddress, _hbytesInWord,
    _hfunctions⟩
  have htargetEntry : lookupInfo entry targetDeclaration.returnShapes = none := by
    rw [← hreturnShapes]
    exact hentry
  have hnormal :=
    evalPanValueFfiClockProgram_of_declarations_and_normal_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState memoryAccess memoryHandler
      hdeclarations hentry hcall hstate hprefix
  exact ⟨targetDeclaration, htargetDeclarations,
    ⟨_hstructs, _hglobals, _hmemory, hreturnShapes, _hparameterShapes,
      _hexceptions, _hbaseAddress, _htopAddress, _hbytesInWord, _hfunctions⟩,
    htargetEntry,
    hnormal.1, hnormal.2.1, hnormal.2.2⟩

/-! The normal declaration bridge also has a context-preserving form without
    requiring a callee-body lookup.  This is the direct state-relation step
    needed when the enclosing `state_rel_imp_semantics_to_crep` induction has
    already established the call result but not the stronger declaration
    adequacy facts. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_normal_call_result_rel_ioEvents_prefix_with_context
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
    (nextClock : Nat)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), nextClock))
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      locals globals memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupInfo entry targetDeclaration.returnShapes = none ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.normal locals globals memory ffi), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.normal locals globals memory) (.normal targetState) ∧
      panValueCrepStateRelWithContext state.structs pcContext locals globals
        memory targetState ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hstate := panValueCrepStateRelWithContext_to_stateRel
    state.structs pcContext locals globals memory targetState hstateContext
  have hnormal :=
    evalPanValueFfiClockProgram_of_related_declarations_and_normal_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState memoryAccess memoryHandler targetInitial
      hinitial hdeclarations hentry hcall hstate hprefix
  rcases hnormal with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetEntry, hprogram, hresult, hprefix'⟩
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetEntry,
    hprogram, hresult, hstateContext, hprefix'⟩

/-! The adequacy-strengthened normal branch exposes the declaration facts needed
    by the subsequent `state_rel` induction: the transformed callee body and
    exception table are returned alongside the clocked evaluator result. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_normal_call_result_rel_adequacy
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
    (nextClock : Nat)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), nextClock))
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      lookupInfo entry targetDeclaration.returnShapes = none ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.normal locals globals memory ffi), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.normal locals globals memory) (.normal targetState) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions⟩ :=
    panValueProgramStateRel_evalDeclarations_adequacy
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations entry hfunction
  rcases hpostRel with ⟨hstructs, hglobals, hmemory, hreturnShapes,
    hparameterShapes, hexceptions, hbaseAddress, htopAddress, hbytesInWord,
    hfunctions⟩
  have htargetEntry : lookupInfo entry targetDeclaration.returnShapes = none := by
    rw [← hreturnShapes]
    exact hentry
  have hnormal :=
    evalPanValueFfiClockProgram_of_declarations_and_normal_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState memoryAccess memoryHandler
      hdeclarations hentry hcall hstate hprefix
  exact ⟨targetDeclaration, htargetDeclarations,
    ⟨hstructs, hglobals, hmemory, hreturnShapes, hparameterShapes, hexceptions,
      hbaseAddress, htopAddress, hbytesInWord, hfunctions⟩,
    htargetFunction, htargetExceptions, htargetEntry,
    hnormal.1, hnormal.2.1, hnormal.2.2⟩

/-! The normal-call adequacy branch also preserves Cake's strengthened
    declaration-state relation.  This is the normal counterpart of the
    returned-call context bridge and is the state-rel induction's concrete
    declaration step. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_normal_call_result_rel_adequacy_with_context
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
    (nextClock : Nat)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), nextClock))
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      locals globals memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      lookupInfo entry targetDeclaration.returnShapes = none ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.normal locals globals memory ffi), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.normal locals globals memory) (.normal targetState) ∧
      panValueCrepStateRelWithContext state.structs pcContext locals globals
        memory targetState ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hstate := panValueCrepStateRelWithContext_to_stateRel
    state.structs pcContext locals globals memory targetState hstateContext
  have hnormal :=
    evalPanValueFfiClockProgram_of_related_declarations_and_normal_call_result_rel_adequacy
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState memoryAccess memoryHandler targetInitial
      hinitial hdeclarations hfunction hentry hcall hstate hprefix
  rcases hnormal with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions, htargetEntry, hprogram, hresult, hprefix'⟩
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetFunction,
    htargetExceptions, htargetEntry, hprogram, hresult, hstateContext, hprefix'⟩

/-! The normal declaration-call adequacy also has a context-preserving form.
    This is the normal branch needed by the `state_rel_imp_semantics_to_crep`
    induction: declaration evaluation and the transformed callee are retained,
    while the stronger context state relation remains available to the caller. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_normal_call_context_code_adequacy
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
    (nextClock : Nat)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), nextClock))
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      locals globals memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      lookupInfo entry targetDeclaration.returnShapes = none ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.normal locals globals memory ffi), nextClock) ∧
      panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
        exceptionCode globalsLookup
        (.normal locals globals memory) (.normal targetState) ∧
      panValueCrepStateRelWithContext state.structs pcContext locals globals
        memory targetState ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hstate := panValueCrepStateRelWithContext_to_stateRel
    state.structs pcContext locals globals memory targetState hstateContext
  have hnormal :=
    evalPanValueFfiClockProgram_of_related_declarations_and_normal_call_result_rel_adequacy
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState memoryAccess memoryHandler targetInitial
      hinitial hdeclarations hfunction hentry hcall hstate hprefix
  rcases hnormal with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions, htargetEntry, hprogram, hresult, hprefix'⟩
  have hcontextResult :=
    (panValuePcResultRelWithContextCode_normal_iff state.structs pcContext
      exceptionRel exceptionCode globalsLookup locals globals memory targetState).2 hstate
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetFunction,
    htargetExceptions, htargetEntry, hprogram, hcontextResult, hstateContext,
    hprefix'⟩

/-! The raised adequacy branch exposes the same declaration-state facts while
    retaining the explicit exception payload and result relation. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_raised_call_result_rel_adequacy
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
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
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
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.raised (fun _ => none) globals memory ffi exception value),
          nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.raised locals globals memory exception value)
        (.raised targetState targetException) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions⟩ :=
    panValueProgramStateRel_evalDeclarations_adequacy
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations entry hfunction
  rcases hpostRel with ⟨hstructs, hglobals, hmemory, hreturnShapes,
    hparameterShapes, hexceptions, hbaseAddress, htopAddress, hbytesInWord,
    hfunctions⟩
  have hraised :=
    evalPanValueFfiClockProgram_of_declarations_and_raised_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi exception value nextClock pcContext exceptionRel
      exceptionCode globalsLookup targetState targetException memoryAccess memoryHandler
      hdeclarations hcall hstate hresult hprefix
  exact ⟨targetDeclaration, htargetDeclarations,
    ⟨hstructs, hglobals, hmemory, hreturnShapes, hparameterShapes, hexceptions,
      hbaseAddress, htopAddress, hbytesInWord, hfunctions⟩,
    htargetFunction, htargetExceptions,
    hraised.1, hraised.2.1, hraised.2.2⟩

/-! The raised-call adequacy branch also preserves Cake's strengthened
    declaration-state relation.  This is the raised counterpart of the
    normal and returned declaration bridges consumed by the
    `state_rel_imp_semantics_decls_to_crep` induction. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_raised_call_result_rel_adequacy_with_context
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
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock))
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      locals globals memory targetState)
    (hresult : panValuePcExceptionResultRel state.structs pcContext exceptionRel
      exceptionCode globalsLookup globals memory exception value targetState
      targetException)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.raised (fun _ => none) globals memory ffi exception value),
          nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.raised locals globals memory exception value)
        (.raised targetState targetException) ∧
      panValueCrepStateRelWithContext state.structs pcContext locals globals
        memory targetState ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hstate := panValueCrepStateRelWithContext_to_stateRel
    state.structs pcContext locals globals memory targetState hstateContext
  have hraised :=
    evalPanValueFfiClockProgram_of_related_declarations_and_raised_call_result_rel_adequacy
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi exception value nextClock pcContext exceptionRel
      exceptionCode globalsLookup targetState targetException memoryAccess memoryHandler
      targetInitial hinitial hdeclarations hfunction hcall hstate hresult hprefix
  rcases hraised with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions, hprogram, hresult', hprefix'⟩
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetFunction,
    htargetExceptions, hprogram, hresult', hstateContext, hprefix'⟩

/-! The timeout counterpart composes the declaration evaluator with the
    clocked call boundary and the concrete `state_rel` result relation.  This
    is the timeout branch of Cake's `state_rel_imp_semantics_decls_to_crep`:
    declaration setup is evaluated first, then the zero-clock call result is
    transported without weakening the source/target memory and locals state
    obligation. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_timeout_call_result_rel_ioEvents_prefix
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
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
    (hstate : panValueCrepStateRel state.structs pcContext (fun _ => none)
      globals memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) globals memory ffi, nextClock) ∧
    initial.ffi.ioEvents <+: ffi.ioEvents ∧
    panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
      globalsLookup
      (.timeout (fun _ => none) globals memory)
      (.timeout targetState) := by
  have hprogram := evalPanValueFfiClockProgram_of_declarations_and_timeout_call_ioEvents_prefix
    context initial clock primitive handler fuel declarations entry arguments state globals
    memory ffi nextClock (memoryAccess := memoryAccess)
    (memoryHandler := memoryHandler) hdeclarations hcall hprefix
  refine ⟨hprogram.1, hprogram.2, ?_⟩
  exact (panValuePcResultRel_timeout_iff state.structs pcContext exceptionRel
    exceptionCode globalsLookup (fun _ => none) globals memory targetState).2 hstate

/-! The timeout branch also transports a related initial source/target
    declaration state.  This is the corresponding declaration-boundary case
    of Cake's `state_rel_imp_semantics_decls_to_crep` induction. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_timeout_call_result_rel_ioEvents_prefix
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
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
    (hstate : panValueCrepStateRel state.structs pcContext (fun _ => none)
      globals memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.timeout (fun _ => none) globals memory ffi, nextClock) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup
        (.timeout (fun _ => none) globals memory)
        (.timeout targetState) := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel⟩ :=
    panValueProgramStateRel_evalPanValueDeclarations
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations
  have htimeout :=
    evalPanValueFfiClockProgram_of_declarations_and_timeout_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state globals
      memory ffi nextClock pcContext exceptionRel exceptionCode globalsLookup targetState
      memoryAccess memoryHandler hdeclarations hcall hstate hprefix
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htimeout.1, htimeout.2.1, htimeout.2.2⟩

/-! The timeout declaration branch also retains the exception-table equality
    from the post-declaration `state_rel`.  This is the concrete timeout case
    consumed by Cake's `state_rel_imp_semantics_to_crep` induction: it
    transports the declaration evaluator, then composes the timeout result
    relation without dropping the declaration-state facts. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_timeout_call_result_rel_adequacy
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
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
    (hstate : panValueCrepStateRel state.structs pcContext (fun _ => none)
      globals memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      state.exceptions = targetDeclaration.exceptions ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.timeout (fun _ => none) globals memory ffi, nextClock) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup
        (.timeout (fun _ => none) globals memory)
        (.timeout targetState) := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel⟩ :=
    panValueProgramStateRel_evalPanValueDeclarations
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations
  rcases hpostRel with ⟨hstructs, hglobals, hmemory, hreturnShapes,
    hparameterShapes, hexceptions, hbaseAddress, htopAddress, hbytesInWord,
    hfunctions⟩
  have htimeout :=
    evalPanValueFfiClockProgram_of_declarations_and_timeout_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state globals
      memory ffi nextClock pcContext exceptionRel exceptionCode globalsLookup targetState
      memoryAccess memoryHandler hdeclarations hcall hstate hprefix
  exact ⟨targetDeclaration,
    htargetDeclarations,
    ⟨hstructs, hglobals, hmemory, hreturnShapes, hparameterShapes,
      hexceptions, hbaseAddress, htopAddress, hbytesInWord, hfunctions⟩,
    hexceptions,
    htimeout.1, htimeout.2.1, htimeout.2.2⟩

/-! The timeout adequacy branch also preserves Cake's strengthened declaration
    state relation.  The timeout result has no local payload, so its context
    package explicitly records the empty-local state alongside globals/memory.
    This is the declaration-boundary timeout case for the state-relation
    induction. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_timeout_call_result_rel_adequacy_with_context
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
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
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      (fun _ => none) globals memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      state.exceptions = targetDeclaration.exceptions ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.timeout (fun _ => none) globals memory ffi, nextClock) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.timeout (fun _ => none) globals memory)
        (.timeout targetState) ∧
      panValueCrepStateRelWithContext state.structs pcContext
        (fun _ => none) globals memory targetState := by
  have hstate := panValueCrepStateRelWithContext_to_stateRel
    state.structs pcContext (fun _ => none) globals memory targetState
    hstateContext
  have htimeout :=
    evalPanValueFfiClockProgram_of_related_declarations_and_timeout_call_result_rel_adequacy
      context initial clock primitive handler fuel declarations entry arguments state globals
      memory ffi nextClock pcContext exceptionRel exceptionCode globalsLookup targetState
      memoryAccess memoryHandler targetInitial hinitial hdeclarations hcall hstate hprefix
  rcases htimeout with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    hexceptions, hprogram, hprefix', hresult⟩
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, hexceptions,
    hprogram, hprefix', hresult, hstateContext⟩


/-! The timeout declaration bridge also has the context-code form needed by
    the Cake state-relation induction.  Convert the timeout state relation
    through the exact timeout result characterization and retain the event
    prefix. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_timeout_call_context_code_adequacy
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
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
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      (fun _ => none) globals memory targetState)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      state.exceptions = targetDeclaration.exceptions ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.timeout (fun _ => none) globals memory ffi, nextClock) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents ∧
      panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
        exceptionCode globalsLookup
        (.timeout (fun _ => none) globals memory)
        (.timeout targetState) ∧
      panValueCrepStateRelWithContext state.structs pcContext
        (fun _ => none) globals memory targetState := by
  have hfinal :=
    evalPanValueFfiClockProgram_of_related_declarations_and_timeout_call_result_rel_adequacy_with_context
      context initial clock primitive handler fuel declarations entry arguments state globals
      memory ffi nextClock pcContext exceptionRel exceptionCode globalsLookup targetState
      memoryAccess memoryHandler targetInitial hinitial hdeclarations hcall hstateContext
      hprefix
  rcases hfinal with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetExceptions, hprogram, hprefixFinal, hresult, hstateContextFinal⟩
  have hparts := (panValuePcResultRel_timeout_iff state.structs pcContext
    exceptionRel exceptionCode globalsLookup (fun _ => none) globals memory
    targetState).1 hresult
  have hcontextResult := (panValuePcResultRelWithContextCode_timeout_iff
    state.structs pcContext exceptionRel exceptionCode globalsLookup
    (fun _ => none) globals memory targetState).2 hparts
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetExceptions,
    hprogram, hprefixFinal, hcontextResult, hstateContextFinal⟩

/-! Returned calls likewise transport their declaration post-state and return
    shape through the source/target state relation. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_returned_call_result_rel_ioEvents_prefix
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
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
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
    (hvalues : panValueCrepValuesRel [value] targetValues)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupInfo entry targetDeclaration.returnShapes = some shape ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.returned locals globals memory ffi [value]), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup
        (.returned locals globals memory [value])
        (.returned targetState targetValues) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel⟩ :=
    panValueProgramStateRel_evalPanValueDeclarations
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations
  rcases hpostRel with ⟨_hstructs, _hglobals, _hmemory, hreturnShapes,
    _hparameterShapes, _hexceptions, _hbaseAddress, _htopAddress, _hbytesInWord,
    _hfunctions⟩
  have htargetEntry : lookupInfo entry targetDeclaration.returnShapes = some shape := by
    rw [← hreturnShapes]
    exact hentry
  have hreturned :=
    evalPanValueFfiClockProgram_of_declarations_and_returned_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state shape
      locals globals memory ffi value nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState targetValues memoryAccess memoryHandler
      hdeclarations hcall hentry hshape hstate hvalues hprefix
  exact ⟨targetDeclaration, htargetDeclarations,
    ⟨_hstructs, _hglobals, _hmemory, hreturnShapes, _hparameterShapes,
      _hexceptions, _hbaseAddress, _htopAddress, _hbytesInWord, _hfunctions⟩,
    htargetEntry, hreturned.1, hreturned.2.1, hreturned.2.2⟩

/-! The returned adequacy branch preserves the callee body and exception table
    in addition to the return-shape and value relations. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_returned_call_result_rel_adequacy
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
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
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
    (hvalues : panValueCrepValuesRel [value] targetValues)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      lookupInfo entry targetDeclaration.returnShapes = some shape ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.returned locals globals memory ffi [value]), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.returned locals globals memory [value])
        (.returned targetState targetValues) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions⟩ :=
    panValueProgramStateRel_evalDeclarations_adequacy
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations entry hfunction
  rcases hpostRel with ⟨hstructs, hglobals, hmemory, hreturnShapes,
    hparameterShapes, hexceptions, hbaseAddress, htopAddress, hbytesInWord,
    hfunctions⟩
  have htargetEntry : lookupInfo entry targetDeclaration.returnShapes = some shape := by
    rw [← hreturnShapes]
    exact hentry
  have hreturned :=
    evalPanValueFfiClockProgram_of_declarations_and_returned_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state shape
      locals globals memory ffi value nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState targetValues memoryAccess memoryHandler
      hdeclarations hcall hentry hshape hstate hvalues hprefix
  exact ⟨targetDeclaration, htargetDeclarations,
    ⟨hstructs, hglobals, hmemory, hreturnShapes, hparameterShapes, hexceptions,
      hbaseAddress, htopAddress, hbytesInWord, hfunctions⟩,
    htargetFunction, htargetExceptions, htargetEntry,
    hreturned.1, hreturned.2.1, hreturned.2.2⟩

/-! The returned-call adequacy branch also has a context-preserving form.  This
    keeps Cake's `locals_rel` invariants available to the enclosing
    `state_rel_imp_semantics_to_crep` induction instead of projecting them away
    after the call result relation is established. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_returned_call_result_rel_adequacy_with_context
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
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
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
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      locals globals memory targetState)
    (hvalues : panValueCrepValuesRel [value] targetValues)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      lookupInfo entry targetDeclaration.returnShapes = some shape ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.returned locals globals memory ffi [value]), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.returned locals globals memory [value])
        (.returned targetState targetValues) ∧
      panValueCrepStateRelWithContext state.structs pcContext locals globals
        memory targetState ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hstate := panValueCrepStateRelWithContext_to_stateRel
    state.structs pcContext locals globals memory targetState hstateContext
  have hreturned :=
    evalPanValueFfiClockProgram_of_related_declarations_and_returned_call_result_rel_adequacy
      context initial clock primitive handler fuel declarations entry arguments state shape
      locals globals memory ffi value nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState targetValues memoryAccess memoryHandler targetInitial
      hinitial hdeclarations hfunction hcall hentry hshape hstate hvalues hprefix
  rcases hreturned with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions, htargetEntry, hprogram, hresult, hprefix'⟩
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetFunction,
    htargetExceptions, htargetEntry, hprogram, hresult, hstateContext, hprefix'⟩


/-! The returned declaration bridge also has the context-code form consumed by
    the Cake state-relation induction.  Transport the returned value relation
    through the exact returned-result characterization while preserving the
    strengthened context state relation and FFI prefix. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_returned_call_context_code_adequacy
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
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
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
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      locals globals memory targetState)
    (hvalues : panValueCrepValuesRel [value] targetValues)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      lookupInfo entry targetDeclaration.returnShapes = some shape ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.returned locals globals memory ffi [value]), nextClock) ∧
      panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
        exceptionCode globalsLookup
        (.returned locals globals memory [value])
        (.returned targetState targetValues) ∧
      panValueCrepStateRelWithContext state.structs pcContext locals globals
        memory targetState ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hfinal :=
    evalPanValueFfiClockProgram_of_related_declarations_and_returned_call_result_rel_adequacy_with_context
      context initial clock primitive handler fuel declarations entry arguments state shape
      locals globals memory ffi value nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState targetValues memoryAccess memoryHandler targetInitial
      hinitial hdeclarations hfunction hcall hentry hshape hstateContext hvalues hprefix
  rcases hfinal with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions, htargetEntry, hprogram, hresult,
    hstateContextFinal, hprefixFinal⟩
  have hparts := (panValuePcResultRel_returned_iff state.structs pcContext
    exceptionRel exceptionCode globalsLookup locals globals memory [value]
    targetState targetValues).1 hresult
  have hcontextResult := (panValuePcResultRelWithContextCode_returned_iff
    state.structs pcContext exceptionRel exceptionCode globalsLookup locals globals
    memory [value] targetState targetValues).2 hparts
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetFunction,
    htargetExceptions, htargetEntry, hprogram, hcontextResult, hstateContextFinal,
    hprefixFinal⟩

/-! The terminal FFI branch transports the declaration post-state while
    preserving the final event equality required by the result relation. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_finalFfi_call_result_rel_ioEvents_prefix
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α) (targetEvent : FfiFinalEvent)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi locals globals memory ffi event), nextClock))
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState)
    (hevent : event = targetEvent)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.finalFfi locals globals memory ffi event), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup
        (.finalFfi locals globals memory event)
        (.finalFfi targetState targetEvent) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel⟩ :=
    panValueProgramStateRel_evalPanValueDeclarations
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations
  have hfinal :=
    evalPanValueFfiClockProgram_of_declarations_and_finalFfi_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi event nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState targetEvent memoryAccess memoryHandler
      hdeclarations hcall hstate hevent hprefix
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel,
    hfinal.1, hfinal.2.1, hfinal.2.2⟩

/-! The terminal-FFI adequacy branch keeps declaration lookup and exception
    equality available to the state-relation induction alongside final-event
    equality and the clocked result relation. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_finalFfi_call_result_rel_adequacy
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α) (targetEvent : FfiFinalEvent)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi locals globals memory ffi event), nextClock))
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState)
    (hevent : event = targetEvent)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.finalFfi locals globals memory ffi event), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.finalFfi locals globals memory event)
        (.finalFfi targetState targetEvent) ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  obtain ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions⟩ :=
    panValueProgramStateRel_evalDeclarations_adequacy
      initial.source targetInitial hinitial declarations memoryAccess state
      hdeclarations entry hfunction
  rcases hpostRel with ⟨hstructs, hglobals, hmemory, hreturnShapes,
    hparameterShapes, hexceptions, hbaseAddress, htopAddress, hbytesInWord,
    hfunctions⟩
  have hfinal :=
    evalPanValueFfiClockProgram_of_declarations_and_finalFfi_call_result_rel_ioEvents_prefix
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi event nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState targetEvent memoryAccess memoryHandler
      hdeclarations hcall hstate hevent hprefix
  exact ⟨targetDeclaration, htargetDeclarations,
    ⟨hstructs, hglobals, hmemory, hreturnShapes, hparameterShapes, hexceptions,
      hbaseAddress, htopAddress, hbytesInWord, hfunctions⟩,
    htargetFunction, htargetExceptions,
    hfinal.1, hfinal.2.1, hfinal.2.2⟩

/-! The terminal-FFI declaration branch also preserves the strengthened
    context state relation.  This is the FinalFFI counterpart of the normal,
    raised, and timeout adequacy bridges above. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_finalFfi_call_result_rel_adequacy_with_context
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α) (targetEvent : FfiFinalEvent)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi locals globals memory ffi event), nextClock))
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      locals globals memory targetState)
    (hevent : event = targetEvent)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.finalFfi locals globals memory ffi event), nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (.finalFfi locals globals memory event)
        (.finalFfi targetState targetEvent) ∧
      panValueCrepStateRelWithContext state.structs pcContext locals globals
        memory targetState ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hstate := panValueCrepStateRelWithContext_to_stateRel
    state.structs pcContext locals globals memory targetState hstateContext
  have hfinal :=
    evalPanValueFfiClockProgram_of_related_declarations_and_finalFfi_call_result_rel_adequacy
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi event nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState targetEvent memoryAccess memoryHandler targetInitial
      hinitial hdeclarations hfunction hcall hstate hevent hprefix
  rcases hfinal with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions, hprogram, hresult, hprefixFinal⟩
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetFunction,
    htargetExceptions, hprogram, hresult, hstateContext, hprefixFinal⟩

/-! The FinalFFI declaration bridge also has the context-code form used by
    the Cake state-relation induction.  Convert the context-state result and
    event equality through the exact FinalFFI relation characterization. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_finalFfi_call_context_code_adequacy
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α) (targetEvent : FfiFinalEvent)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi locals globals memory ffi event), nextClock))
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      locals globals memory targetState)
    (hevent : event = targetEvent)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.finalFfi locals globals memory ffi event), nextClock) ∧
      panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
        exceptionCode globalsLookup
        (.finalFfi locals globals memory event)
        (.finalFfi targetState targetEvent) ∧
      panValueCrepStateRelWithContext state.structs pcContext locals globals
        memory targetState ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hfinal :=
    evalPanValueFfiClockProgram_of_related_declarations_and_finalFfi_call_result_rel_adequacy_with_context
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi event nextClock pcContext exceptionRel exceptionCode
      globalsLookup targetState targetEvent memoryAccess memoryHandler targetInitial
      hinitial hdeclarations hfunction hcall hstateContext hevent hprefix
  rcases hfinal with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions, hprogram, hresult, hstateContextFinal,
    hprefixFinal⟩
  have hparts := (panValuePcResultRel_finalFfi_iff state.structs pcContext
    exceptionRel exceptionCode globalsLookup locals globals memory event
    targetState targetEvent).1 hresult
  have hcontextResult := (panValuePcResultRelWithContextCode_finalFfi_iff
    state.structs pcContext exceptionRel exceptionCode globalsLookup locals globals
    memory event targetState targetEvent).2 hparts
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetFunction,
    htargetExceptions, hprogram, hcontextResult, hstateContextFinal, hprefixFinal⟩

/-! The ordinary normal-call branch also has a context-code form.  It keeps
    the declaration evaluator and the clocked call evaluator explicit, then
    lifts the concrete source/target state relation to the context-code
    relation consumed by the `state_rel_imp_semantics_to_crep` induction. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_normal_call_context_code
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
    (nextClock : Nat)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), nextClock))
    (hstate : panValueCrepStateRel state.structs pcContext locals globals
      memory targetState) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), nextClock) ∧
    panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
      exceptionCode globalsLookup
      (.normal locals globals memory) (.normal targetState) := by
  have hprogram := evalPanValueFfiClockProgram_of_declarations_and_call
    context initial clock primitive handler fuel declarations entry arguments state
    (.control (.normal locals globals memory ffi)) nextClock
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hentry hcall
  refine ⟨hprogram, ?_⟩
  exact (panValuePcResultRelWithContextCode_normal_iff state.structs pcContext
    exceptionRel exceptionCode globalsLookup locals globals memory targetState).2 hstate

/-! The direct returned-call branch has the same context-code state boundary as
    the normal branch.  The return-shape lookup, evaluator result, source/target
    state relation, and flattened value relation remain explicit for the
    returned constructor of `state_rel_imp_semantics_to_crep`. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_returned_call_context_code
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
    panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
      exceptionCode globalsLookup
      (.returned locals globals memory [value]) (.returned targetState targetValues) := by
  have hprogram := evalPanValueFfiClockProgram_of_declarations_and_returned_call
    context initial clock primitive handler fuel declarations entry arguments
    state shape locals globals memory ffi value nextClock
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    hdeclarations hcall hentry hshape
  refine ⟨hprogram, ?_⟩
  exact (panValuePcResultRelWithContextCode_returned_iff state.structs pcContext
    exceptionRel exceptionCode globalsLookup locals globals memory [value]
    targetState targetValues).2 ⟨hstate, hvalues⟩

/-! The timeout declaration branch has the same context-code boundary as the
    normal branch.  This is the clock-exhaustion case of
    `state_rel_imp_semantics_to_crep`: declaration evaluation and the call
    evaluator remain explicit, while the concrete state relation is lifted to
    the context-aware result relation rather than being dropped at timeout. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_timeout_call_context_code
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
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetState : CrepState α)
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
    (hstate : panValueCrepStateRel state.structs pcContext
      (fun _ => none) globals memory targetState) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) globals memory ffi, nextClock) ∧
    panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
      exceptionCode globalsLookup
      (.timeout (fun _ => none) globals memory) (.timeout targetState) := by
  have hprogram := evalPanValueFfiClockProgram_of_declarations_and_timeout_call
    context initial clock primitive handler fuel declarations entry arguments state
    globals memory ffi nextClock (memoryAccess := memoryAccess)
    (memoryHandler := memoryHandler) hdeclarations hcall
  refine ⟨hprogram, ?_⟩
  exact (panValuePcResultRelWithContextCode_timeout_iff state.structs pcContext
    exceptionRel exceptionCode globalsLookup (fun _ => none) globals memory
    targetState).2 hstate

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

/-! The raised-call context bridge also needs the declaration-state package
    used by Cake's `state_rel_imp_semantics_decls_to_crep` induction.  Keep the
    transformed callee, exception table, evaluator result, and context-aware
    raised relation together so the caller can continue the induction without
    reconstructing any of those facts from a weakened state relation. -/
theorem evalPanValueFfiClockProgram_of_related_declarations_and_raised_call_context_code_adequacy
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
    (targetInitial : PanValueProgramState α)
    (hinitial : panValueProgramStateRel initial.source targetInitial)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    {parameters : List VarName} {body : Prog α}
    (hfunction : lookupPanFunction entry state.functions = some (parameters, body))
    (hcall : evalPanValueFfiClockCall context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord fuel
      (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
      (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock))
    (hstateContext : panValueCrepStateRelWithContext state.structs pcContext
      locals globals memory targetState)
    (hresult : panValuePcExceptionResultRel state.structs pcContext exceptionRel
      exceptionCode globalsLookup globals memory exception value targetState
      targetException)
    (hlookup : lookupInfo exception pcContext.exceptions = some targetException)
    (hprefix : initial.ffi.ioEvents <+: ffi.ioEvents) :
    ∃ targetDeclaration,
      evalPanValueDeclarations targetInitial (panSimpDecls declarations)
        (memoryAccess := memoryAccess) = some targetDeclaration ∧
      panValueProgramStateRel state targetDeclaration ∧
      lookupPanFunction entry targetDeclaration.functions =
        some (parameters, panSimpProg body) ∧
      state.exceptions = targetDeclaration.exceptions ∧
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) =
        some (.control (.raised (fun _ => none) globals memory ffi exception value),
          nextClock) ∧
      panValuePcResultRelWithContextCode state.structs pcContext exceptionRel
        exceptionCode globalsLookup
        (.raised locals globals memory exception value)
        (.raised targetState targetException) ∧
      panValueCrepStateRelWithContext state.structs pcContext locals globals
        memory targetState ∧
      initial.ffi.ioEvents <+: ffi.ioEvents := by
  have hstate := panValueCrepStateRelWithContext_to_stateRel
    state.structs pcContext locals globals memory targetState hstateContext
  have hraised :=
    evalPanValueFfiClockProgram_of_related_declarations_and_raised_call_result_rel_adequacy
      context initial clock primitive handler fuel declarations entry arguments state
      locals globals memory ffi exception value nextClock pcContext exceptionRel
      exceptionCode globalsLookup targetState targetException memoryAccess memoryHandler
      targetInitial
      hinitial hdeclarations hfunction hcall hstate hresult hprefix
  rcases hraised with ⟨targetDeclaration, htargetDeclarations, hpostRel,
    htargetFunction, htargetExceptions, hprogram, hresultRel, hprefix'⟩
  have hcontextResult := panValuePcResultRelWithContextCode_raised_of_rel_and_lookup
    state.structs pcContext exceptionRel exceptionCode globalsLookup locals globals
    memory exception value targetState targetException hresultRel hlookup
  exact ⟨targetDeclaration, htargetDeclarations, hpostRel, htargetFunction,
    htargetExceptions, hprogram, hcontextResult, hstateContext, hprefix'⟩

/-! Declaration calls preserve the incoming event trace when the callee times
    out before the declaration continuation can run. -/
theorem evalPanValueFfiClockProg_decCall_timeout_ioEvents_prefix
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
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.timeout (fun _ => none) nextGlobals nextMemory nextFfi, callClock))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.timeout (fun _ => none) nextGlobals nextMemory nextFfi, callClock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_decCall_timeout context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock callClock locals globals
      memory ffi name shape function arguments body nextGlobals nextMemory nextFfi hcall
  · exact hprefix

/-! A declaration call propagates a callee's terminal FFI result without
    entering its local continuation, while retaining the event prefix. -/
theorem evalPanValueFfiClockProg_decCall_finalFfi_ioEvents_prefix
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
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_decCall_finalFfi context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock callClock locals globals
      memory ffi name shape function arguments body nextLocals nextGlobals nextMemory
      nextFfi event hcall
  · exact hprefix

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

theorem evalPanValueFfiClockProg_tick_zero_timeout_ioEvents_prefix
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
      some (.timeout (fun _ => none) globals memory ffi, 0) ∧
      ffi.ioEvents <+: ffi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_tick_zero context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
      memoryAccess contracts
  · exact List.prefix_refl _

theorem evalPanValueFfiClockProg_tick_succ_ioEvents_prefix
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
      some (.control (.normal locals globals memory ffi), clock) ∧
      ffi.ioEvents <+: ffi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_tick_succ context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock locals globals memory
      ffi memoryAccess contracts
  · exact List.prefix_refl _

theorem evalPanValueFfiClockProg_while_zero_ioEvents_prefix
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
    (condition : Exp α) (body : Prog α) (w : α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hcondition : evalPanValueExp structs locals globals memory baseAddress
      topAddress bytesInWord condition (memoryAccess := memoryAccess) =
      some (.word w))
    (hw : (w == (0 : α)) = true) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.while condition body) memoryAccess contracts memoryHandler =
      some (.control (.normal locals globals memory ffi), clock) ∧
      ffi.ioEvents <+: ffi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_while_zero_some context primitive handler
      structs functions baseAddress topAddress bytesInWord fuel locals globals
      memory ffi clock condition body memoryAccess contracts memoryHandler w
      hcondition hw
  · exact List.prefix_refl _

theorem evalPanValueFfiClockProg_ite_true_ioEvents_prefix
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
    (condition : Exp α) (thenBranch elseBranch : Prog α)
    (wordValue : α) (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hcondition : evalPanValueExp structs locals globals memory baseAddress
      topAddress bytesInWord condition (memoryAccess := memoryAccess) =
      some (.word wordValue))
    (hnonzero : (wordValue != 0) = true)
    (hthen : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      thenBranch (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (outcome, nextClock))
    (hprefix : ffi.ioEvents <+:
      (panResultFfi (outcome, nextClock)).ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.ite condition thenBranch elseBranch) memoryAccess contracts memoryHandler =
      some (outcome, nextClock) ∧
      ffi.ioEvents <+: (panResultFfi (outcome, nextClock)).ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_ite_true_some context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
      clock condition thenBranch elseBranch memoryAccess contracts memoryHandler
      wordValue outcome nextClock hcondition hnonzero hthen
  · exact hprefix

theorem evalPanValueFfiClockProg_ite_false_ioEvents_prefix
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
    (condition : Exp α) (thenBranch elseBranch : Prog α)
    (wordValue : α) (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hcondition : evalPanValueExp structs locals globals memory baseAddress
      topAddress bytesInWord condition (memoryAccess := memoryAccess) =
      some (.word wordValue))
    (hzero : (wordValue != 0) = false)
    (helse : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      elseBranch (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (outcome, nextClock))
    (hprefix : ffi.ioEvents <+:
      (panResultFfi (outcome, nextClock)).ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.ite condition thenBranch elseBranch) memoryAccess contracts memoryHandler =
      some (outcome, nextClock) ∧
      ffi.ioEvents <+: (panResultFfi (outcome, nextClock)).ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_ite_false_some context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
      clock condition thenBranch elseBranch memoryAccess contracts memoryHandler
      wordValue outcome nextClock hcondition hzero helse
  · exact hprefix

theorem evalPanValueFfiClockProg_return_ioEvents_prefix
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
    (value : Exp α)
    (returnLocals returnGlobals : VarName → Option (PanValue α))
    (returnMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (values : List (PanValue α)) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi (.return value)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned returnLocals returnGlobals returnMemory nextFfi values, steps))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.return value) memoryAccess contracts memoryHandler =
      some (.control
        (.returned returnLocals returnGlobals returnMemory nextFfi values), clock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_leaf_some context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
      clock (.return value) memoryAccess contracts memoryHandler
      (PanValueFfiLeafProg.return value)
      (.returned returnLocals returnGlobals returnMemory nextFfi values) steps hsteps
  · exact hprefix

theorem evalPanValueFfiClockProg_raise_ioEvents_prefix
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
    (exception : ExceptionId) (value : Exp α)
    (raisedLocals raisedGlobals : VarName → Option (PanValue α))
    (raisedMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (raisedValue : PanValue α) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi
      (.raise exception value) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.raised raisedLocals raisedGlobals raisedMemory nextFfi exception
        raisedValue, steps))
    (hprefix : ffi.ioEvents <+: nextFfi.ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.raise exception value) memoryAccess contracts memoryHandler =
      some (.control
        (.raised raisedLocals raisedGlobals raisedMemory nextFfi exception
          raisedValue), clock) ∧
      ffi.ioEvents <+: nextFfi.ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_leaf_some context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
      clock (.raise exception value) memoryAccess contracts memoryHandler
      (PanValueFfiLeafProg.raise exception value)
      (.raised raisedLocals raisedGlobals raisedMemory nextFfi exception raisedValue)
      steps hsteps
  · exact hprefix

theorem evalPanValueFfiProgSteps_raise_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat) (exception : ExceptionId) (value : Exp α)
    (result : PanValueFfiControlResult α σ) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi
      (.raise exception value) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (result, steps)) :
    ffi.ioEvents <+:
      (panResultFfi ((.control result : PanValueFfiClockOutcome α σ), clock)).ioEvents := by
  cases hvalue : evalPanValueExpCounted structs locals globals memory baseAddress topAddress
      bytesInWord value (memoryAccess := memoryAccess) with
  | none =>
      simp [evalPanValueFfiProgSteps, hvalue] at hsteps
  | some pair =>
      obtain ⟨valueResult, valueSteps⟩ := pair
      by_cases hvalid :
          (panValueExceptionValid structs contracts exception valueResult &&
            panValuePayloadWithinLimit structs valueResult) = true
      · simp [evalPanValueFfiProgSteps, hvalue] at hsteps
        rcases hsteps with ⟨_, hresult, _⟩
        rw [← hresult]
        exact List.prefix_refl _
      · simp [evalPanValueFfiProgSteps, hvalue] at hsteps
        rcases hsteps with ⟨hvalids, _, _⟩
        apply False.elim
        apply hvalid
        simp [hvalids.1, hvalids.2]

theorem evalPanValueFfiProgSteps_return_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat) (value : Exp α)
    (result : PanValueFfiControlResult α σ) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi
      (.return value) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (result, steps)) :
    ffi.ioEvents <+:
      (panResultFfi ((.control result : PanValueFfiClockOutcome α σ), clock)).ioEvents := by
  cases hvalue : evalPanValueExpCounted structs locals globals memory
      baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess) with
  | none =>
      simp [evalPanValueFfiProgSteps, hvalue] at hsteps
  | some pair =>
      obtain ⟨valueResult, valueSteps⟩ := pair
      by_cases hvalid : panValuePayloadWithinLimit structs valueResult = true
      · simp [evalPanValueFfiProgSteps, hvalue, hvalid] at hsteps
        rcases hsteps with ⟨rfl, rfl⟩
        exact List.prefix_refl _
      · simp [evalPanValueFfiProgSteps, hvalue, hvalid] at hsteps

theorem evalPanValueFfiClockProg_leaf_ioEvents_prefix
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
    (program : Prog α) (hleaf : PanValueFfiLeafProg program)
    (result : PanValueFfiControlResult α σ) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi program
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (result, steps))
    (hprefix : ffi.ioEvents <+: (panResultFfi ((.control result :
      PanValueFfiClockOutcome α σ), clock)).ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      program memoryAccess contracts memoryHandler =
      some (.control result, clock) ∧
      ffi.ioEvents <+:
        (panResultFfi ((.control result : PanValueFfiClockOutcome α σ),
          clock)).ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_leaf_some context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
      clock program memoryAccess contracts memoryHandler hleaf result steps hsteps
  · exact hprefix

theorem panResultFfi_panValueFfiClockRestoreLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α))
    (outcome : PanValueFfiClockOutcome α σ) (clock : Nat) :
    panResultFfi (panValueFfiClockRestoreLocal name oldValue outcome, clock) =
      panResultFfi (outcome, clock) := by
  cases outcome with
  | control result => cases result <;> rfl
  | timeout locals globals memory ffi => rfl

theorem evalPanValueFfiClockProg_dec_ioEvents_prefix
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
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (valueResult : PanValue α) (outcome : PanValueFfiClockOutcome α σ)
    (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hvalue : evalPanValueExp structs locals globals memory baseAddress topAddress
      bytesInWord value (memoryAccess := memoryAccess) = some valueResult)
    (hmatch : panShapeMatches (panValueShape structs valueResult) shape = true)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name valueResult)
      globals memory ffi clock body (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, nextClock))
    (hprefix : ffi.ioEvents <+:
      (panResultFfi (outcome, nextClock)).ioEvents) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.dec name shape value body) memoryAccess contracts memoryHandler =
      some (panValueFfiClockRestoreLocal name (locals name) outcome, nextClock) ∧
      ffi.ioEvents <+:
        (panResultFfi
          (panValueFfiClockRestoreLocal name (locals name) outcome, nextClock)).ioEvents := by
  constructor
  · exact evalPanValueFfiClockProg_dec_some context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
      clock name shape value body memoryAccess contracts memoryHandler valueResult
      outcome nextClock hvalue hmatch hbody
  · rw [panResultFfi_panValueFfiClockRestoreLocal]
    exact hprefix


set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
/-- Generic event-prefix monotonicity for the clocked evaluator, by mutual induction over the
residual/timeout `fuel` budget. The per-leaf residual obligation is threaded explicitly as
`hleaf`: every successful unit-fuel `evalPanValueFfiProgSteps` run preserves the FFI event log.
All other constructors (declaration, sequence, conditional, call, declaration-call, while, tick)
are reduced to the corresponding induction hypothesis or to `List.prefix_refl`. -/
theorem evalPanValueFfiClock_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (hleaf : ∀ (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
        (ffi : FfiState σ) (clock : Nat) (program : Prog α)
        (result : PanValueFfiControlResult α σ) (steps : Nat)
        (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
        evalPanValueFfiProgSteps context primitive handler structs functions baseAddress topAddress
          bytesInWord 1 locals globals memory ffi program
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (result, steps) →
        ffi.ioEvents <+:
          (panResultFfi ((.control result : PanValueFfiClockOutcome α σ), clock)).ioEvents) :
    (∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
        (ffi : FfiState σ) (clock : Nat)
        (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
        (function : FunName) (arguments : List (Exp α))
        (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
        (outcome : PanValueFfiClockOutcome α σ) (resultClock : Nat),
        evalPanValueFfiClockCall context primitive handler structs functions baseAddress topAddress bytesInWord
          fuel locals globals memory ffi clock info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock) →
        ffi.ioEvents <+: (panResultFfi (outcome, resultClock)).ioEvents)
    ∧
    (∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
        (ffi : FfiState σ) (clock : Nat) (program : Prog α)
        (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
        (outcome : PanValueFfiClockOutcome α σ) (resultClock : Nat),
        evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress bytesInWord
          fuel locals globals memory ffi clock program
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock) →
        ffi.ioEvents <+: (panResultFfi (outcome, resultClock)).ioEvents) := by
  refine evalPanValueFfiClockCall.mutual_induct
    (motive1 := fun fuel locals globals memory ffi clock info function arguments memoryAccess contracts memoryHandler =>
      ∀ outcome resultClock,
        evalPanValueFfiClockCall context primitive handler structs functions baseAddress topAddress bytesInWord
          fuel locals globals memory ffi clock info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock) →
        ffi.ioEvents <+: (panResultFfi (outcome, resultClock)).ioEvents)
    (motive2 := fun fuel locals globals memory ffi clock program memoryAccess contracts memoryHandler =>
      ∀ outcome resultClock,
        evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress bytesInWord
          fuel locals globals memory ffi clock program
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock) →
        ffi.ioEvents <+: (panResultFfi (outcome, resultClock)).ioEvents)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- case1: Call fuel 0
    intro memoryAccess contracts memoryHandler locals globals memory ffi clock info function arguments outcome resultClock hrun
    simp only [evalPanValueFfiClockCall] at hrun
    exact absurd hrun (by simp)
  · -- case2: Call fuel+1
    intro fuel locals globals memory ffi clock info function arguments memoryAccess contracts memoryHandler hbodyIH hhandlerIH outcome resultClock hrun
    simp only [evalPanValueFfiClockCall] at hrun
    cases hvalues : evalPanValueExps structs locals globals memory baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) with
    | none => simp only [hvalues, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
    | some values =>
      simp only [hvalues, Option.bind_eq_bind, Option.bind_some] at hrun
      cases hlookup : lookupPanFunction function functions with
      | none => simp only [hlookup, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
      | some pair =>
        obtain ⟨parameters, body⟩ := pair
        simp only [hlookup, Option.bind_eq_bind, Option.bind_some] at hrun
        by_cases hparams : panValueParametersValid structs contracts function values = true
        · simp only [hparams, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
          cases hbind : bindPanValueParameters parameters values with
          | none => simp only [hbind, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
          | some calleeLocals =>
            simp only [hbind, Option.bind_eq_bind, Option.bind_some] at hrun
            by_cases hclock : clock = 0
            · simp only [hclock, if_true, Option.pure_def] at hrun
              have hpair := Option.some.inj hrun
              rw [← hpair]
              simp only [panValueFfiClockTimeout, panResultFfi]
              exact List.prefix_refl _
            · simp only [hclock, if_false, Option.bind_eq_bind, Option.bind_some] at hrun
              cases hcallee : evalPanValueFfiClockProg context primitive handler structs functions baseAddress
                  topAddress bytesInWord fuel calleeLocals globals memory ffi (decPanClock clock) body
                  (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
              | none => simp only [hcallee, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
              | some pair2 =>
                obtain ⟨calleeOutcome, calleeClock⟩ := pair2
                simp only [hcallee, Option.bind_eq_bind, Option.bind_some] at hrun
                have hb : ffi.ioEvents <+: (panResultFfi (calleeOutcome, calleeClock)).ioEvents :=
                  hbodyIH body calleeLocals calleeOutcome calleeClock hcallee
                cases calleeOutcome with
                | timeout l g m f =>
                  simp only [Option.pure_def] at hrun
                  have hpair := Option.some.inj hrun
                  rw [← hpair]
                  exact hb
                | control result =>
                  cases result with
                  | normal l g m f => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                  | broke l g m f => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                  | continued l g m f => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                  | returned l g m f vs =>
                    by_cases hret : (panValueReturnValid structs contracts function vs && panValueValuesWithinLimit structs vs) = true
                    · simp only [hret, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                      cases info with
                      | none =>
                        simp only [Option.pure_def] at hrun
                        have hpair := Option.some.inj hrun
                        rw [← hpair]
                        exact hb
                      | some ipair =>
                        obtain ⟨destination, sndOpt⟩ := ipair
                        simp only [Option.bind_eq_bind, Option.bind_some] at hrun
                        cases hassign : assignPanValueCallResult locals g destination vs structs with
                        | none => simp only [hassign, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                        | some apair =>
                          simp only [hassign, Option.bind_eq_bind, Option.bind_some] at hrun
                          simp only [Option.pure_def] at hrun
                          have hpair := Option.some.inj hrun
                          rw [← hpair]
                          exact hb
                    · simp only [hret, if_false, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                  | raised l g m f ex v =>
                    by_cases hexc : (panValueExceptionValid structs contracts ex v && panValuePayloadWithinLimit structs v) = true
                    · simp only [hexc, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                      cases info with
                      | none =>
                        simp only [Option.pure_def] at hrun
                        have hpair := Option.some.inj hrun
                        rw [← hpair]
                        exact hb
                      | some ipair =>
                        obtain ⟨destination, sndOpt⟩ := ipair
                        cases sndOpt with
                        | none =>
                          simp only [Option.pure_def] at hrun
                          have hpair := Option.some.inj hrun
                          rw [← hpair]
                          exact hb
                        | some htriple =>
                          obtain ⟨caught, handlerVariable, handlerProgram⟩ := htriple
                          by_cases hcaught : (caught == ex) = true
                          · simp only [hcaught, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                            by_cases hvalid : panValueHandlerValid structs contracts locals handlerVariable v = true
                            · simp only [hvalid, if_true] at hrun
                              have hidx := hhandlerIH calleeClock g m f v handlerVariable handlerProgram outcome resultClock hrun
                              exact List.IsPrefix.trans (by simpa [panResultFfi] using hb) hidx
                            · simp only [hvalid, if_false, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                          · simp only [hcaught, if_false, Option.pure_def] at hrun
                            have hpair := Option.some.inj hrun
                            rw [← hpair]
                            exact hb
                    · simp only [hexc, if_false, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                  | finalFfi l g m f ev =>
                    simp only [Option.pure_def] at hrun
                    have hpair := Option.some.inj hrun
                    rw [← hpair]
                    exact hb
        · simp only [hparams, if_false, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
  · -- case3: Prog fuel 0
    intro memoryAccess contracts memoryHandler locals globals memory ffi clock program outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    exact absurd hrun (by simp)
  · -- case4: Prog dec
    intro fuel locals globals memory ffi clock name shape value body memoryAccess contracts memoryHandler hbodyIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hvalue : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord value
        (memoryAccess := memoryAccess) with
    | none => simp only [hvalue, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
    | some valueResult =>
      simp only [hvalue, Option.bind_eq_bind, Option.bind_some] at hrun
      by_cases hmatch : panShapeMatches (panValueShape structs valueResult) shape = true
      · simp only [hmatch, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
        cases hbody : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
            bytesInWord fuel (updatePanValueMap locals name valueResult) globals memory ffi clock body
            (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
        | none => simp only [hbody, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
        | some pair =>
          obtain ⟨bodyOutcome, bodyClock⟩ := pair
          simp only [hbody, Option.bind_eq_bind, Option.bind_some] at hrun
          have hb : ffi.ioEvents <+: (panResultFfi (bodyOutcome, bodyClock)).ioEvents :=
            hbodyIH valueResult bodyOutcome bodyClock hbody
          simp only [Option.pure_def] at hrun
          have hpair := Option.some.inj hrun
          rw [← hpair]
          rw [panResultFfi_panValueFfiClockRestoreLocal]
          exact hb
      · simp only [hmatch, if_false, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
  · -- case5: Prog seq
    intro fuel locals globals memory ffi clock first second memoryAccess contracts memoryHandler hfirstIH hsecondIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hfirst : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock first
        (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
    | none => simp only [hfirst, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
    | some pair =>
      obtain ⟨firstOutcome, firstClock⟩ := pair
      simp only [hfirst, Option.bind_eq_bind, Option.bind_some] at hrun
      have hf : ffi.ioEvents <+: (panResultFfi (firstOutcome, firstClock)).ioEvents :=
        hfirstIH firstOutcome firstClock hfirst
      cases firstOutcome with
      | timeout l g m f =>
        simp only [Option.pure_def] at hrun
        have hpair := Option.some.inj hrun
        rw [← hpair]
        exact hf
      | control result =>
        cases result with
        | normal nl ng nm nf =>
          cases hsecond : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
              bytesInWord fuel nl ng nm nf firstClock second
              (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
          | none => simp only [hsecond, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
          | some pair2 =>
            obtain ⟨secondOutcome, secondClock⟩ := pair2
            simp only [hsecond, Option.bind_eq_bind, Option.bind_some] at hrun
            have hs : nf.ioEvents <+: (panResultFfi (secondOutcome, secondClock)).ioEvents :=
              hsecondIH firstClock nl ng nm nf secondOutcome secondClock hsecond
            have hpair := Option.some.inj hrun
            rw [← hpair]
            exact List.IsPrefix.trans (by simpa [panResultFfi] using hf) hs
        | returned l g m f vs =>
          simp only [Option.pure_def] at hrun
          have hpair := Option.some.inj hrun
          rw [← hpair]
          exact hf
        | raised l g m f ex v =>
          simp only [Option.pure_def] at hrun
          have hpair := Option.some.inj hrun
          rw [← hpair]
          exact hf
        | broke l g m f =>
          simp only [Option.pure_def] at hrun
          have hpair := Option.some.inj hrun
          rw [← hpair]
          exact hf
        | continued l g m f =>
          simp only [Option.pure_def] at hrun
          have hpair := Option.some.inj hrun
          rw [← hpair]
          exact hf
        | finalFfi l g m f ev =>
          simp only [Option.pure_def] at hrun
          have hpair := Option.some.inj hrun
          rw [← hpair]
          exact hf
  · -- case6: Prog ite
    intro fuel locals globals memory ffi clock condition thenBranch elseBranch memoryAccess contracts memoryHandler hthenIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hcond : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord condition
        (memoryAccess := memoryAccess) with
    | none => simp only [hcond, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
    | some condValue =>
      simp only [hcond, Option.bind_eq_bind, Option.bind_some] at hrun
      cases condValue with
      | word w => exact hthenIH w outcome resultClock hrun
      | rStruct fields => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
      | nStruct nm fields => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
  · -- case7: Prog call
    intro fuel locals globals memory ffi clock info function arguments memoryAccess contracts memoryHandler hcallIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    exact hcallIH outcome resultClock hrun
  · -- case8: Prog decCall
    intro fuel locals globals memory ffi clock name shape function arguments body memoryAccess contracts memoryHandler hcallIH hbodyIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hcall : evalPanValueFfiClockCall context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock none function arguments
        (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
    | none => simp only [hcall, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
    | some pair =>
      obtain ⟨callOutcome, nextClock⟩ := pair
      simp only [hcall, Option.bind_eq_bind, Option.bind_some] at hrun
      have hc : ffi.ioEvents <+: (panResultFfi (callOutcome, nextClock)).ioEvents :=
        hcallIH callOutcome nextClock hcall
      cases callOutcome with
      | timeout l g m f =>
        simp only [Option.pure_def] at hrun
        have hpair := Option.some.inj hrun
        rw [← hpair]
        exact hc
      | control result =>
        cases result with
        | returned l g m f vs =>
          cases vs with
          | nil =>
            simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
          | cons v rest =>
            cases rest with
            | cons v2 rest2 =>
              simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
            | nil =>
              simp only [Option.bind_eq_bind, Option.bind_some] at hrun
              by_cases hmatch : panShapeMatches (panValueShape structs v) shape = true
              · simp only [hmatch, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                cases hbody : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
                    bytesInWord fuel (updatePanValueMap locals name v) g m f nextClock body
                    (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
                | none => simp only [hbody, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                | some pair2 =>
                  obtain ⟨bodyOutcome, bodyClock⟩ := pair2
                  simp only [hbody, Option.bind_eq_bind, Option.bind_some] at hrun
                  have hb : f.ioEvents <+: (panResultFfi (bodyOutcome, bodyClock)).ioEvents :=
                    hbodyIH nextClock g m f v bodyOutcome bodyClock hbody
                  simp only [Option.pure_def] at hrun
                  have hpair := Option.some.inj hrun
                  rw [← hpair]
                  rw [panResultFfi_panValueFfiClockRestoreLocal]
                  exact List.IsPrefix.trans (by simpa [panResultFfi] using hc) hb
              · simp only [hmatch, if_false, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
        | normal l g m f => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
        | broke l g m f => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
        | continued l g m f => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
        | raised l g m f ex v =>
          simp only [Option.pure_def] at hrun
          have hpair := Option.some.inj hrun
          rw [← hpair]
          exact hc
        | finalFfi l g m f ev =>
          simp only [Option.pure_def] at hrun
          have hpair := Option.some.inj hrun
          rw [← hpair]
          exact hc
  · -- case9: Prog while
    intro fuel locals globals memory ffi clock conditionExp body memoryAccess contracts memoryHandler hbodyIH hrecIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hcond : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord conditionExp
        (memoryAccess := memoryAccess) with
    | none => simp only [hcond, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
    | some condValue =>
      simp only [hcond, Option.bind_eq_bind, Option.bind_some] at hrun
      cases condValue with
      | word w =>
        by_cases hz : (w == 0) = true
        · simp only [hz, if_true, Option.pure_def] at hrun
          have hpair := Option.some.inj hrun
          rw [← hpair]
          simp only [panResultFfi]
          exact List.prefix_refl _
        · simp only [hz, if_false, Option.bind_eq_bind, Option.bind_some] at hrun
          by_cases hclock : (clock == 0) = true
          · simp only [hclock, if_true, Option.pure_def] at hrun
            have hpair := Option.some.inj hrun
            rw [← hpair]
            simp only [panValueFfiClockTimeout, panResultFfi]
            exact List.prefix_refl _
          · simp only [hclock, if_false, Option.bind_eq_bind, Option.bind_some] at hrun
            cases hbody : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
                bytesInWord fuel locals globals memory ffi (decPanClock clock) body
                (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
            | none => simp only [hbody, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
            | some pair =>
              obtain ⟨bodyOutcome, bodyClock⟩ := pair
              simp only [hbody, Option.bind_eq_bind, Option.bind_some] at hrun
              have hb : ffi.ioEvents <+: (panResultFfi (bodyOutcome, bodyClock)).ioEvents :=
                hbodyIH bodyOutcome bodyClock hbody
              cases bodyOutcome with
              | timeout l g m f =>
                simp only [Option.pure_def] at hrun
                have hpair := Option.some.inj hrun
                rw [← hpair]
                exact hb
              | control result =>
                cases result with
                | normal nl ng nm nf =>
                  cases hrec : evalPanValueFfiClockProg context primitive handler structs functions baseAddress
                      topAddress bytesInWord fuel nl ng nm nf bodyClock (.while conditionExp body)
                      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
                  | none => simp only [hrec, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                  | some pair2 =>
                    obtain ⟨recOutcome, recClock⟩ := pair2
                    simp only [hrec, Option.bind_eq_bind, Option.bind_some] at hrun
                    have hr : nf.ioEvents <+: (panResultFfi (recOutcome, recClock)).ioEvents :=
                      hrecIH bodyClock nl ng nm nf recOutcome recClock hrec
                    simp only [Option.pure_def] at hrun
                    have hpair := Option.some.inj hrun
                    rw [← hpair]
                    exact List.IsPrefix.trans (by simpa [panResultFfi] using hb) hr
                | continued nl ng nm nf =>
                  cases hrec : evalPanValueFfiClockProg context primitive handler structs functions baseAddress
                      topAddress bytesInWord fuel nl ng nm nf bodyClock (.while conditionExp body)
                      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
                  | none => simp only [hrec, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                  | some pair2 =>
                    obtain ⟨recOutcome, recClock⟩ := pair2
                    simp only [hrec, Option.bind_eq_bind, Option.bind_some] at hrun
                    have hr : nf.ioEvents <+: (panResultFfi (recOutcome, recClock)).ioEvents :=
                      hrecIH bodyClock nl ng nm nf recOutcome recClock hrec
                    simp only [Option.pure_def] at hrun
                    have hpair := Option.some.inj hrun
                    rw [← hpair]
                    exact List.IsPrefix.trans (by simpa [panResultFfi] using hb) hr
                | broke nl ng nm nf =>
                  simp only [Option.pure_def] at hrun
                  have hpair := Option.some.inj hrun
                  rw [← hpair]
                  simpa [panResultFfi] using hb
                | returned l g m f vs =>
                  simp only [Option.pure_def] at hrun
                  have hpair := Option.some.inj hrun
                  rw [← hpair]
                  exact hb
                | raised l g m f ex v =>
                  simp only [Option.pure_def] at hrun
                  have hpair := Option.some.inj hrun
                  rw [← hpair]
                  exact hb
                | finalFfi l g m f ev =>
                  simp only [Option.pure_def] at hrun
                  have hpair := Option.some.inj hrun
                  rw [← hpair]
                  exact hb
      | rStruct fields => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
      | nStruct nm fields => simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
  · -- case10: Prog tick clock 0
    intro memoryAccess contracts memoryHandler _fuel locals globals memory ffi outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    simp only [Option.pure_def] at hrun
    have hpair := Option.some.inj hrun
    rw [← hpair]
    simp only [panValueFfiClockTimeout, panResultFfi]
    exact List.prefix_refl _
  · -- case11: Prog tick clock != 0
    intro memoryAccess contracts memoryHandler _fuel locals globals memory ffi clock hclock outcome resultClock hrun
    simp only [evalPanValueFfiClockProg, if_neg hclock, Option.pure_def] at hrun
    have hpair := Option.some.inj hrun
    rw [← hpair]
    simp only [panResultFfi]
    exact List.prefix_refl _
  · -- case12: Prog fallback (residual / leaf)
    intro _fuel locals globals memory ffi clock program memoryAccess contracts memoryHandler hdec hseq hite hcall hdecCall hwhile htick outcome resultClock hrun
    simp only [evalPanValueFfiClockProg, hdec, hseq, hite, hcall, hdecCall, hwhile, htick,
      evalPanValueFfiClockLeaf, Function.comp_def] at hrun
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨⟨r, s⟩, hstep, heq⟩ := hrun
    have ho : outcome = (PanValueFfiClockOutcome.control r : PanValueFfiClockOutcome α σ) :=
      congrArg Prod.fst heq.symm
    have hc : resultClock = clock := congrArg Prod.snd heq.symm
    rw [ho, hc]
    exact hleaf locals globals memory ffi clock program r s memoryAccess contracts memoryHandler hstep


inductive PanValueFfiEventSafeLeaf : Prog α → Prop
  | skip : PanValueFfiEventSafeLeaf (.skip : Prog α)
  | assign (kind : VarKind) (name : VarName) (value : Exp α) :
      PanValueFfiEventSafeLeaf (.assign kind name value)
  | primitive (name : VarName) (operator : PrimOp) (args : List (Exp α)) :
      PanValueFfiEventSafeLeaf (.primitive name operator args)
  | store (address value : Exp α) : PanValueFfiEventSafeLeaf (.store address value)
  | store32 (address value : Exp α) : PanValueFfiEventSafeLeaf (.store32 address value)
  | storeByte (address value : Exp α) : PanValueFfiEventSafeLeaf (.storeByte address value)
  | break : PanValueFfiEventSafeLeaf (.break : Prog α)
  | continue : PanValueFfiEventSafeLeaf (.continue : Prog α)
  | raise (exception : ExceptionId) (value : Exp α) :
      PanValueFfiEventSafeLeaf (.raise exception value)
  | return (value : Exp α) : PanValueFfiEventSafeLeaf (.return value)
  | shMemLoad (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α) :
      PanValueFfiEventSafeLeaf (.shMemLoad size kind name address)
  | shMemStore (size : OpSize) (address value : Exp α) :
      PanValueFfiEventSafeLeaf (.shMemStore size address value)

set_option linter.unusedSimpArgs false in
theorem evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α) (hleaf : PanValueFfiEventSafeLeaf program)
    (result : PanValueFfiControlResult α σ) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) (clock : Nat)
    (hstep : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (Nat.succ fuel) locals globals memory ffi
      program (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (result, steps)) :
    ffi.ioEvents <+: (panResultFfi ((.control result : PanValueFfiClockOutcome α σ), clock)).ioEvents := by
  cases hleaf with
  | skip =>
      rw [evalPanValueFfiProgSteps] at hstep
      simp only [Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      simp only [panResultFfi]
      exact List.prefix_refl _
  | assign kind name value =>
      cases kind <;>
      · rw [evalPanValueFfiProgSteps] at hstep
        cases hvalue : evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess) with
        | none =>
            simp only [hvalue, Option.bind_eq_bind, Option.bind_none] at hstep
            exact absurd hstep (by simp)
        | some pair =>
            obtain ⟨valueResult, valueSteps⟩ := pair
            simp only [hvalue, Option.bind_eq_bind, Option.bind_some] at hstep
            split at hstep
            · obtain ⟨rfl, rfl⟩ := hstep
              simp only [panResultFfi]
              exact List.prefix_refl _
            · simp at hstep
  | primitive name operator args =>
      rw [evalPanValueFfiProgSteps] at hstep
      cases hvalues : evalPanValueExpsCounted structs locals globals memory
        baseAddress topAddress bytesInWord args (memoryAccess := memoryAccess) with
      | none =>
          simp only [hvalues, Option.bind_eq_bind, Option.bind_none] at hstep
          exact absurd hstep (by simp)
      | some pair =>
          obtain ⟨valuesResult, valueSteps⟩ := pair
          simp only [hvalues, Option.bind_eq_bind, Option.bind_some] at hstep
          cases hprim : primitive operator valuesResult with
          | none =>
              simp only [hprim, Option.bind_eq_bind, Option.bind_none] at hstep
              exact absurd hstep (by simp)
          | some primValue =>
              simp only [hprim, Option.bind_eq_bind, Option.bind_some] at hstep
              cases hold : locals name with
              | none =>
                  simp only [hold, Option.bind_eq_bind, Option.bind_none] at hstep
                  exact absurd hstep (by simp)
              | some oldValue =>
                  simp only [hold, Option.bind_eq_bind, Option.bind_some] at hstep
                  split at hstep
                  · obtain ⟨rfl, rfl⟩ := hstep
                    simp only [panResultFfi]
                    exact List.prefix_refl _
                  · simp at hstep
  | store address value =>
      rw [evalPanValueFfiProgSteps] at hstep
      cases haddress : evalPanValueExpCounted structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess) with
      | none =>
          simp only [haddress, Option.bind_eq_bind, Option.bind_none] at hstep
          exact absurd hstep (by simp)
      | some pair =>
          obtain ⟨addressResult, addressSteps⟩ := pair
          simp only [haddress, Option.bind_eq_bind, Option.bind_some] at hstep
          cases hvalue : evalPanValueExpCounted structs locals globals memory
            baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess) with
          | none =>
              simp only [hvalue, Option.bind_eq_bind, Option.bind_none] at hstep
              exact absurd hstep (by simp)
          | some pair2 =>
              obtain ⟨valueResult, valueSteps⟩ := pair2
              simp only [hvalue, Option.bind_eq_bind, Option.bind_some] at hstep
              cases addressResult with
              | word addressWord =>
                  cases hstore : panValueStoreWithAccess memory bytesInWord
                    addressWord valueResult memoryAccess with
                  | none =>
                      simp only [hstore, Option.bind_eq_bind, Option.bind_none] at hstep
                      exact absurd hstep (by simp)
                  | some memory' =>
                      simp only [hstore, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
                      obtain ⟨rfl, rfl⟩ := hstep
                      simp only [panResultFfi]
                      exact List.prefix_refl _
              | rStruct _ => simp at hstep
              | nStruct _ _ => simp at hstep
  | «break» =>
      rw [evalPanValueFfiProgSteps] at hstep
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      simp only [panResultFfi]
      exact List.prefix_refl _
  | «continue» =>
      rw [evalPanValueFfiProgSteps] at hstep
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      simp only [panResultFfi]
      exact List.prefix_refl _
  | raise exception value =>
      rw [evalPanValueFfiProgSteps] at hstep
      cases hvalue : evalPanValueExpCounted structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess) with
      | none =>
          simp only [hvalue, Option.bind_eq_bind, Option.bind_none] at hstep
          exact absurd hstep (by simp)
      | some pair =>
          obtain ⟨valueResult, valueSteps⟩ := pair
          simp only [hvalue, Option.bind_eq_bind, Option.bind_some] at hstep
          split at hstep
          · obtain ⟨rfl, rfl⟩ := hstep
            simp only [panResultFfi]
            exact List.prefix_refl _
          · simp at hstep
  | «return» value =>
      rw [evalPanValueFfiProgSteps] at hstep
      cases hvalue : evalPanValueExpCounted structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess) with
      | none =>
          simp only [hvalue, Option.bind_eq_bind, Option.bind_none] at hstep
          exact absurd hstep (by simp)
      | some pair =>
          obtain ⟨valueResult, valueSteps⟩ := pair
          simp only [hvalue, Option.bind_eq_bind, Option.bind_some] at hstep
          split at hstep
          · obtain ⟨rfl, rfl⟩ := hstep
            simp only [panResultFfi]
            exact List.prefix_refl _
          · simp at hstep
  | store32 address value =>
      rw [evalPanValueFfiProgSteps] at hstep
      cases haddress : evalPanValueExpCounted structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess) with
      | none =>
          simp only [haddress, Option.bind_eq_bind, Option.bind_none] at hstep
          exact absurd hstep (by simp)
      | some pair =>
          obtain ⟨addressResult, addressSteps⟩ := pair
          simp only [haddress, Option.bind_eq_bind, Option.bind_some] at hstep
          cases hvalue : evalPanValueExpCounted structs locals globals memory
            baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess) with
          | none =>
              simp only [hvalue, Option.bind_eq_bind, Option.bind_none] at hstep
              exact absurd hstep (by simp)
          | some pair2 =>
              obtain ⟨valueResult, valueSteps⟩ := pair2
              simp only [hvalue, Option.bind_eq_bind, Option.bind_some] at hstep
              cases addressResult with
              | word addressWord =>
                  cases valueResult with
                  | word valueWord =>
                      cases memoryAccess with
                      | none =>
                          simp only [Option.bind_eq_bind, Option.bind_some] at hstep
                          obtain ⟨rfl, rfl⟩ := hstep
                          simp only [panResultFfi]
                          exact List.prefix_refl _
                      | some access =>
                          simp only [Option.bind_eq_bind] at hstep
                          cases hm : access.store32 access.domain memory bytesInWord
                            addressWord valueWord with
                          | none =>
                              simp only [hm, Option.bind_eq_bind, Option.bind_none] at hstep
                              exact absurd hstep (by simp)
                          | some memory' =>
                              simp only [hm, Option.bind_eq_bind, Option.bind_some] at hstep
                              obtain ⟨rfl, rfl⟩ := hstep
                              simp only [panResultFfi]
                              exact List.prefix_refl _
                  | rStruct _ => simp at hstep
                  | nStruct _ _ => simp at hstep
              | rStruct _ => simp at hstep
              | nStruct _ _ => simp at hstep
  | storeByte address value =>
      rw [evalPanValueFfiProgSteps] at hstep
      cases haddress : evalPanValueExpCounted structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess) with
      | none =>
          simp only [haddress, Option.bind_eq_bind, Option.bind_none] at hstep
          exact absurd hstep (by simp)
      | some pair =>
          obtain ⟨addressResult, addressSteps⟩ := pair
          simp only [haddress, Option.bind_eq_bind, Option.bind_some] at hstep
          cases hvalue : evalPanValueExpCounted structs locals globals memory
            baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess) with
          | none =>
              simp only [hvalue, Option.bind_eq_bind, Option.bind_none] at hstep
              exact absurd hstep (by simp)
          | some pair2 =>
              obtain ⟨valueResult, valueSteps⟩ := pair2
              simp only [hvalue, Option.bind_eq_bind, Option.bind_some] at hstep
              cases addressResult with
              | word addressWord =>
                  cases valueResult with
                  | word valueWord =>
                      cases memoryAccess with
                      | none =>
                          simp only [Option.bind_eq_bind, Option.bind_some] at hstep
                          obtain ⟨rfl, rfl⟩ := hstep
                          simp only [panResultFfi]
                          exact List.prefix_refl _
                      | some access =>
                          simp only [Option.bind_eq_bind] at hstep
                          cases hm : access.storeByte access.domain memory bytesInWord
                            addressWord valueWord with
                          | none =>
                              simp only [hm, Option.bind_eq_bind, Option.bind_none] at hstep
                              exact absurd hstep (by simp)
                          | some memory' =>
                              simp only [hm, Option.bind_eq_bind, Option.bind_some] at hstep
                              obtain ⟨rfl, rfl⟩ := hstep
                              simp only [panResultFfi]
                              exact List.prefix_refl _
                  | rStruct _ => simp at hstep
                  | nStruct _ _ => simp at hstep
              | rStruct _ => simp at hstep
              | nStruct _ _ => simp at hstep
  | shMemLoad size kind name address =>
      rw [evalPanValueFfiProgSteps] at hstep
      cases haddress : evalPanValueExpCounted structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess) with
      | none =>
          simp only [haddress, Option.bind_eq_bind, Option.bind_none] at hstep
          exact absurd hstep (by simp)
      | some pair =>
          obtain ⟨addressResult, addressSteps⟩ := pair
          simp only [haddress, Option.bind_eq_bind, Option.bind_some] at hstep
          cases addressResult with
          | word addressWord =>
              by_cases hvalid :
                  panValueSharedLoadValid structs locals globals kind name (.word 0) = true
              · simp only [hvalid, if_true, Option.bind_eq_bind] at hstep
                cases hload : panValueFfiSharedLoad context ffi size addressWord with
                | none =>
                    simp only [hload, Option.bind_eq_bind, Option.bind_none] at hstep
                    exact absurd hstep (by simp)
                | some res =>
                    cases res with
                    | loaded nextFfi value =>
                        simp only [hload, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
                        cases kind <;>
                        · simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
                          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                          obtain ⟨rfl, rfl⟩ := hstep
                          simp only [panResultFfi]
                          simpa [panValueFfiSharedResultFfi] using
                            panValueFfiSharedLoad_ioEvents_prefix context ffi size addressWord
                              (.loaded nextFfi value) hload
                    | final nextFfi event =>
                        simp only [hload, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
                        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                        obtain ⟨rfl, rfl⟩ := hstep
                        simp only [panResultFfi]
                        simpa [panValueFfiSharedResultFfi] using
                          panValueFfiSharedLoad_ioEvents_prefix context ffi size addressWord
                            (.final nextFfi event) hload
                    | stored _ =>
                        simp only [hload, Option.bind_eq_bind, Option.bind_none] at hstep
                        exact absurd hstep (by simp)
              · simp only [hvalid, if_false] at hstep
                exact absurd hstep (by simp)
          | rStruct _ => simp at hstep
          | nStruct _ _ => simp at hstep
  | shMemStore size address value =>
      rw [evalPanValueFfiProgSteps] at hstep
      cases haddress : evalPanValueExpCounted structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess) with
      | none =>
          simp only [haddress, Option.bind_eq_bind, Option.bind_none] at hstep
          exact absurd hstep (by simp)
      | some pair =>
          obtain ⟨addressResult, addressSteps⟩ := pair
          simp only [haddress, Option.bind_eq_bind, Option.bind_some] at hstep
          cases hvalue : evalPanValueExpCounted structs locals globals memory
            baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess) with
          | none =>
              simp only [hvalue, Option.bind_eq_bind, Option.bind_none] at hstep
              exact absurd hstep (by simp)
          | some pair2 =>
              obtain ⟨valueResult, valueSteps⟩ := pair2
              simp only [hvalue, Option.bind_eq_bind, Option.bind_some] at hstep
              cases addressResult with
              | word addressWord =>
                  cases valueResult with
                  | word valueWord =>
                      cases hstore : panValueFfiSharedStore context ffi size addressWord
                        valueWord with
                      | none =>
                          simp only [hstore, Option.bind_eq_bind, Option.bind_none] at hstep
                          exact absurd hstep (by simp)
                      | some res =>
                          cases res with
                          | stored nextFfi =>
                              simp only [hstore, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
                              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                              obtain ⟨rfl, rfl⟩ := hstep
                              simp only [panResultFfi]
                              simpa [panValueFfiSharedResultFfi] using
                                panValueFfiSharedStore_ioEvents_prefix context ffi size
                                  addressWord valueWord (.stored nextFfi) hstore
                          | final nextFfi event =>
                              simp only [hstore, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
                              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                              obtain ⟨rfl, rfl⟩ := hstep
                              simp only [panResultFfi]
                              simpa [panValueFfiSharedResultFfi] using
                                panValueFfiSharedStore_ioEvents_prefix context ffi size
                                  addressWord valueWord (.final nextFfi event) hstore
                          | loaded _ _ =>
                              simp only [hstore, Option.bind_eq_bind, Option.bind_none] at hstep
                              exact absurd hstep (by simp)
                  | rStruct _ => simp at hstep
                  | nStruct _ _ => simp at hstep
              | rStruct _ => simp at hstep
              | nStruct _ _ => simp at hstep



set_option linter.unusedSimpArgs false in
theorem evalPanValueFfiProgSteps_extCall_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (result : PanValueFfiControlResult α σ) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) (clock : Nat)
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : match memoryHandler with
      | none => True
      | some memoryHandler =>
          panValueFfiMemoryHandlerPreservesIoEvents memoryHandler)
    (hstep : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (Nat.succ fuel) locals globals memory ffi
      (.extCall function configuration configurationLength array arrayLength)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (result, steps)) :
    ffi.ioEvents <+: (panResultFfi ((.control result : PanValueFfiClockOutcome α σ), clock)).ioEvents := by
  rw [evalPanValueFfiProgSteps] at hstep
  cases hvalues : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord
      [configuration, configurationLength, array, arrayLength]
      (memoryAccess := memoryAccess) with
  | none =>
      simp only [hvalues, Option.bind_eq_bind, Option.bind_none] at hstep
      exact absurd hstep (by simp)
  | some pair =>
      obtain ⟨valuesResult, valueSteps⟩ := pair
      simp only [hvalues, Option.bind_eq_bind, Option.bind_some] at hstep
      cases valuesResult with
      | nil => simp at hstep
      | cons v1 rest1 =>
        cases rest1 with
        | nil => simp at hstep
        | cons v2 rest2 =>
          cases rest2 with
          | nil => simp at hstep
          | cons v3 rest3 =>
            cases rest3 with
            | nil => simp at hstep
            | cons v4 rest4 =>
              cases rest4 with
              | cons _ _ => simp at hstep
              | nil =>
                cases v1 with
                | word configurationValue =>
                  cases v2 with
                  | word configurationLengthValue =>
                    cases v3 with
                    | word arrayValue =>
                      cases v4 with
                      | word arrayLengthValue =>
                        cases memoryHandler with
                        | some mh =>
                          cases hcall : mh function configurationValue configurationLengthValue
                              arrayValue arrayLengthValue locals memory ffi with
                          | none =>
                            simp only [hcall, Option.bind_eq_bind, Option.bind_none] at hstep
                            cases memoryAccess with
                            | none =>
                              cases hhandler : handler function configurationValue
                                  configurationLengthValue arrayValue arrayLengthValue locals ffi with
                              | none =>
                                simp only [hhandler, Option.bind_eq_bind, Option.bind_none] at hstep
                                exact absurd hstep (by simp)
                              | some pairH =>
                                obtain ⟨nextLocals, nextFfi⟩ := pairH
                                simp only [hhandler, Option.bind_eq_bind, Option.bind_some,
                                  Option.pure_def] at hstep
                                obtain ⟨rfl, rfl⟩ := hstep
                                simp only [panResultFfi]
                                exact hstateful function configurationValue configurationLengthValue
                                  arrayValue arrayLengthValue locals ffi nextLocals nextFfi hhandler
                            | some access =>
                              cases hx : panValueFfiExtCall access context memory bytesInWord ffi
                                  function configurationValue configurationLengthValue arrayValue
                                  arrayLengthValue with
                              | none =>
                                simp only [hx, Option.bind_eq_bind, Option.bind_none] at hstep
                                exact absurd hstep (by simp)
                              | some res =>
                                cases res with
                                | returned nextMemory nextFfi =>
                                  simp only [hx, Option.bind_eq_bind, Option.bind_some,
                                    Option.pure_def] at hstep
                                  obtain ⟨rfl, rfl⟩ := hstep
                                  simp only [panResultFfi]
                                  simpa [panValueFfiExtCallResultFfi] using
                                    panValueFfiExtCall_ioEvents_prefix access context memory
                                      bytesInWord ffi function configurationValue
                                      configurationLengthValue arrayValue arrayLengthValue
                                      (.returned nextMemory nextFfi) hx
                                | final nextFfi event =>
                                  simp only [hx, Option.bind_eq_bind, Option.bind_some,
                                    Option.pure_def] at hstep
                                  obtain ⟨rfl, rfl⟩ := hstep
                                  simp only [panResultFfi]
                                  simpa [panValueFfiExtCallResultFfi] using
                                    panValueFfiExtCall_ioEvents_prefix access context memory
                                      bytesInWord ffi function configurationValue
                                      configurationLengthValue arrayValue arrayLengthValue
                                      (.final nextFfi event) hx
                          | some triple =>
                            obtain ⟨nextLocals, nextMemory, nextFfi⟩ := triple
                            simp only [hcall, Option.bind_eq_bind, Option.bind_some,
                              Option.pure_def] at hstep
                            obtain ⟨rfl, rfl⟩ := hstep
                            simp only [panResultFfi]
                            exact hmemory function configurationValue configurationLengthValue
                              arrayValue arrayLengthValue locals memory ffi nextLocals nextMemory
                              nextFfi hcall
                        | none =>
                          cases memoryAccess with
                          | none =>
                            cases hhandler : handler function configurationValue
                                configurationLengthValue arrayValue arrayLengthValue locals ffi with
                            | none =>
                              simp only [hhandler, Option.bind_eq_bind, Option.bind_none] at hstep
                              exact absurd hstep (by simp)
                            | some pairH =>
                              obtain ⟨nextLocals, nextFfi⟩ := pairH
                              simp only [hhandler, Option.bind_eq_bind, Option.bind_some,
                                Option.pure_def] at hstep
                              obtain ⟨rfl, rfl⟩ := hstep
                              simp only [panResultFfi]
                              exact hstateful function configurationValue configurationLengthValue
                                arrayValue arrayLengthValue locals ffi nextLocals nextFfi hhandler
                          | some access =>
                            cases hx : panValueFfiExtCall access context memory bytesInWord ffi
                                function configurationValue configurationLengthValue arrayValue
                                arrayLengthValue with
                            | none =>
                              simp only [hx, Option.bind_eq_bind, Option.bind_none] at hstep
                              exact absurd hstep (by simp)
                            | some res =>
                              cases res with
                              | returned nextMemory nextFfi =>
                                simp only [hx, Option.bind_eq_bind, Option.bind_some,
                                  Option.pure_def] at hstep
                                obtain ⟨rfl, rfl⟩ := hstep
                                simp only [panResultFfi]
                                simpa [panValueFfiExtCallResultFfi] using
                                  panValueFfiExtCall_ioEvents_prefix access context memory
                                    bytesInWord ffi function configurationValue
                                    configurationLengthValue arrayValue arrayLengthValue
                                    (.returned nextMemory nextFfi) hx
                              | final nextFfi event =>
                                simp only [hx, Option.bind_eq_bind, Option.bind_some,
                                  Option.pure_def] at hstep
                                obtain ⟨rfl, rfl⟩ := hstep
                                simp only [panResultFfi]
                                simpa [panValueFfiExtCallResultFfi] using
                                  panValueFfiExtCall_ioEvents_prefix access context memory
                                    bytesInWord ffi function configurationValue
                                    configurationLengthValue arrayValue arrayLengthValue
                                    (.final nextFfi event) hx
                      | rStruct _ => simp at hstep
                      | nStruct _ _ => simp at hstep
                    | rStruct _ => simp at hstep
                    | nStruct _ _ => simp at hstep
                  | rStruct _ => simp at hstep
                  | nStruct _ _ => simp at hstep
                | rStruct _ => simp at hstep
                | nStruct _ _ => simp at hstep



set_option linter.unusedSimpArgs false in
theorem evalPanValueFfiProgSteps_leaf_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α) (hleaf : PanValueFfiLeafProg program)
    (result : PanValueFfiControlResult α σ) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) (clock : Nat)
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler)
    (hstep : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (Nat.succ fuel) locals globals memory ffi
      program (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (result, steps)) :
    ffi.ioEvents <+: (panResultFfi ((.control result : PanValueFfiClockOutcome α σ), clock)).ioEvents := by
  cases hleaf with
  | skip =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.skip : Prog α) .skip result steps memoryAccess contracts memoryHandler clock hstep
  | assign kind name value =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.assign kind name value) (.assign kind name value) result steps memoryAccess contracts
        memoryHandler clock hstep
  | primitive name operator args =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.primitive name operator args) (.primitive name operator args) result steps memoryAccess
        contracts memoryHandler clock hstep
  | store address value =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.store address value) (.store address value) result steps memoryAccess contracts
        memoryHandler clock hstep
  | store32 address value =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.store32 address value) (.store32 address value) result steps memoryAccess contracts
        memoryHandler clock hstep
  | storeByte address value =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.storeByte address value) (.storeByte address value) result steps memoryAccess contracts
        memoryHandler clock hstep
  | «break» =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.break : Prog α) .break result steps memoryAccess contracts memoryHandler clock hstep
  | «continue» =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.continue : Prog α) .continue result steps memoryAccess contracts memoryHandler clock hstep
  | extCall function configuration configurationLength array arrayLength =>
      cases memoryHandler with
      | none =>
          exact evalPanValueFfiProgSteps_extCall_ioEvents_prefix context primitive handler structs
            functions baseAddress topAddress bytesInWord fuel locals globals memory ffi function
            configuration configurationLength array arrayLength result steps memoryAccess contracts
            none clock hstateful True.intro hstep
      | some memoryHandler =>
          exact evalPanValueFfiProgSteps_extCall_ioEvents_prefix context primitive handler structs
            functions baseAddress topAddress bytesInWord fuel locals globals memory ffi function
            configuration configurationLength array arrayLength result steps memoryAccess contracts
            (some memoryHandler) clock hstateful (hmemory memoryHandler) hstep
  | raise exception value =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.raise exception value) (.raise exception value) result steps memoryAccess contracts
        memoryHandler clock hstep
  | «return» value =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.return value) (.return value) result steps memoryAccess contracts memoryHandler clock hstep
  | shMemLoad size kind name address =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.shMemLoad size kind name address) (.shMemLoad size kind name address) result steps
        memoryAccess contracts memoryHandler clock hstep
  | shMemStore size address value =>
      exact evalPanValueFfiProgSteps_eventSafeLeaf_ioEvents_prefix context primitive handler
        structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (.shMemStore size address value) (.shMemStore size address value) result steps
        memoryAccess contracts memoryHandler clock hstep



set_option linter.unusedSimpArgs false in
theorem evalPanValueFfiClockProg_leaf_of_handlerPreserves
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α) (hleaf : PanValueFfiLeafProg program)
    (result : PanValueFfiControlResult α σ) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (hstep : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi program
      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
      some (result, steps)) :
    evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
        bytesInWord (fuel + 1) locals globals memory ffi clock program memoryAccess contracts
        memoryHandler = some (.control result, clock) ∧
      ffi.ioEvents <+: (panResultFfi ((.control result : PanValueFfiClockOutcome α σ), clock)).ioEvents :=
  ⟨evalPanValueFfiClockProg_leaf_some context primitive handler structs functions baseAddress
      topAddress bytesInWord fuel locals globals memory ffi clock program memoryAccess contracts
      memoryHandler hleaf result steps hstep,
   evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs functions
      baseAddress topAddress bytesInWord 0 locals globals memory ffi program hleaf result steps
      memoryAccess contracts memoryHandler clock hstateful hmemory hstep⟩



theorem panValueFfiStatefulHandlerPreservesIoEvents_fails
    (α : Type u) (σ : Type v) :
    panValueFfiStatefulHandlerPreservesIoEvents (α := α) (σ := σ)
      (fun (_ : FunName) (_ _ _ _ : α) (_ : VarName → Option (PanValue α))
        (_ : FfiState σ) => none) := by
  intro function configuration configurationLength array arrayLength locals ffi nextLocals
    nextFfi h
  exact absurd h (by simp)

theorem panValueFfiMemoryHandlerPreservesIoEvents_fails
    (α : Type u) (σ : Type v) :
    panValueFfiMemoryHandlerPreservesIoEvents (α := α) (σ := σ)
      (fun (_ : FunName) (_ _ _ _ : α) (_ : VarName → Option (PanValue α))
        (_ : α → Option (PanValue α)) (_ : FfiState σ) => none) := by
  intro function configuration configurationLength array arrayLength locals memory ffi nextLocals
    nextMemory nextFfi h
  exact absurd h (by simp)

theorem panValueFfiStatefulHandlerPreservesIoEvents_ffi
    (α : Type u) (σ : Type v) :
    panValueFfiStatefulHandlerPreservesIoEvents (α := α) (σ := σ)
      (fun (_ : FunName) (_ _ _ _ : α) (_ : VarName → Option (PanValue α))
        (ffi : FfiState σ) => some (fun _ => none, ffi)) := by
  intro function configuration configurationLength array arrayLength locals ffi nextLocals
    nextFfi h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact List.prefix_refl _

theorem panValueFfiMemoryHandlerPreservesIoEvents_ffi
    (α : Type u) (σ : Type v) :
    panValueFfiMemoryHandlerPreservesIoEvents (α := α) (σ := σ)
      (fun (_ : FunName) (_ _ _ _ : α) (_ : VarName → Option (PanValue α))
        (_ : α → Option (PanValue α)) (ffi : FfiState σ) =>
          some (fun _ => none, fun _ => none, ffi)) := by
  intro function configuration configurationLength array arrayLength locals memory ffi nextLocals
    nextMemory nextFfi h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, rfl⟩ := h
  exact List.prefix_refl _

set_option linter.unusedSimpArgs false in
theorem evalPanValueFfiProgSteps_ite_one_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (condition : Exp α) (thenBranch elseBranch : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiProgSteps context primitive handler structs functions baseAddress topAddress
      bytesInWord 1 locals globals memory ffi (.ite condition thenBranch elseBranch)
      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
      none := by
  rw [evalPanValueFfiProgSteps]
  simp only [evalPanValueFfiProgSteps]
  cases hx : evalPanValueExpCounted structs locals globals memory baseAddress topAddress
    bytesInWord condition (memoryAccess := memoryAccess) with
  | none => rfl
  | some p => obtain ⟨a, b⟩ := p; cases a <;> simp [Option.bind_eq_bind]

set_option linter.unusedSimpArgs false in
theorem evalPanValueFfiProgSteps_dec_one_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiProgSteps context primitive handler structs functions baseAddress topAddress
      bytesInWord 1 locals globals memory ffi (.dec name shape value body)
      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
      none := by
  rw [evalPanValueFfiProgSteps]
  simp only [evalPanValueFfiProgSteps, Option.bind_eq_bind]
  cases hv : evalPanValueExpCounted structs locals globals memory baseAddress topAddress
    bytesInWord value (memoryAccess := memoryAccess) with
  | none => simp [hv]
  | some p =>
      obtain ⟨a, b⟩ := p
      by_cases hm : panShapeMatches (panValueShape structs a) shape = true <;> simp [hv, hm]

theorem evalPanValueFfiProgSteps_seq_one_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (first second : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiProgSteps context primitive handler structs functions baseAddress topAddress
      bytesInWord 1 locals globals memory ffi (.seq first second)
      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
      none := by
  rw [evalPanValueFfiProgSteps]
  simp only [evalPanValueFfiProgSteps, Option.bind_eq_bind, Option.bind_none]

theorem evalPanValueFfiProgSteps_call_one_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiProgSteps context primitive handler structs functions baseAddress topAddress
      bytesInWord 1 locals globals memory ffi (.call info function arguments)
      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
      none := by
  rw [evalPanValueFfiProgSteps]
  simp only [evalPanValueFfiCallSteps, Option.bind_eq_bind, Option.bind_none]

theorem evalPanValueFfiProgSteps_decCall_one_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName) (arguments : List (Exp α))
    (body : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiProgSteps context primitive handler structs functions baseAddress topAddress
      bytesInWord 1 locals globals memory ffi (.decCall name shape function arguments body)
      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
      none := by
  rw [evalPanValueFfiProgSteps]
  simp only [evalPanValueFfiCallSteps, Option.bind_eq_bind, Option.bind_none]

set_option linter.unusedSimpArgs false in
theorem evalPanValueFfiProgSteps_while_one_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (condition : Exp α) (body : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) (clock : Nat)
    (result : PanValueFfiControlResult α σ) (steps : Nat)
    (hstep : evalPanValueFfiProgSteps context primitive handler structs functions baseAddress
      topAddress bytesInWord 1 locals globals memory ffi (.while condition body)
      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
      some (result, steps)) :
    ffi.ioEvents <+: (panResultFfi (((.control result) : PanValueFfiClockOutcome α σ), clock)).ioEvents := by
  rw [evalPanValueFfiProgSteps] at hstep
  simp only [evalPanValueFfiProgSteps] at hstep
  cases hc : evalPanValueExpCounted structs locals globals memory baseAddress topAddress
    bytesInWord condition (memoryAccess := memoryAccess) with
  | none => simp [hc] at hstep
  | some p =>
      obtain ⟨v, cs⟩ := p
      cases v with
      | word cv =>
          by_cases hz : (cv == 0) = true
          · simp only [hc, hz, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            simp only [panResultFfi]
            exact List.prefix_refl _
          · simp only [hc, hz, Option.bind_eq_bind, Option.bind_some] at hstep
            simp at hstep
          | rStruct _ => simp [hc] at hstep
      | nStruct _ _ => simp [hc] at hstep

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem evalPanValueFfiProgSteps_one_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (clock : Nat) (result : PanValueFfiControlResult α σ) (steps : Nat)
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler)
    (hstep : evalPanValueFfiProgSteps context primitive handler structs functions baseAddress
      topAddress bytesInWord 1 locals globals memory ffi program
      (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
      some (result, steps)) :
    ffi.ioEvents <+: (panResultFfi ((.control result : PanValueFfiClockOutcome α σ), clock)).ioEvents := by
  cases program with
  | skip =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.skip : Prog α) .skip result steps memoryAccess contracts memoryHandler clock
        hstateful hmemory hstep
  | dec name shape value body =>
      rw [evalPanValueFfiProgSteps_dec_one_none context primitive handler structs functions
        baseAddress topAddress bytesInWord locals globals memory ffi name shape value body
        memoryAccess contracts memoryHandler] at hstep
      exact absurd hstep (by simp)
  | assign kind name value =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.assign kind name value) (.assign kind name value) result steps memoryAccess contracts
        memoryHandler clock hstateful hmemory hstep
  | primitive name operator args =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.primitive name operator args) (.primitive name operator args) result steps memoryAccess
        contracts memoryHandler clock hstateful hmemory hstep
  | store address value =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.store address value) (.store address value) result steps memoryAccess contracts
        memoryHandler clock hstateful hmemory hstep
  | store32 address value =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.store32 address value) (.store32 address value) result steps memoryAccess contracts
        memoryHandler clock hstateful hmemory hstep
  | storeByte address value =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.storeByte address value) (.storeByte address value) result steps memoryAccess contracts
        memoryHandler clock hstateful hmemory hstep
  | seq first second =>
      rw [evalPanValueFfiProgSteps_seq_one_none context primitive handler structs functions
        baseAddress topAddress bytesInWord locals globals memory ffi first second memoryAccess
        contracts memoryHandler] at hstep
      exact absurd hstep (by simp)
  | ite condition thenBranch elseBranch =>
      rw [evalPanValueFfiProgSteps_ite_one_none context primitive handler structs functions
        baseAddress topAddress bytesInWord locals globals memory ffi condition thenBranch
        elseBranch memoryAccess contracts memoryHandler] at hstep
      exact absurd hstep (by simp)
  | «while» condition body =>
      exact evalPanValueFfiProgSteps_while_one_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord locals globals memory ffi condition body
        memoryAccess contracts memoryHandler clock result steps hstep
  | «break» =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.break : Prog α) .break result steps memoryAccess contracts memoryHandler clock
        hstateful hmemory hstep
  | «continue» =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.continue : Prog α) .continue result steps memoryAccess contracts memoryHandler clock
        hstateful hmemory hstep
  | call info function arguments =>
      rw [evalPanValueFfiProgSteps_call_one_none context primitive handler structs functions
        baseAddress topAddress bytesInWord locals globals memory ffi info function arguments
        memoryAccess contracts memoryHandler] at hstep
      exact absurd hstep (by simp)
  | decCall name shape function arguments body =>
      rw [evalPanValueFfiProgSteps_decCall_one_none context primitive handler structs functions
        baseAddress topAddress bytesInWord locals globals memory ffi name shape function arguments
        body memoryAccess contracts memoryHandler] at hstep
      exact absurd hstep (by simp)
  | extCall function configuration configurationLength array arrayLength =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.extCall function configuration configurationLength array arrayLength)
        (.extCall function configuration configurationLength array arrayLength) result
        steps memoryAccess contracts memoryHandler clock hstateful hmemory hstep
  | raise exception value =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.raise exception value) (.raise exception value) result steps memoryAccess contracts
        memoryHandler clock hstateful hmemory hstep
  | «return» value =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.return value) (.return value) result steps memoryAccess contracts
        memoryHandler clock hstateful hmemory hstep
  | shMemLoad size kind name address =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.shMemLoad size kind name address) (.shMemLoad size kind name address) result steps
        memoryAccess contracts memoryHandler clock hstateful hmemory hstep
  | shMemStore size address value =>
      exact evalPanValueFfiProgSteps_leaf_ioEvents_prefix context primitive handler structs
        functions baseAddress topAddress bytesInWord 0 locals globals memory ffi
        (.shMemStore size address value) (.shMemStore size address value) result steps
        memoryAccess contracts memoryHandler clock hstateful hmemory hstep
  | tick =>
      rw [evalPanValueFfiProgSteps] at hstep
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      simp only [panResultFfi]
      exact List.prefix_refl _
  | annot tag text =>
      rw [evalPanValueFfiProgSteps] at hstep
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      simp only [panResultFfi]
      exact List.prefix_refl _

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem evalPanValueFfiClockProg_ioEvents_prefix_of_handlerPreserves
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler) :
    ∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) (program : Prog α)
      (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
      (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
      (outcome : PanValueFfiClockOutcome α σ) (resultClock : Nat),
      evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock program
        (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
        some (outcome, resultClock) →
      ffi.ioEvents <+: (panResultFfi (outcome, resultClock)).ioEvents :=
  (evalPanValueFfiClock_ioEvents_prefix context primitive handler structs functions baseAddress
    topAddress bytesInWord
    (fun locals globals memory ffi clock program result steps memoryAccess contracts memoryHandler
        hstep =>
      evalPanValueFfiProgSteps_one_ioEvents_prefix context primitive handler structs functions
        baseAddress topAddress bytesInWord locals globals memory ffi program memoryAccess contracts
        memoryHandler clock result steps hstateful hmemory hstep)).2

/-! Lift the generic clocked prefix theorem through Cake's production
    `panSemEvaluate` fuel/state wrapper.  This is the top-level event-prefix
    premise needed by the semantic state-rel induction; handler and memory
    preservation remain explicit rather than being hidden in the hook type. -/
theorem panSemEvaluate_ioEvents_prefix_of_handlerPreserves
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α)
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler) :
    ∀ result,
      panSemEvaluate context primitive handler state program = some result →
      state.ffi.ioEvents <+: panResultEvents (some result) := by
  intro result hrun
  unfold panSemEvaluate panSemEvaluateWithFuel at hrun
  have hprefix := evalPanValueFfiClockProg_ioEvents_prefix_of_handlerPreserves
    context primitive handler state.structs state.functions state.baseAddress
    state.topAddress state.bytesInWord hstateful hmemory
    (panSemEvaluateFuel state program) state.locals state.globals state.memory
    state.ffi state.clock program state.memoryAccess state.contracts
    state.memoryHandler result.1 result.2 hrun
  simpa [panResultEvents] using hprefix

/-! Expose the full Cake-style mutual prefix induction at the production
    `panSemEvaluate` boundary.  The unit-fuel leaf event relation stays an
    explicit premise, so this bridge does not hide the only backend-specific
    obligation in the top-level correctness theorem. -/
theorem panSemEvaluate_ioEvents_prefix_of_leaf
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α)
    (hleaf : ∀ (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
      (program : Prog α) (result : PanValueFfiControlResult α σ) (steps : Nat)
      (memoryAccess : Option (PanValueMemoryAccess α))
      (contracts : Option PanValueCallContracts)
      (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiProgSteps context primitive handler state.structs state.functions
        state.baseAddress state.topAddress state.bytesInWord 1 locals globals memory ffi
        program (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) = some (result, steps) →
      ffi.ioEvents <+:
        (panResultFfi ((.control result : PanValueFfiClockOutcome α σ), clock)).ioEvents) :
    ∀ outcome returnedClock,
      panSemEvaluate context primitive handler state program =
        some (outcome, returnedClock) →
      state.ffi.ioEvents <+: panResultEvents (some (outcome, returnedClock)) := by
  intro outcome returnedClock hrun
  unfold panSemEvaluate panSemEvaluateWithFuel at hrun
  have hclockPrefix := evalPanValueFfiClock_ioEvents_prefix
    context primitive handler state.structs state.functions state.baseAddress
    state.topAddress state.bytesInWord hleaf
  have hprefix := hclockPrefix.2
    (panSemEvaluateFuel state program)
    state.locals state.globals state.memory state.ffi state.clock program
    state.memoryAccess state.contracts state.memoryHandler outcome returnedClock hrun
  simpa [panResultEvents] using hprefix

/-! The zero-clock `While` timeout is the base case of Cake's
    `evaluate_add_clock_io_events_mono`: the low-clock result exposes exactly
    the incoming FFI trace, so the generic high-clock prefix theorem lifts it
    to a cross-clock result prefix. -/
theorem evalPanValueFfiClockProg_while_zero_timeout_cross_clock_ioEvents_prefix
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
    (condition : Exp α) (body : Prog α) (extra : Nat)
    (conditionValue : α)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := none) = some (.word conditionValue))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    (highOutcome : PanValueFfiClockOutcome α σ) (highClock : Nat)
    (hhigh : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (0 + extra) (.while condition body) = some (highOutcome, highClock))
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      (.while condition body) =
        some (.timeout (fun _ => none) globals memory ffi, 0) ∧
      (panResultFfi
          (.timeout (fun _ => none) globals memory ffi, 0)).ioEvents <+:
        (panResultFfi (highOutcome, highClock)).ioEvents := by
  have hlow := evalPanValueFfiClockProg_while_timeout_ioEvents_prefix
    context primitive handler structs functions baseAddress topAddress bytesInWord fuel
    locals globals memory ffi 0 condition body (memoryAccess := none)
    (contracts := none) (memoryHandler := none) conditionValue hcondition
    hconditionNonzero (by simp)
  have hhighPrefix := evalPanValueFfiClockProg_ioEvents_prefix_of_handlerPreserves
    context primitive handler structs functions baseAddress topAddress bytesInWord
    hstateful hmemory (fuel + 1) locals globals memory ffi (0 + extra)
    (.while condition body)
    (memoryAccess := none) (contracts := none) (memoryHandler := none)
    highOutcome highClock (by simpa using hhigh)
  refine ⟨hlow.1, ?_⟩
  simpa [panResultFfi] using hhighPrefix

/-! The zero-clock `Tick` timeout is the other direct base case of
    `evaluate_add_clock_io_events_mono`: unlike a `While`, it needs no
    expression premise, and its low-clock trace is still exactly the incoming
    FFI trace. -/
theorem evalPanValueFfiClockProg_tick_zero_timeout_cross_clock_ioEvents_prefix
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
    (extra : Nat)
    (highOutcome : PanValueFfiClockOutcome α σ) (highClock : Nat)
    (hhigh : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (0 + extra) .tick = some (highOutcome, highClock))
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      .tick = some (.timeout (fun _ => none) globals memory ffi, 0) ∧
      (panResultFfi
          (.timeout (fun _ => none) globals memory ffi, 0)).ioEvents <+:
        (panResultFfi (highOutcome, highClock)).ioEvents := by
  have hlow : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      .tick = some (.timeout (fun _ => none) globals memory ffi, 0) := by
    simp [evalPanValueFfiClockProg, panValueFfiClockTimeout]
  have hhighPrefix := evalPanValueFfiClockProg_ioEvents_prefix_of_handlerPreserves
    context primitive handler structs functions baseAddress topAddress bytesInWord
    hstateful hmemory (fuel + 1) locals globals memory ffi (0 + extra) .tick
    (memoryAccess := none) (contracts := none) (memoryHandler := none)
    highOutcome highClock (by simpa using hhigh)
  refine ⟨hlow, ?_⟩
  simpa [panResultFfi] using hhighPrefix

/-! A zero-clock `Seq` whose first component times out is the recursive
    sequence base case of Cake's `evaluate_add_clock_io_events_mono`. The
    first component's incoming-trace equality remains explicit because a
    general zero-clock program may itself perform an FFI event before timing
    out. -/
theorem evalPanValueFfiClockProg_seq_zero_timeout_cross_clock_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (first second : Prog α)
    (middleLocals middleGlobals : VarName → Option (PanValue α))
    (middleMemory : α → Option (PanValue α)) (middleFfi : FfiState σ)
    (extra : Nat)
    (highOutcome : PanValueFfiClockOutcome α σ) (highClock : Nat)
    (hfirst : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi 0 first =
      some (.timeout middleLocals middleGlobals middleMemory middleFfi, 0))
    (hfirstEvents : middleFfi.ioEvents = ffi.ioEvents)
    (hhigh : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (0 + extra) (.seq first second) = some (highOutcome, highClock))
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      (.seq first second) =
      some (.timeout middleLocals middleGlobals middleMemory middleFfi, 0) ∧
      (panResultFfi
        (.timeout middleLocals middleGlobals middleMemory middleFfi, 0)).ioEvents <+:
        (panResultFfi (highOutcome, highClock)).ioEvents := by
  have hlow := evalPanValueFfiClockProg_seq_timeout context primitive handler structs
    functions baseAddress topAddress bytesInWord fuel 0 0 locals globals memory ffi
    middleLocals middleGlobals middleMemory middleFfi first second
    (memoryAccess := none) (contracts := none) hfirst
  have hhighPrefix := evalPanValueFfiClockProg_ioEvents_prefix_of_handlerPreserves
    context primitive handler structs functions baseAddress topAddress bytesInWord
    hstateful hmemory (fuel + 1) locals globals memory ffi (0 + extra)
    (.seq first second) none none none highOutcome highClock (by simpa using hhigh)
  refine ⟨hlow, ?_⟩
  simpa [panResultFfi, hfirstEvents] using hhighPrefix

/-! The nonzero-clock counterpart of the preceding `Seq` timeout base case.
    When the first component has already consumed a positive clock but leaves
    the incoming FFI trace unchanged, the same explicit preservation argument
    supplies the recursive Cake prefix step. -/
theorem evalPanValueFfiClockProg_seq_timeout_cross_clock_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock extra : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (first second : Prog α)
    (middleLocals middleGlobals : VarName → Option (PanValue α))
    (middleMemory : α → Option (PanValue α)) (middleFfi : FfiState σ)
    (firstClock : Nat)
    (highOutcome : PanValueFfiClockOutcome α σ) (highClock : Nat)
    (hfirst : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first =
      some (.timeout middleLocals middleGlobals middleMemory middleFfi, firstClock))
    (hfirstEvents : middleFfi.ioEvents = ffi.ioEvents)
    (hhigh : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + extra) (.seq first second) = some (highOutcome, highClock))
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.seq first second) =
      some (.timeout middleLocals middleGlobals middleMemory middleFfi, firstClock) ∧
      (panResultFfi
        (.timeout middleLocals middleGlobals middleMemory middleFfi, firstClock)).ioEvents <+:
        (panResultFfi (highOutcome, highClock)).ioEvents := by
  have hlow := evalPanValueFfiClockProg_seq_timeout context primitive handler structs
    functions baseAddress topAddress bytesInWord fuel clock firstClock locals globals
    memory ffi middleLocals middleGlobals middleMemory middleFfi first second
    (memoryAccess := none) (contracts := none) hfirst
  have hhighPrefix := evalPanValueFfiClockProg_ioEvents_prefix_of_handlerPreserves
    context primitive handler structs functions baseAddress topAddress bytesInWord
    hstateful hmemory (fuel + 1) locals globals memory ffi (clock + extra)
    (.seq first second) none none none highOutcome highClock (by simpa using hhigh)
  refine ⟨hlow, ?_⟩
  simpa [panResultFfi, hfirstEvents] using hhighPrefix
end Flapjack
