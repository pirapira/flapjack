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

end Flapjack
