import Flapjack.PanValueFfiClockCorrectness
import Flapjack.PanObservationalSemantics

namespace Flapjack

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

end Flapjack
