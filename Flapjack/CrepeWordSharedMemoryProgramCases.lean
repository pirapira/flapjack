import Flapjack.CrepeWordExpressionContract
import Flapjack.CrepeProgramSharedMemoryCorrectness
import Flapjack.CrepeProgramSharedMemoryLoadCorrectness

/-!
Lift shared-memory correctness constructors from `SourceWordExp` operands to
the original Pancake expression syntax.  The shared-memory transition
relations remain explicit because they describe the external memory/handler
boundary rather than a compiler-local fact.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_shMemLoad_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (name : VarName) (address : Exp α)
    (haddress : wordExp address)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (current : VarName) (value : PanValue α),
      sourceLocals current = some value →
      ∃ slot, lookupInfo current context.vars = some (.one, [slot]))
    (hsharedRel : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (state targetState : CrepState α) (_crepPrimitive : CrepPrimitiveHandler α)
      (_ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
      (_baseAddress _topAddress _bytesInWord addressValue valueValue oldValue : α)
      (slot : Nat),
      sharedMem (loadMemOp size) slot addressValue state = some targetState →
      sourceLocals name = some (.word oldValue) →
      panValueCrepStateRel structs context
        (updatePanValueMap sourceLocals name (.word valueValue)) sourceGlobals
        sourceMemory targetState) :
    PanValueCrepProgramCorrect (.shMemLoad size .local name address) := by
  have haddressToExp : (sourceWordExpOf address haddress).toExp = address :=
    sourceWordExpOf_toExp address haddress
  simpa [haddressToExp] using
    (panValueCrepProgramCorrect_shMemLoad_source_word size name
      (sourceWordExpOf address haddress) hbytesInWord hlookup hsharedRel)

theorem panValueCrepProgramCorrect_shMemStore_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (address value : Exp α)
    (haddress : wordExp address) (hvalue : wordExp value)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstable : ∀ (state : CrepState α) (baseAddress topAddress : α)
      (temporary : Nat) (compiled : CrepExp α) (value updateValue : α),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value)
    (hsharedRel : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (state targetState : CrepState α) (_crepPrimitive : CrepPrimitiveHandler α)
      (_ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
      (_baseAddress _topAddress _bytesInWord addressValue valueValue : α),
      sharedMem (storeMemOp size) (context.maxVar + 1) addressValue
        { state with
          locals := updateCrepLocal state.locals (context.maxVar + 1) valueValue } =
        some targetState →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory addressValue (.word valueValue))
        { targetState with
          locals := restoreCrepLocal targetState.locals
            (context.maxVar + 1) (state.locals (context.maxVar + 1)) }) :
    PanValueCrepProgramCorrect (.shMemStore size address value) := by
  have haddressToExp : (sourceWordExpOf address haddress).toExp = address :=
    sourceWordExpOf_toExp address haddress
  have hvalueToExp : (sourceWordExpOf value hvalue).toExp = value :=
    sourceWordExpOf_toExp value hvalue
  simpa [haddressToExp, hvalueToExp] using
    (panValueCrepProgramCorrect_shMemStore_source_word size
      (sourceWordExpOf address haddress) (sourceWordExpOf value hvalue)
      hbytesInWord hlookup hstable hsharedRel)

end Flapjack
