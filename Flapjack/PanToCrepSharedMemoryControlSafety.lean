import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeWordSharedMemoryProgramCases

/-!
# Control safety for shared-memory leaves

The original Pancake `pc_compile_correct` proof has dedicated `ShMemLoad` and
`ShMemStore` branches (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1912`
and `:1960`).  The shared-memory leaves can only evaluate to `normal` (or
fail), never to `break`/`continue`, so the label-safety obligation is
discharged constructively from the source evaluator, mirroring the existing
`store`/`store32`/`storeByte` control-safety instances in
`Flapjack/PanToCrepCorrectnessBoundary.lean`.
-/

namespace Flapjack

theorem panValueCrepProgramStateControlSafe_shMemLoad
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α) :
    PanValueCrepProgramStateControlSafe (.shMemLoad size kind name address) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases haddress : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord address with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at hsource
      | some addressValue =>
          cases addressValue with
          | word word =>
              cases hmem : sourceMemory word with
              | none =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hmem]
                    at hsource
              | some value =>
                  cases hvalid : panValueSharedLoadValid structs sourceLocals
                      sourceGlobals kind name value with
                  | false =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hmem, hvalid] at hsource
                  | true =>
                      cases kind
                      all_goals
                        simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                          hmem, hvalid] at hsource
                        cases hsource
                        simp [panValuePcControlLabelSafe]
          | rStruct fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at hsource
          | nStruct name fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at hsource

theorem panValueCrepProgramStateControlSafe_shMemStore
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (address value : Exp α) :
    PanValueCrepProgramStateControlSafe (.shMemStore size address value) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases haddress : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord address with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at hsource
      | some addressValue =>
          cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord value with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hvalue]
                at hsource
          | some storedValue =>
              cases addressValue with
              | word word =>
                  cases storedValue with
                  | word wordValue =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at hsource
                      cases hsource
                      simp [panValuePcControlLabelSafe]
                  | rStruct fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at hsource
                  | nStruct name fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at hsource
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at hsource
              | nStruct name fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at hsource

/-! The paired constructors below are the direct source-word obligations used
by the `pc_compile_correct` ShMemLoad/ShMemStore branches.  Keeping the
correctness and control-safety halves together avoids silently instantiating
the induction boundary with only the label-safety premise. -/

theorem panValueCrepProgramStateCorrect_and_controlSafe_shMemLoad_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (name : VarName) (address : SourceWordExp α)
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
    PanValueCrepProgramStateCorrect (.shMemLoad size .local name address.toExp) ∧
      PanValueCrepProgramStateControlSafe (.shMemLoad size .local name address.toExp) := by
  exact ⟨panValueCrepProgramStateCorrect_shMemLoad_source_word size name address
      hbytesInWord hlookup hsharedRel,
    panValueCrepProgramStateControlSafe_shMemLoad size .local name address.toExp⟩

theorem panValueCrepProgramStateCorrect_and_controlSafe_shMemStore_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (address value : SourceWordExp α)
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
      (_baseAddress _topAddress _bytesInWord addressValue valueValue : α)
      (temporary : Nat),
      sharedMem (storeMemOp size) temporary addressValue
          { state with
            locals := updateCrepLocal state.locals temporary valueValue } =
        some targetState →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory addressValue (.word valueValue))
        { targetState with
          locals := restoreCrepLocal targetState.locals
            temporary (state.locals temporary) }) :
    PanValueCrepProgramStateCorrect (.shMemStore size address.toExp value.toExp) ∧
      PanValueCrepProgramStateControlSafe (.shMemStore size address.toExp value.toExp) := by
  exact ⟨panValueCrepProgramStateCorrect_shMemStore_source_word size address value
      hbytesInWord hlookup hstable hsharedRel,
    panValueCrepProgramStateControlSafe_shMemStore size address.toExp value.toExp⟩

end Flapjack
