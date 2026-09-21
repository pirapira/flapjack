import Flapjack.PanToCrepCorrectnessBoundary

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

end Flapjack
