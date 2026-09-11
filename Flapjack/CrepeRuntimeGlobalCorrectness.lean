import Flapjack.CrepeRuntime
import Flapjack.LoopSemantics

namespace Flapjack

/-! The runtime evaluator and Loop both read globals from their global
    environment.  This boundary is intentionally separate from the compact
     adapter, whose legacy model has no global field. -/
def loopStateOfCrepRuntimeStateForGlobals (state : CrepRuntimeState α σ) : LoopState α :=
  { locals := state.locals
    globals := state.globals
    memory := state.memory }

theorem crepRuntimeToLoop_loadGlob_assign_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ) (live : List Nat)
    (name : Nat) (address value : α)
    (hglobal : state.globals address = some value) :
    (evalCrepRuntimeResult handler primitive (fuel + 1) state
      (.assign name (.loadGlob address))).map
        (fun result => result.2.locals name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepRuntimeStateForGlobals state)
      (loopCompileProg context live
        (.assign name (.loadGlob address)))).map
    (fun result => (loopResultState result).locals name) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
    loopStateOfCrepRuntimeStateForGlobals, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopResultState, updateLoopLocal, updateCrepLocal, hglobal]

theorem crepRuntimeToLoop_storeGlob_loadGlob_sequence_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ)
    (name : Nat) (address value : α) :
    (evalCrepRuntimeResult handler primitive (fuel + 2) state
      (.seq (.storeGlob address (.const value))
        (.assign name (.loadGlob address)))).map
        (fun result => result.2.globals address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 3)
      (loopStateOfCrepRuntimeStateForGlobals state)
      (loopCompileProg context []
        (.seq (.storeGlob address (.const value))
          (.assign name (.loadGlob address))))).map
        (fun result => (loopResultState result).globals address) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
    loopStateOfCrepRuntimeStateForGlobals, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopResultState, updateLoopGlobal, updateMemory]

end Flapjack
