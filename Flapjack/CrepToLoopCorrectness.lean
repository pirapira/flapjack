import Flapjack.CorrectnessFfi
import Flapjack.CrepeSemantics

/-!
Crepe-to-Loop correctness for the FFI boundary.

The two evaluators use different state records even though an `extCall` has
the same observable effect in both languages.  These adapters make that
correspondence explicit and keep the proof independent of the implementation
details of `loopCompileProg`.
-/

namespace Flapjack

def loopStateOfCrepState (state : CrepState α) : LoopState α :=
  { locals := state.locals
    globals := fun _ => none
    memory := state.memory }

def crepStateOfLoopState (state : LoopState α) : CrepState α :=
  { locals := state.locals
    memory := state.memory }

def loopFfiOfCrepFfi (ffi : CrepFfiHandler α) :
    FunName → α → α → α → α → LoopState α → Option (LoopState α) :=
  fun function configuration configurationLength array arrayLength state =>
    (ffi function configuration configurationLength array arrayLength
      (crepStateOfLoopState state)).map loopStateOfCrepState

theorem crepToLoop_extCall_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state state' : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some state') :
    evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state
        (.extCall function configuration configurationLength array arrayLength) =
      some (.normal state') ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 1)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.extCall function configuration configurationLength array arrayLength)) =
      some (.normal (loopStateOfCrepState state')) := by
  constructor
  · exact evalCrepFullProg_extCall crepFunctions primitive ffi sharedMem
      baseAddress topAddress fuel state state' function configuration
      configurationLength array arrayLength configurationValue
      configurationLengthValue arrayValue arrayLengthValue hconfiguration
      hconfigurationLength harray harrayLength hffi
  · rw [evalLoopCompiledExtCall]
    simp [loopFfiOfCrepFfi, crepStateOfLoopState, loopStateOfCrepState,
      hconfiguration, hconfigurationLength, harray, harrayLength, hffi]

end Flapjack
