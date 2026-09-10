import Flapjack.CrepeFfiCorrectness
import Flapjack.CrepeStateRelation

/-!
Relation-aware correctness for the normal structured FFI boundary.

The ABI marshalling and temporary-slot restoration are established by
compile_full_pan_value_extCall_simulation.  This theorem adds the
source-to-Crep state relation needed to compose that boundary in the full
program simulation.
-/

namespace Flapjack

theorem compile_full_pan_value_extCall_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceLocals' : VarName → Option (PanValue α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state state' : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (configuration' configurationLength' array' arrayLength' : CrepExp α)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (hconfiguration : firstCompiledExp context configuration = some configuration')
    (hconfigurationLength :
      firstCompiledExp context configurationLength = some configurationLength')
    (harray : firstCompiledExp context array = some array')
    (harrayLength : firstCompiledExp context arrayLength = some arrayLength')
    (hsourceValues : evalPanValueExps structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord
      [configuration, configurationLength, array, arrayLength] =
      some [.word configurationValue, .word configurationLengthValue,
        .word arrayValue, .word arrayLengthValue])
    (hconfigurationValue :
      evalCrepFullExp state.locals state.memory baseAddress topAddress
        configuration' = some configurationValue)
    (hconfigurationLengthValue :
      evalCrepFullExp
        (updateCrepLocal state.locals (context.maxVar + 1) configurationValue)
        state.memory baseAddress topAddress
        configurationLength' = some configurationLengthValue)
    (harrayValue :
      evalCrepFullExp
        (updateCrepLocal
          (updateCrepLocal state.locals (context.maxVar + 1) configurationValue)
          (context.maxVar + 2) configurationLengthValue)
        state.memory baseAddress topAddress
        array' = some arrayValue)
    (harrayLengthValue :
      evalCrepFullExp
        (updateCrepLocal
          (updateCrepLocal
            (updateCrepLocal state.locals (context.maxVar + 1) configurationValue)
            (context.maxVar + 2) configurationLengthValue)
          (context.maxVar + 3) arrayValue)
        state.memory baseAddress topAddress
        arrayLength' = some arrayLengthValue)
    (hsource : sourceHandler function configurationValue configurationLengthValue
      arrayValue arrayLengthValue sourceLocals = some sourceLocals')
    (hffi : ffi function configurationValue configurationLengthValue arrayValue
      arrayLengthValue
      ({ state with
        locals :=
          updateCrepLocal
            (updateCrepLocal
              (updateCrepLocal
                (updateCrepLocal state.locals (context.maxVar + 1)
                  configurationValue)
                (context.maxVar + 2) configurationLengthValue)
              (context.maxVar + 3) arrayValue)
            (context.maxVar + 4) arrayLengthValue }) = some state')
    (hrel : panValueCrepStateRel structs context sourceLocals' sourceGlobals
      sourceMemory (restoreCrepFfiTemps state' state context.maxVar)) :
    evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler structs []
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.extCall function configuration configurationLength array arrayLength)
      (contracts := none) (memoryHandler := none) =
      some (.normal sourceLocals' sourceGlobals sourceMemory) ∧
    evalCrepFullProg [] crepPrimitive ffi sharedMem baseAddress topAddress
      (fuel + 5) state
      (compileProg context
        (.extCall function configuration configurationLength array arrayLength)) =
      some (.normal (restoreCrepFfiTemps state' state context.maxVar)) ∧
    panValueCrepControlRel structs context
      (fun _ _ _ => False)
      (.normal sourceLocals' sourceGlobals sourceMemory)
      (.normal (restoreCrepFfiTemps state' state context.maxVar)) := by
  have hresult := compile_full_pan_value_extCall_simulation
    context structs sourceLocals sourceLocals' sourceGlobals sourceMemory
    state state' primitive crepPrimitive ffi sharedMem sourceHandler
    baseAddress topAddress bytesInWord fuel function
    configuration configurationLength array arrayLength
    configuration' configurationLength' array' arrayLength'
    configurationValue configurationLengthValue arrayValue arrayLengthValue
    hconfiguration hconfigurationLength harray harrayLength hsourceValues
    hconfigurationValue hconfigurationLengthValue harrayValue harrayLengthValue
    hsource hffi
  exact ⟨hresult.2, hresult.1, by
    simpa [panValueCrepControlRel] using hrel⟩

end Flapjack
