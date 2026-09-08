import Flapjack.CrepeCorrectness

/-!
Correctness boundary for the FFI part of `pan_to_crep`.

The compiler evaluates the four source arguments into fresh Crepe locals,
executes the external call, and restores those locals when the call returns.
This theorem makes that temporary-state protocol explicit.  The relation
between the source and target handlers is intentionally an assumption: it is
the same semantic boundary at which CakeML leaves `call_FFI` abstract.
-/

namespace Flapjack

def restoreCrepFfiTemps (state original : CrepState α) (offset : Nat) :
    CrepState α :=
  { state with
    locals :=
      restoreCrepLocal
        (restoreCrepLocal
          (restoreCrepLocal
            (restoreCrepLocal state.locals (offset + 4) (original.locals (offset + 4)))
            (offset + 3) (original.locals (offset + 3)))
          (offset + 2) (original.locals (offset + 2)))
        (offset + 1) (original.locals (offset + 1)) }

theorem compile_full_extCall_simulation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
    (context : CompileContext α)
    (sourceLocals sourceLocals' : VarName → Option α)
    (state state' : CrepState α)
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (sourceHandler : PanFfiHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (configuration' configurationLength' array' arrayLength' : CrepExp α)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (hconfiguration : firstCompiledExp context configuration = some configuration')
    (hconfigurationLength :
      firstCompiledExp context configurationLength = some configurationLength')
    (harray : firstCompiledExp context array = some array')
    (harrayLength : firstCompiledExp context arrayLength = some arrayLength')
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
    (hsource : evalPanExtCall sourceHandler sourceLocals function
      configuration configurationLength array arrayLength = some sourceLocals')
    (hffi : ffi function configurationValue configurationLengthValue arrayValue
      arrayLengthValue
      ({ state with
        locals :=
          (updateCrepLocal
            (updateCrepLocal
              (updateCrepLocal
                (updateCrepLocal state.locals (context.maxVar + 1)
                  configurationValue)
                (context.maxVar + 2) configurationLengthValue)
              (context.maxVar + 3) arrayValue)
            (context.maxVar + 4) arrayLengthValue) }) = some state') :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
        (fuel + 5) state
        (compileProg context
          (.extCall function configuration configurationLength array arrayLength)) =
      some (.normal (restoreCrepFfiTemps state' state context.maxVar)) ∧
    evalPanFfiProg sourceHandler sourceLocals
        (.extCall function configuration configurationLength array arrayLength) =
      some sourceLocals' := by
  constructor
  · rw [compileProg_extCall_of_compiled context function configuration
      configurationLength array arrayLength configuration' configurationLength'
      array' arrayLength' hconfiguration hconfigurationLength harray harrayLength]
    simp [nestedDecs, evalCrepFullProg, updateCrepLocal,
      hconfigurationValue, hconfigurationLengthValue, harrayValue,
      harrayLengthValue, hffi, restoreCrepResult, restoreCrepFfiTemps]
  · simpa [evalPanFfiProg] using hsource

end Flapjack
