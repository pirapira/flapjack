import Flapjack.CrepeDecCallIndependentFuelRelation
import Flapjack.CrepeRaisedResultRestoration

/-!
Independent-fuel exception propagation for declaration calls.  A raised
callee result skips the declaration body; the generated temporary declarations
only restore locals around that raised result.
-/

namespace Flapjack

theorem compile_full_pan_value_decCall_raised_independent_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (crepException : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory none function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue))
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context shape) }
      (some (allocatedNames context shape, none)) function compiledArguments =
      some (.raised state crepException))
    (hrel : panValueCrepControlRel structs context exceptionRel
      (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue)
      (.raised state crepException)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.decCall name shape function arguments body)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (targetFuel + (allocatedNames context shape).length + 2) state
      (compileProg context (.decCall name shape function arguments body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context shape) (.raised state crepException)) ∧
    panValueCrepControlRel structs context exceptionRel
      (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue)
      (restoreCrepResultList state.locals
        (allocatedNames context shape) (.raised state crepException)) := by
  have hsourceResult :
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive sourceHandler structs sourceFunctions
        baseAddress topAddress bytesInWord (sourceFuel + 1)
        sourceLocals sourceGlobals sourceMemory
        (.decCall name shape function arguments body)
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) =
        some (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
          sourceException sourceValue) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCall]
  have hseq :
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress (targetFuel + 2)
        { state with
            locals := initializeCrepLocals state.locals
              (allocatedNames context shape) }
        (.seq
          (.call (some (allocatedNames context shape, none)) function
            compiledArguments)
          (compileProg
            { context with
                vars := (name, (shape, allocatedNames context shape)) :: context.vars
                maxVar := context.maxVar + Shape.shapeSize shape }
            body)) =
        some (.raised state crepException) := by
    have hcallProg :
        evalCrepFullProg functions crepPrimitive ffi sharedMem
          baseAddress topAddress (targetFuel + 1)
          { state with
              locals := initializeCrepLocals state.locals
                (allocatedNames context shape) }
          (.call (some (allocatedNames context shape, none)) function
            compiledArguments) =
          some (.raised state crepException) := by
      simpa only [evalCrepFullProg] using hcrepCall
    simp [evalCrepFullProg, hcallProg]
  have hnested := evalCrepFullProg_nestedDecs_const_zero
    functions crepPrimitive ffi sharedMem baseAddress topAddress
    (targetFuel + 2) state (allocatedNames context shape)
    (.seq
      (.call (some (allocatedNames context shape, none)) function
        compiledArguments)
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body))
    (.raised state crepException) hseq
  have houterRel := panValueCrepControlRel_restore_raised_list
    structs context exceptionRel
    (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
    sourceException sourceValue state crepException
    (allocatedNames context shape) hrel
  simpa [compileProg, allocatedNames, nestedDecs,
    hcompileArgs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    And.intro hsourceResult (And.intro hnested houterRel)

end Flapjack
