import Flapjack.CrepeDecCallInversion
import Flapjack.CrepeRaisedDecCallRelation

/-!
Direct raised-callee declaration-call correctness.

The compiled declaration-call inversion identifies the call fuel and result.
The supplied call relation rules out every result except an uncaught raised
result, after which the generated zero-declaration prefix is evaluated and
its local restoration is related to the source raised result.
-/

namespace Flapjack

theorem compile_full_pan_value_decCall_raised_of_compiled_inversion
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
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
    (crepResult : CrepControlResult α)
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
    (hcrep : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (compileProg context (.decCall name shape function arguments body)) =
      some crepResult)
    (hcallCorrect : ∀ (callFuel : Nat) (targetResult : CrepControlResult α),
      evalPanValueCallWithPrimitiveCallsAndFfi
        primitive sourceHandler structs sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel
        sourceLocals sourceGlobals sourceMemory none function arguments
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) =
        some (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
          sourceException sourceValue) →
      evalCrepFullCall functions crepPrimitive ffi sharedMem
        baseAddress topAddress callFuel
        { state with
            locals := initializeCrepLocals state.locals
              (allocatedNames context shape) }
        (some (allocatedNames context shape, none)) function compiledArguments =
        some targetResult →
      panValueCrepControlRel structs context exceptionRel
        (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
          sourceException sourceValue) targetResult) :
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
      targetFuel state
      (compileProg context (.decCall name shape function arguments body)) =
      some crepResult ∧
    panValueCrepControlRel structs context exceptionRel
      (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue) crepResult := by
  obtain ⟨innerFuel, callResult, htargetFuel, hcall, hrestore⟩ :=
    evalCrepFullProg_decCall_inversion
      context functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state name shape function arguments body
      compiledArguments crepResult hcompileArgs hcrep
  have hcallRel :
      panValueCrepControlRel structs context exceptionRel
        (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
          sourceException sourceValue) callResult := by
    exact hcallCorrect innerFuel callResult hsourceCall hcall
  cases callResult with
  | normal callState =>
      simp [panValueCrepControlRel] at hcallRel
  | returned callState values =>
      simp [panValueCrepControlRel] at hcallRel
  | raised callState crepException =>
      have hrel := hcallRel
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
      have hcompileProg :
          compileProg context (.decCall name shape function arguments body) =
            nestedDecs (allocatedNames context shape)
              ((allocatedNames context shape).map
                (fun _ => CrepExp.const (0 : α)))
              (.seq
                (.call (some (allocatedNames context shape, none)) function
                  compiledArguments)
                (compileProg
                  { context with
                      vars := (name, (shape, allocatedNames context shape)) ::
                        context.vars
                      maxVar := context.maxVar + Shape.shapeSize shape }
                  body)) := by
        simp [compileProg, hcompileArgs]
      have hcallProg :
          evalCrepFullProg functions crepPrimitive ffi sharedMem
            baseAddress topAddress (innerFuel + 1)
            { state with
                locals := initializeCrepLocals state.locals
                  (allocatedNames context shape) }
            (.call (some (allocatedNames context shape, none)) function
              compiledArguments) = some (.raised callState crepException) := by
        simpa only [evalCrepFullProg] using hcall
      have hseq :
          evalCrepFullProg functions crepPrimitive ffi sharedMem
            baseAddress topAddress (innerFuel + 2)
            { state with
                locals := initializeCrepLocals state.locals
                  (allocatedNames context shape) }
            (.seq
              (.call (some (allocatedNames context shape, none)) function
                compiledArguments)
              (compileProg
                { context with
                    vars := (name, (shape, allocatedNames context shape)) ::
                      context.vars
                    maxVar := context.maxVar + Shape.shapeSize shape }
                body)) = some (.raised callState crepException) := by
        simp [evalCrepFullProg, hcallProg]
      have hnested := evalCrepFullProg_nestedDecs_const_zero
        functions crepPrimitive ffi sharedMem baseAddress topAddress (innerFuel + 2)
        state (allocatedNames context shape)
        (.seq
          (.call (some (allocatedNames context shape, none)) function
            compiledArguments)
          (compileProg
            { context with
                vars := (name, (shape, allocatedNames context shape)) :: context.vars
                maxVar := context.maxVar + Shape.shapeSize shape }
            body))
        (.raised callState crepException) hseq
      rw [hrestore] at hnested
      have htarget :
          evalCrepFullProg functions crepPrimitive ffi sharedMem
            baseAddress topAddress
            ((innerFuel + 2) + (allocatedNames context shape).length) state
            (compileProg context (.decCall name shape function arguments body)) =
            some crepResult := by
        rw [hcompileProg]
        exact hnested
      have houterRel :
          panValueCrepControlRel structs context exceptionRel
            (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
              sourceException sourceValue)
            (restoreCrepResultList state.locals
              (allocatedNames context shape) (.raised callState crepException)) := by
        rw [restoreCrepResultList_raised]
        exact panValueCrepControlRel_restore_local_raised
          structs context exceptionRel
          (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
          sourceException sourceValue callState crepException
          (restoreCrepLocalList state.locals
            (allocatedNames context shape) callState.locals) hrel
      have hrestore' :
          restoreCrepResultList state.locals
            (allocatedNames context shape) (.raised callState crepException) =
            crepResult := by
        simpa using hrestore
      refine ⟨hsourceResult, ?_, ?_⟩
      · simpa [htargetFuel] using htarget
      · rw [hrestore'] at houterRel
        exact houterRel
  | broke callState label =>
      simp [panValueCrepControlRel] at hcallRel
  | continued callState label =>
      simp [panValueCrepControlRel] at hcallRel
  | finalFfi callState event =>
      simp [panValueCrepControlRel] at hcallRel

end Flapjack
