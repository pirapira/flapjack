import Flapjack.CrepeDecCallInversion

/-!
Inversion for a successful source declaration call.

This exposes the two possible ways in which the source evaluator can finish a
decCall: a one-value, shape-checked callee return followed by the body, or
an uncaught exception returned directly by the callee.
-/

namespace Flapjack

theorem evalPanValueProg_decCall_inversion
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (result : PanValueControlResult α)
    (heval :
      evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1)
        sourceLocals sourceGlobals sourceMemory
        (.decCall name shape function arguments body)
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) = some result) :
    (∃ calleeLocals calleeGlobals calleeMemory value bodyResult,
       evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs functions
         baseAddress topAddress bytesInWord fuel
         sourceLocals sourceGlobals sourceMemory none function arguments
         (memoryAccess := memoryAccess) (contracts := contracts)
         (memoryHandler := memoryHandler) =
           some (.returned calleeLocals calleeGlobals calleeMemory [value]) ∧
       panShapeMatches (panValueShape structs value) shape = true ∧
       evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
         baseAddress topAddress bytesInWord fuel
         (updatePanValueMap sourceLocals name value)
         calleeGlobals calleeMemory body
         (memoryAccess := memoryAccess) (contracts := contracts)
         (memoryHandler := memoryHandler) = some bodyResult ∧
       result = restorePanValueControlLocal name (sourceLocals name) bodyResult)
    ∨
    (∃ calleeLocals calleeGlobals calleeMemory exception value,
       evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs functions
         baseAddress topAddress bytesInWord fuel
         sourceLocals sourceGlobals sourceMemory none function arguments
         (memoryAccess := memoryAccess) (contracts := contracts)
         (memoryHandler := memoryHandler) =
           some (.raised calleeLocals calleeGlobals calleeMemory exception value) ∧
       result = .raised (fun _ => none) calleeGlobals calleeMemory exception value) := by
  cases hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord fuel sourceLocals sourceGlobals sourceMemory
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) with
  | none =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at heval
  | some callResult =>
      cases callResult with
      | normal locals globals memory =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at heval
      | returned locals globals memory values =>
          cases values with
          | nil =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at heval
          | cons value values =>
              cases values with
              | nil =>
                  cases hshape : panShapeMatches (panValueShape structs value) shape with
                  | false =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall, hshape] at heval
                  | true =>
                      cases hbody : evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                          structs functions baseAddress topAddress bytesInWord fuel
                          (updatePanValueMap sourceLocals name value) globals memory body
                          (memoryAccess := memoryAccess) (contracts := contracts)
                          (memoryHandler := memoryHandler) with
                      | none =>
                          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall, hshape,
                            hbody] at heval
                      | some bodyResult =>
                          refine Or.inl ⟨locals, globals, memory, value, bodyResult, ?_, ?_,
                            ?_, ?_⟩
                          · simp
                          · simp [hshape]
                          · simp [hbody]
                          have hresult :
                              some (restorePanValueControlLocal name (sourceLocals name)
                                bodyResult) = some result := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi, hcall, hshape,
                              hbody] using heval
                          exact (Option.some.inj hresult).symm
              | cons value values =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at heval
      | raised locals globals memory exception value =>
          refine Or.inr ⟨locals, globals, memory, exception, value, ?_, ?_⟩
          · simp
          have hresult :
              some (.raised (fun _ => none) globals memory exception value) = some result := by
            simpa [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] using heval
          exact (Option.some.inj hresult).symm
      | broke locals globals memory =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at heval
      | continued locals globals memory =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at heval

end Flapjack
