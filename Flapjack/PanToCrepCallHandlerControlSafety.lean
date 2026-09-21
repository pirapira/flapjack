import Flapjack.PanToCrepCorrectnessBoundary

/-!
Control-safety for the source-to-Crep `call` constructor when the call
metadata carries an exception handler.  The callee's own `broke`/`continued`
results are discarded by both evaluators, but a matching handler body is
evaluated directly and can propagate its own loop control.  Hence this slice
takes explicit handler safety evidence: a handler program that never returns
`broke`/`continued` from any state.  The no-handler companion lives in
`Flapjack.PanToCrepCallControlSafety`.
-/

namespace Flapjack

/-- A source program that never exposes a loop-control result: from any state
    it either fails or returns a `normal`/`returned`/`raised` result. -/
def PanValueProgNotBrokeContinued
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (program : Prog α) : Prop :=
  ∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (result : PanValueControlResult α),
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory program =
      some result →
    (∀ l g m, result ≠ .broke l g m) ∧
      (∀ l g m, result ≠ .continued l g m)

theorem evalPanValueCallWithPrimitiveCallsAndFfi_handler_not_broke_continued
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (result : PanValueControlResult α)
    (hhandlerNotBroke : ∀ (handlerProgram : Prog α),
      (∃ (destination : Option (VarKind × VarName)) (caught : ExceptionId)
        (handlerVariable : VarName),
        info = some (destination, some (caught, handlerVariable, handlerProgram))) →
      PanValueProgNotBrokeContinued primitive handler structs functions
        baseAddress topAddress bytesInWord handlerProgram)
    (h : evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs
      functions baseAddress topAddress bytesInWord fuel locals globals memory
      info function arguments = some result) :
    (∀ l g m, result ≠ .broke l g m) ∧
      (∀ l g m, result ≠ .continued l g m) := by
  cases fuel with
  | zero => simp [evalPanValueCallWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hvalues : evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments with
      | none =>
          simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues] at h
      | some values =>
          cases hlookup : lookupPanFunction function functions with
          | none =>
              simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                hlookup] at h
          | some entry =>
              obtain ⟨parameters, body⟩ := entry
              cases hbind : bindPanValueParameters parameters values with
              | none =>
                  simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                    hlookup, hbind] at h
              | some calleeLocals =>
                  cases hbody : evalPanValueProgWithPrimitiveCallsAndFfi
                      primitive handler structs functions baseAddress
                      topAddress bytesInWord fuel calleeLocals globals memory
                      body with
                  | none =>
                      simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                        hlookup, hbind, hbody] at h
                  | some bodyResult =>
                      simp only [evalPanValueCallWithPrimitiveCallsAndFfi] at h
                      cases bodyResult with
                      | normal bodyLocals bodyGlobals bodyMemory =>
                          simp_all
                      | returned bodyLocals bodyGlobals bodyMemory bodyValues =>
                          cases hwithin : panValueValuesWithinLimit structs bodyValues with
                          | false => simp_all
                          | true =>
                              cases info with
                              | none =>
                                  simp_all
                                  rw [← h]
                                  exact ⟨(fun l g m => by simp),
                                    (fun l g m => by simp)⟩
                              | some destination =>
                                  obtain ⟨destinationValue, _handlerOption⟩ :=
                                    destination
                                  cases hassign : assignPanValueCallResult
                                      locals bodyGlobals destinationValue
                                      bodyValues (structs := structs) with
                                  | none => simp_all
                                  | some assigned =>
                                      obtain ⟨assignedLocals, assignedGlobals⟩ :=
                                        assigned
                                      simp_all
                                      rw [← h]
                                      exact ⟨(fun l g m => by simp),
                                        (fun l g m => by simp)⟩
                      | raised bodyLocals bodyGlobals bodyMemory exception value =>
                          cases hexcValid :
                              panValueExceptionValid structs none exception value with
                          | false => simp_all
                          | true =>
                              cases hpayload :
                                  panValuePayloadWithinLimit structs value with
                              | false => simp_all
                              | true =>
                                  cases info with
                                  | none =>
                                      simp_all
                                      rw [← h]
                                      exact ⟨(fun l g m => by simp),
                                        (fun l g m => by simp)⟩
                                  | some destination =>
                                      obtain ⟨destinationValue, handlerOption⟩ :=
                                        destination
                                      cases handlerOption with
                                      | none =>
                                          simp_all
                                          rw [← h]
                                          exact ⟨(fun l g m => by simp),
                                            (fun l g m => by simp)⟩
                                      | some caughtHandler =>
                                          obtain ⟨caught, handlerVariable,
                                            handlerProgram⟩ := caughtHandler
                                          by_cases hcaught :
                                              caught = exception
                                          · by_cases hvalid :
                                                panValueHandlerValid structs none
                                                  locals handlerVariable value = true
                                            · have hhandlerEval :
                                                  evalPanValueProgWithPrimitiveCallsAndFfi
                                                    primitive handler structs
                                                    functions baseAddress topAddress
                                                    bytesInWord fuel
                                                    (updatePanValueMap locals
                                                      handlerVariable value)
                                                    bodyGlobals bodyMemory
                                                    handlerProgram = some result := by
                                                simpa [evalPanValueCallWithPrimitiveCallsAndFfi,
                                                  hvalues, hlookup, hbind, hbody,
                                                  hexcValid, hpayload, hcaught,
                                                  hvalid] using h
                                              exact hhandlerNotBroke handlerProgram
                                                ⟨destinationValue, caught,
                                                  handlerVariable, rfl⟩
                                                fuel
                                                (updatePanValueMap locals
                                                  handlerVariable value)
                                                bodyGlobals bodyMemory result
                                                hhandlerEval
                                            · simp_all
                                          · have hres : result =
                                                PanValueControlResult.raised
                                                  (fun _ => none) bodyGlobals
                                                  bodyMemory exception value := by
                                              simpa [evalPanValueCallWithPrimitiveCallsAndFfi,
                                                hvalues, hlookup, hbind, hbody,
                                                hexcValid, hpayload, hcaught] using
                                                h.symm
                                            rw [hres]
                                            exact ⟨(fun l g m => by simp),
                                              (fun l g m => by simp)⟩
                      | broke bodyLocals bodyGlobals bodyMemory =>
                          simp_all
                      | continued bodyLocals bodyGlobals bodyMemory =>
                          simp_all

theorem panValueCrepProgramStateControlSafe_call_handler
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (name : FunName) (args : List (Exp α))
    (hhandlerNotBroke : ∀ (primitive : PanPrimitiveHandler α)
      (sourceHandler : PanValueFfiHandler α) (structs : StructContext)
      (sourceFunctions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) (handlerProgram : Prog α),
      (∃ (destination : Option (VarKind × VarName)) (caught : ExceptionId)
        (handlerVariable : VarName),
        info = some (destination, some (caught, handlerVariable, handlerProgram))) →
      PanValueProgNotBrokeContinued primitive sourceHandler structs
        sourceFunctions baseAddress topAddress bytesInWord handlerProgram) :
    PanValueCrepProgramStateControlSafe (.call info name args) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      have hcall :
          evalPanValueCallWithPrimitiveCallsAndFfi primitive sourceHandler structs
            sourceFunctions baseAddress topAddress bytesInWord sourceFuel
            sourceLocals sourceGlobals sourceMemory info name args =
            some sourceResult := by
        simpa [evalPanValueProgWithPrimitiveCallsAndFfi] using hsource
      obtain ⟨hnotBroke, hnotContinued⟩ :=
        evalPanValueCallWithPrimitiveCallsAndFfi_handler_not_broke_continued
          primitive sourceHandler structs sourceFunctions baseAddress topAddress
          bytesInWord sourceFuel sourceLocals sourceGlobals sourceMemory info name
          args sourceResult
          (fun handlerProgram hinfo =>
            hhandlerNotBroke primitive sourceHandler structs sourceFunctions
              baseAddress topAddress bytesInWord handlerProgram hinfo)
          hcall
      cases sourceResult with
      | normal resultLocals resultGlobals resultMemory =>
          simp [panValuePcControlLabelSafe]
      | returned resultLocals resultGlobals resultMemory values =>
          simp [panValuePcControlLabelSafe]
      | raised resultLocals resultGlobals resultMemory exception value =>
          simp [panValuePcControlLabelSafe]
      | broke resultLocals resultGlobals resultMemory =>
          exact absurd rfl (hnotBroke resultLocals resultGlobals resultMemory)
      | continued resultLocals resultGlobals resultMemory =>
          exact absurd rfl (hnotContinued resultLocals resultGlobals resultMemory)

/-! Compositional rules for the source-level handler/body safety predicate.
    These make the explicit handler-safety evidence of the handler-carrying call
    theorem dischargeable for concrete handler programs built from leaves,
    sequences, and conditionals. -/

theorem PanValueProgNotBrokeContinued_skip
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.skip : Prog α) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      simp only [evalPanValueProgWithPrimitiveCallsAndFfi, Option.some.injEq] at h
      subst h
      exact ⟨(fun l g m => by simp), (fun l g m => by simp)⟩

theorem PanValueProgNotBrokeContinued_seq
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (first second : Prog α)
    (hfirst : PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord first)
    (hsecond : PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord second) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.seq first second) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hfirstEval : evalPanValueProgWithPrimitiveCallsAndFfi primitive
          handler structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory first with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hfirstEval] at h
      | some firstResult =>
          have hf := hfirst fuel locals globals memory firstResult hfirstEval
          cases firstResult with
          | normal fl fg fm =>
              simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hfirstEval,
                Option.bind_eq_bind, Option.bind_some] at h
              exact hsecond fuel fl fg fm result h
          | returned fl fg fm fv =>
              simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hfirstEval,
                Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
              subst h
              exact hf
          | raised fl fg fm ex v =>
              simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hfirstEval,
                Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
              subst h
              exact hf
          | broke fl fg fm =>
              exact absurd rfl (hf.1 fl fg fm)
          | continued fl fg fm =>
              exact absurd rfl (hf.2 fl fg fm)

theorem PanValueProgNotBrokeContinued_ite
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (condition : Exp α) (thenBranch elseBranch : Prog α)
    (hthen : PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord thenBranch)
    (helse : PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord elseBranch) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.ite condition thenBranch elseBranch) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hcond : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord condition with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond] at h
      | some conditionValue =>
          cases conditionValue with
          | word w =>
              by_cases hw : w != 0
              · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond, hw] at h
                exact hthen fuel locals globals memory result h
              · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond, hw] at h
                exact helse fuel locals globals memory result h
          | rStruct fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond] at h
          | nStruct name fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond] at h

theorem restorePanValueControlLocal_not_broke
    (name : VarName) (oldValue : Option (PanValue α))
    (result : PanValueControlResult α)
    (h : ∀ l g m, result ≠ .broke l g m) :
    ∀ l g m, restorePanValueControlLocal name oldValue result ≠ .broke l g m := by
  intro l g m hb
  cases result <;> simp_all [restorePanValueControlLocal]

theorem restorePanValueControlLocal_not_continued
    (name : VarName) (oldValue : Option (PanValue α))
    (result : PanValueControlResult α)
    (h : ∀ l g m, result ≠ .continued l g m) :
    ∀ l g m, restorePanValueControlLocal name oldValue result ≠ .continued l g m := by
  intro l g m hb
  cases result <;> simp_all [restorePanValueControlLocal]

theorem panValuePcControlLabelSafe_of_not_broke_continued
    (sourceResult : PanValueControlResult α) (crepResult : CrepControlResult α)
    (h : (∀ l g m, sourceResult ≠ .broke l g m) ∧
      (∀ l g m, sourceResult ≠ .continued l g m)) :
    panValuePcControlLabelSafe sourceResult crepResult := by
  obtain ⟨hb, hc⟩ := h
  cases sourceResult with
  | normal l g m => simp [panValuePcControlLabelSafe]
  | returned l g m v => simp [panValuePcControlLabelSafe]
  | raised l g m e v => simp [panValuePcControlLabelSafe]
  | broke l g m => exact absurd rfl (hb l g m)
  | continued l g m => exact absurd rfl (hc l g m)

theorem panValueCrepProgramStateControlSafe_decCall
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (hbody : ∀ (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α),
      PanValueProgNotBrokeContinued primitive handler structs functions
        baseAddress topAddress bytesInWord body) :
    PanValueCrepProgramStateControlSafe
      (.decCall name shape function arguments body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive sourceHandler
          structs sourceFunctions baseAddress topAddress bytesInWord sourceFuel
          sourceLocals sourceGlobals sourceMemory none function arguments with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at hsource
      | some callResult =>
          cases callResult with
          | returned callLocals callGlobals callMemory values =>
              cases values with
              | nil =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at hsource
              | cons value rest =>
                  cases rest with
                  | nil =>
                      by_cases hshape : panShapeMatches (panValueShape structs value)
                          shape = true
                      · cases hbodyEval : evalPanValueProgWithPrimitiveCallsAndFfi
                            primitive sourceHandler structs sourceFunctions
                            baseAddress topAddress bytesInWord sourceFuel
                            (updatePanValueMap sourceLocals name value) callGlobals
                            callMemory body with
                        | none =>
                            simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall,
                              hshape, hbodyEval] at hsource
                        | some bodyResult =>
                            have hsafe := hbody primitive sourceHandler structs
                              sourceFunctions baseAddress topAddress bytesInWord
                              sourceFuel (updatePanValueMap sourceLocals name value)
                              callGlobals callMemory bodyResult hbodyEval
                            simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hcall,
                              hshape, if_true, hbodyEval, Option.bind_eq_bind,
                              Option.bind_some, Option.pure_def, Option.some.injEq] at hsource
                            subst hsource
                            exact panValuePcControlLabelSafe_of_not_broke_continued _ _
                              ⟨restorePanValueControlLocal_not_broke name
                                  (sourceLocals name) bodyResult hsafe.1,
                                restorePanValueControlLocal_not_continued name
                                  (sourceLocals name) bodyResult hsafe.2⟩
                      · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall,
                          hshape] at hsource
                  | cons v vs =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at hsource
          | raised callLocals callGlobals callMemory exception value =>
              have hres : sourceResult =
                  PanValueControlResult.raised (fun _ => none) callGlobals
                    callMemory exception value := by
                simpa [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] using hsource.symm
              rw [hres]
              simp [panValuePcControlLabelSafe]
          | normal callLocals callGlobals callMemory =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at hsource
          | broke callLocals callGlobals callMemory =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at hsource
          | continued callLocals callGlobals callMemory =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at hsource

/-! Common handler leaves.  These source programs terminate with `returned` or
    `raised`, so they cannot expose loop-control results to a surrounding call
    handler. -/

theorem PanValueProgNotBrokeContinued_return
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (expression : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.return expression) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hvalue : evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at h
      | some value =>
          cases hvalid : panValuePayloadWithinLimit structs value with
          | false =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid] at h
          | true =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid] at h
              cases h
              exact ⟨(fun l g m => by simp), (fun l g m => by simp)⟩

theorem PanValueProgNotBrokeContinued_raise
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (exception : ExceptionId) (expression : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.raise exception expression) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hvalue : evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at h
      | some value =>
          cases hexception : panValueExceptionValid structs none exception value with
          | false =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at h
              rcases h with ⟨_, hresult⟩
              cases hresult
              exact ⟨(fun l g m => by simp), (fun l g m => by simp)⟩
          | true =>
              cases hvalid : panValuePayloadWithinLimit structs value with
              | false =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue,
                    hvalid] at h
              | true =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue,
                    hvalid] at h
                  cases h
                  exact ⟨(fun l g m => by simp), (fun l g m => by simp)⟩

end Flapjack
