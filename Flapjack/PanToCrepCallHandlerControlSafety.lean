import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.PanToCrepCallControlSafety

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

/-! Concrete declaration-call handler leaves reuse the generic DecCall safety
    rule while retaining the exact source evaluator body. -/
theorem panValueCrepProgramStateControlSafe_decCall_return
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (expression : Exp α) :
    PanValueCrepProgramStateControlSafe
      (.decCall name shape function arguments (.return expression)) := by
  exact panValueCrepProgramStateControlSafe_decCall name shape function arguments
    (.return expression) (fun primitive handler structs functions baseAddress
      topAddress bytesInWord =>
      PanValueProgNotBrokeContinued_return primitive handler structs functions
        baseAddress topAddress bytesInWord expression)

theorem panValueCrepProgramStateControlSafe_decCall_raise
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (exception : ExceptionId)
    (expression : Exp α) :
    PanValueCrepProgramStateControlSafe
      (.decCall name shape function arguments (.raise exception expression)) := by
  exact panValueCrepProgramStateControlSafe_decCall name shape function arguments
    (.raise exception expression) (fun primitive handler structs functions
      baseAddress topAddress bytesInWord =>
      PanValueProgNotBrokeContinued_raise primitive handler structs functions
        baseAddress topAddress bytesInWord exception expression)

theorem PanValueProgNotBrokeContinued_call_of_no_handler
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (hnoHandler : ∀ destination caughtHandler,
      info = some (destination, some caughtHandler) → False) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.call info function arguments) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      have hcall :
          evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs
            functions baseAddress topAddress bytesInWord fuel locals globals
            memory info function arguments = some result := by
        simpa [evalPanValueProgWithPrimitiveCallsAndFfi] using h
      exact evalPanValueCallWithPrimitiveCallsAndFfi_no_handler_not_broke_continued
        primitive handler structs functions baseAddress topAddress bytesInWord
        fuel locals globals memory info function arguments result hnoHandler hcall

/-- A handler-carrying call is `PanValueProgNotBrokeContinued` whenever the
    handler program is: the callee's own loop control is dropped by the call,
    and the only route to `broke`/`continued` is the handler body. This is the
    program-level counterpart of `panValueCrepProgramStateControlSafe_call_handler`. -/
theorem PanValueProgNotBrokeContinued_call_handler
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (hhandlerNotBroke : ∀ (handlerProgram : Prog α),
      (∃ (destination : Option (VarKind × VarName)) (caught : ExceptionId)
        (handlerVariable : VarName),
        info = some (destination, some (caught, handlerVariable, handlerProgram))) →
      PanValueProgNotBrokeContinued primitive handler structs functions
        baseAddress topAddress bytesInWord handlerProgram) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.call info function arguments) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      have hcall :
          evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs
            functions baseAddress topAddress bytesInWord fuel locals globals
            memory info function arguments = some result := by
        simpa [evalPanValueProgWithPrimitiveCallsAndFfi] using h
      exact evalPanValueCallWithPrimitiveCallsAndFfi_handler_not_broke_continued
        primitive handler structs functions baseAddress topAddress bytesInWord
        fuel locals globals memory info function arguments result hhandlerNotBroke hcall

theorem PanValueProgNotBrokeContinued_dec
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (hbody : PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord body) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.dec name shape value body) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hvalue : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord value with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at h
      | some valueResult =>
          cases hmatch : panShapeMatches (panValueShape structs valueResult) shape with
          | false =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hmatch] at h
          | true =>
              cases hbodyEval : evalPanValueProgWithPrimitiveCallsAndFfi primitive
                  handler structs functions baseAddress topAddress bytesInWord fuel
                  (updatePanValueMap locals name valueResult) globals memory body with
              | none =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hmatch,
                    hbodyEval] at h
              | some bodyResult =>
                  simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue,
                    hmatch, hbodyEval, Option.bind_eq_bind, Option.bind_some,
                    if_true, Option.pure_def, Option.some.injEq] at h
                  subst h
                  exact ⟨restorePanValueControlLocal_not_broke name (locals name)
                      bodyResult
                      (hbody fuel (updatePanValueMap locals name valueResult) globals
                        memory bodyResult hbodyEval).1,
                    restorePanValueControlLocal_not_continued name (locals name)
                      bodyResult
                      (hbody fuel (updatePanValueMap locals name valueResult) globals
                        memory bodyResult hbodyEval).2⟩

/-! The clock and annotation leaves cannot expose loop control: they return a
    normal result unconditionally. -/
theorem PanValueProgNotBrokeContinued_tick
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.tick : Prog α) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      simp only [evalPanValueProgWithPrimitiveCallsAndFfi, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact ⟨fun l g m => by simp, fun l g m => by simp⟩

theorem PanValueProgNotBrokeContinued_annot
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (tag text : String) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.annot tag text) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      simp only [evalPanValueProgWithPrimitiveCallsAndFfi, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact ⟨fun l g m => by simp, fun l g m => by simp⟩

/-! Local assignments cannot expose loop control: they return a normal result
    or fail. -/
theorem PanValueProgNotBrokeContinued_assign_local
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (name : VarName) (value : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.assign .local name value) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hvalue : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord value with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at h
      | some valueResult =>
          by_cases hvalid : panValueAssignmentValid structs locals globals .local
              name valueResult = true
          · simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid,
              if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq] at h
            subst h
            exact ⟨fun l g m => by simp, fun l g m => by simp⟩
          · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid] at h

/-! A single-word store writes memory and returns normally (or fails on a
    non-word address), so it never exposes a loop label. -/
theorem PanValueProgNotBrokeContinued_store
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (address value : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.store address value) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases haddress : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord address with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at h
      | some addressResult =>
          cases hvalue : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord value with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hvalue] at h
          | some storedValue =>
              cases addressResult with
              | word addressValue =>
                  cases hstore : panValueStoreWithAccess memory bytesInWord
                      addressValue storedValue none with
                  | none =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue, hstore] at h
                  | some memory' =>
                      simp only [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue, hstore, Option.bind_eq_bind, Option.bind_some,
                        Option.pure_def, Option.some.injEq] at h
                      subst h
                      exact ⟨fun l g m => by simp, fun l g m => by simp⟩
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at h
              | nStruct structName fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at h

/-! Global assignments cannot expose loop control: they return a normal result
    or fail. -/
theorem PanValueProgNotBrokeContinued_assign_global
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (name : VarName) (value : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.assign .global name value) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hvalue : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord value with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at h
      | some valueResult =>
          by_cases hvalid : panValueAssignmentValid structs locals globals .global
              name valueResult = true
          · simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid,
              if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq] at h
            subst h
            exact ⟨fun l g m => by simp, fun l g m => by simp⟩
          · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid] at h

/-! A primitive call updates a local (or fails), so it never exposes a loop
    label. -/
theorem PanValueProgNotBrokeContinued_primitive
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (name : VarName)
    (operator : PrimOp) (arguments : List (Exp α)) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.primitive name operator arguments) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hvalues : evalPanValueExps structs locals globals memory baseAddress
          topAddress bytesInWord arguments with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues] at h
      | some values =>
          cases hprim : primitive operator values with
          | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues, hprim] at h
          | some valueResult =>
              cases hold : locals name with
              | none =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues,
                    hold] at h
              | some oldValue =>
                  by_cases hmatch : panShapeMatches (panValueShape structs valueResult)
                      (panValueShape structs oldValue) = true
                  · simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues,
                      hprim, hold, Option.bind_eq_bind, Option.bind_some, hmatch,
                      if_true, Option.pure_def, Option.some.injEq] at h
                    subst h
                    exact ⟨fun l g m => by simp, fun l g m => by simp⟩
                  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues, hprim,
                      hold, hmatch] at h

/-! A 32-bit store writes memory and returns normally (or fails), so it never
    exposes a loop label. -/
theorem PanValueProgNotBrokeContinued_store32
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (address value : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.store32 address value) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases haddress : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord address with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at h
      | some addressResult =>
          cases hvalue : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord value with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hvalue] at h
          | some storedValue =>
              cases addressResult with
              | word addressValue =>
                  cases storedValue with
                  | word valueWord =>
                      simp only [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                        Option.some.injEq] at h
                      subst h
                      exact ⟨fun l g m => by simp, fun l g m => by simp⟩
                  | rStruct fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at h
                  | nStruct structName fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at h
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at h
              | nStruct structName fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at h

/-! A byte store writes memory and returns normally (or fails), so it never
    exposes a loop label. -/
theorem PanValueProgNotBrokeContinued_storeByte
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (address value : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.storeByte address value) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases haddress : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord address with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at h
      | some addressResult =>
          cases hvalue : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord value with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hvalue] at h
          | some storedValue =>
              cases addressResult with
              | word addressValue =>
                  cases storedValue with
                  | word valueWord =>
                      simp only [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                        Option.some.injEq] at h
                      subst h
                      exact ⟨fun l g m => by simp, fun l g m => by simp⟩
                  | rStruct fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at h
                  | nStruct structName fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at h
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at h
              | nStruct structName fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at h

/-! An external call resolves to a normal result (or fails), so it never exposes a
    loop label. -/
theorem PanValueProgNotBrokeContinued_extCall
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (function : FunName) (configuration configurationLength
      array arrayLength : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.extCall function configuration configurationLength array
        arrayLength) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hvalues : evalPanValueExps structs locals globals memory baseAddress
          topAddress bytesInWord
          [configuration, configurationLength, array, arrayLength] with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues] at h
      | some values =>
          cases values with
          | nil => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues] at h
          | cons v1 rest1 =>
              cases rest1 with
              | nil => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues] at h
              | cons v2 rest2 =>
                  cases rest2 with
                  | nil => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues] at h
                  | cons v3 rest3 =>
                      cases rest3 with
                      | nil => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues] at h
                      | cons v4 rest4 =>
                          cases rest4 with
                          | cons _ _ =>
                              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues] at h
                          | nil =>
                              simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hvalues,
                                Option.bind_eq_bind, Option.bind_some] at h
                              cases v1 with
                              | word c1 =>
                                  cases v2 with
                                  | word c2 =>
                                      cases v3 with
                                      | word c3 =>
                                          cases v4 with
                                          | word c4 =>
                                              cases hh : handler function c1 c2 c3 c4
                                                  locals with
                                              | none => simp [hh] at h
                                              | some l' =>
                                                  simp only [hh, Option.bind_some, Option.pure_def,
                                                    Option.some.injEq] at h
                                                  subst h
                                                  exact ⟨fun l g m => by simp,
                                                    fun l g m => by simp⟩
                                          | rStruct f => simp at h
                                          | nStruct n f => simp at h
                                      | rStruct f => simp at h
                                      | nStruct n f => simp at h
                                  | rStruct f => simp at h
                                  | nStruct n f => simp at h
                              | rStruct f => simp at h
                              | nStruct n f => simp at h

/-! A shared-memory load returns normally (or fails), so it never exposes a loop
    label. -/
theorem PanValueProgNotBrokeContinued_shMemLoad
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (size : OpSize) (kind : VarKind)
    (name : VarName) (address : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.shMemLoad size kind name address) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases haddress : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord address with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at h
      | some addressResult =>
          cases addressResult with
          | word addressValue =>
              simp only [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                Option.bind_eq_bind, Option.bind_some] at h
              cases hmem : memory addressValue with
              | none => simp [hmem] at h
              | some value =>
                  simp only [hmem, Option.bind_some] at h
                  by_cases hvalid : panValueSharedLoadValid structs locals globals kind name
                      value = true
                  · cases kind <;>
                      simp only [hvalid, if_true, Option.pure_def,
                        Option.some.injEq] at h <;>
                      subst h <;>
                      exact ⟨fun l g m => by simp, fun l g m => by simp⟩
                  · simp [hvalid] at h
          | rStruct fields => simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at h
          | nStruct structName fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at h

/-! A shared-memory store returns normally (or fails), so it never exposes a
    loop label. -/
theorem PanValueProgNotBrokeContinued_shMemStore
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (size : OpSize)
    (address value : Exp α) :
    PanValueProgNotBrokeContinued primitive handler structs functions baseAddress
      topAddress bytesInWord (.shMemStore size address value) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases haddress : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord address with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at h
      | some addressResult =>
          cases addressResult with
          | word addressValue =>
              cases hvalue : evalPanValueExp structs locals globals memory baseAddress
                  topAddress bytesInWord value with
              | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                  hvalue] at h
              | some storedValue =>
                  cases storedValue with
                  | word valueWord =>
                      simp only [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                        Option.some.injEq] at h
                      subst h
                      exact ⟨fun l g m => by simp, fun l g m => by simp⟩
                  | rStruct fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at h
                  | nStruct structName fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at h
          | rStruct fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at h
          | nStruct structName fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at h

/-! A while loop whose body never exposes a loop label is itself safe (the body
    result is either normal/continued, which recurse, or returned/raised, which
    propagate; a broke body result is converted to normal).  Proved by induction on
    the structural fuel. -/
theorem PanValueProgNotBrokeContinued_while
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (condition : Exp α) (body : Prog α)
    (hbody : PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord body) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.while condition body) := by
  intro fuel
  induction fuel with
  | zero =>
      intro locals globals memory result h
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel ih =>
      intro locals globals memory result h
      cases hcond : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord condition with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond] at h
      | some conditionResult =>
          cases conditionResult with
          | word conditionValue =>
              by_cases hz : (conditionValue == 0) = true
              · simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hcond,
                  Option.bind_eq_bind, Option.bind_some, hz, if_true, Option.pure_def,
                  Option.some.injEq] at h
                subst h
                exact ⟨fun l g m => by simp, fun l g m => by simp⟩
              · cases hbodyEval : evalPanValueProgWithPrimitiveCallsAndFfi primitive
                    handler structs functions baseAddress topAddress bytesInWord fuel
                    locals globals memory body with
                | none =>
                    simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond, hz,
                      hbodyEval] at h
                | some bodyResult =>
                    have hbsafe := hbody fuel locals globals memory bodyResult hbodyEval
                    cases bodyResult with
                    | normal bl bgl bm =>
                        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond, hz,
                          hbodyEval] at h
                        exact ih bl bgl bm result h
                    | continued bl bgl bm =>
                        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond, hz,
                          hbodyEval] at h
                        exact ih bl bgl bm result h
                    | broke bl bgl bm =>
                        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond, hz,
                          hbodyEval] at h
                        subst h
                        exact ⟨fun l g m => by simp, fun l g m => by simp⟩
                    | returned bl bgl bm bv =>
                        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond, hz,
                          hbodyEval] at h
                        subst h
                        exact hbsafe
                    | raised bl bgl bm bex bv =>
                        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond, hz,
                          hbodyEval] at h
                        subst h
                        exact hbsafe
          | rStruct fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond] at h
          | nStruct name fields =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcond] at h

/-- Source-level handler safety is strictly stronger than the Crep-side control
    safety predicate.  The source `.break` program is control-safe on the Crep
    side (both sides break at label 0), yet its source evaluation still returns
    `broke`; hence `PanValueCrepProgramStateControlSafe` alone can never yield
    `PanValueProgNotBrokeContinued`. -/
theorem not_panValueProgNotBrokeContinued_break
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) :
    ¬ PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord (.break : Prog α) := by
  intro h
  have hres := h 1 (fun _ => none) (fun _ => none) (fun _ => none)
    (.broke (fun _ => none) (fun _ => none) (fun _ => none))
    (by simp [evalPanValueProgWithPrimitiveCallsAndFfi])
  exact hres.1 _ _ _ rfl

/-! The declaration-call form cannot expose loop control when its body cannot:
    the call itself only yields `returned` (body inlined) or `raised`, and the
    `returned` branch is closed by transporting the body's safety through the
    local restoration. -/
theorem PanValueProgNotBrokeContinued_decCall
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (hbody : PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord body) :
    PanValueProgNotBrokeContinued primitive handler structs functions
      baseAddress topAddress bytesInWord
      (.decCall name shape function arguments body) := by
  intro fuel locals globals memory result h
  cases fuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel locals globals
          memory none function arguments with
      | none => simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at h
      | some callResult =>
          cases callResult with
          | normal callLocals callGlobals callMemory =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at h
          | broke callLocals callGlobals callMemory =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at h
          | continued callLocals callGlobals callMemory =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at h
          | raised callLocals callGlobals callMemory exception value =>
              have hres : result =
                  PanValueControlResult.raised (fun _ => none) callGlobals
                    callMemory exception value := by
                simpa [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] using h.symm
              rw [hres]
              exact ⟨fun l g m => by simp, fun l g m => by simp⟩
          | returned callLocals callGlobals callMemory values =>
              cases values with
              | nil =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at h
              | cons value rest =>
                  cases rest with
                  | cons v vs =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall] at h
                  | nil =>
                      by_cases hshape : panShapeMatches (panValueShape structs value)
                          shape = true
                      · cases hbodyEval : evalPanValueProgWithPrimitiveCallsAndFfi
                            primitive handler structs functions baseAddress topAddress
                            bytesInWord fuel (updatePanValueMap locals name value)
                            callGlobals callMemory body with
                        | none =>
                            simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall,
                              hshape, hbodyEval] at h
                        | some bodyResult =>
                            have hsafe := hbody fuel
                              (updatePanValueMap locals name value) callGlobals
                              callMemory bodyResult hbodyEval
                            simp only [evalPanValueProgWithPrimitiveCallsAndFfi, hcall,
                              hshape, if_true, hbodyEval, Option.bind_eq_bind,
                              Option.bind_some, Option.pure_def,
                              Option.some.injEq] at h
                            subst h
                            exact
                              ⟨restorePanValueControlLocal_not_broke name
                                  (locals name) bodyResult hsafe.1,
                                restorePanValueControlLocal_not_continued name
                                  (locals name) bodyResult hsafe.2⟩
                      · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcall,
                          hshape] at h

end Flapjack
