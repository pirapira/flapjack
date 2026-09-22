import Flapjack.PanValueFfiClockShift
import Flapjack.PanValueFfiClockFuel
import Flapjack.PanValueFfiClockProjection
import Flapjack.PanObservationalSemantics
import Flapjack.PanValueFfiClockEventMonotonicity

namespace Flapjack

variable {α σ : Type}
variable [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α]
variable [HXor α α α] [ShiftLeft α] [ShiftRight α] [LT α]
variable [DecidableRel (fun left right : α => left < right)] [PanCmp α]

/-! Full mutually-recursive analogue of Cake's `evaluate_add_clock_eq`.

Successful non-timeout evaluations are invariant under adding fuel to the
clock, with the returned clock shifted by the same amount.  The proof follows
the mutual evaluator recursion, so it also covers calls, handlers, `decCall`,
and recursive while iterations rather than only the direct `Tick` equation.
-/
set_option linter.unusedSimpArgs false in
theorem evalPanValueFfiClock_shift
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) :
    (∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
        (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
        (function : FunName) (arguments : List (Exp α))
        (memoryAccess : Option (PanValueMemoryAccess α))
        (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
        (outcome : PanValueFfiClockOutcome α σ) (resultClock extra : Nat),
        evalPanValueFfiClockCall context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) = some (outcome, resultClock) →
        (∀ l g m f, outcome ≠ .timeout l g m f) →
        evalPanValueFfiClockCall context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock + extra) info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) = some (outcome, resultClock + extra)) ∧
    (∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
        (program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α))
        (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
        (outcome : PanValueFfiClockOutcome α σ) (resultClock extra : Nat),
        evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) = some (outcome, resultClock) →
        (∀ l g m f, outcome ≠ .timeout l g m f) →
        evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock + extra) program
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) = some (outcome, resultClock + extra)) := by
  refine evalPanValueFfiClockCall.mutual_induct
    (motive1 := fun fuel locals globals memory ffi clock info function arguments memoryAccess contracts memoryHandler =>
      ∀ outcome resultClock extra,
        evalPanValueFfiClockCall context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock) →
        (∀ l g m f, outcome ≠ .timeout l g m f) →
        evalPanValueFfiClockCall context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock + extra) info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock + extra))
    (motive2 := fun fuel locals globals memory ffi clock program memoryAccess contracts memoryHandler =>
      ∀ outcome resultClock extra,
        evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock) →
        (∀ l g m f, outcome ≠ .timeout l g m f) →
        evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock + extra) program
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock + extra))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro memoryAccess contracts memoryHandler locals globals memory ffi clock info function arguments
      outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockCall] at hrun
    exact absurd hrun (by simp)
  · intro fuel locals globals memory ffi clock info function arguments memoryAccess contracts memoryHandler
      hbodyIH hhandlerIH outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockCall] at hrun
    cases hvalues : evalPanValueExps structs locals globals memory baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) with
    | none =>
        simp only [hvalues, Option.bind_eq_bind, Option.bind_none] at hrun
        exact absurd hrun (by simp)
    | some values =>
        simp only [hvalues, Option.bind_eq_bind, Option.bind_some] at hrun
        cases hlookup : lookupPanFunction function functions with
        | none =>
            simp only [hlookup, Option.bind_eq_bind, Option.bind_none] at hrun
            exact absurd hrun (by simp)
        | some pair =>
            obtain ⟨parameters, body⟩ := pair
            simp only [hlookup, Option.bind_eq_bind, Option.bind_some] at hrun
            by_cases hparams : panValueParametersValid structs contracts function values = true
            · simp only [hparams, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
              cases hbind : bindPanValueParameters parameters values with
              | none =>
                  simp only [hbind, Option.bind_eq_bind, Option.bind_none] at hrun
                  exact absurd hrun (by simp)
              | some calleeLocals =>
                  simp only [hbind, Option.bind_eq_bind, Option.bind_some] at hrun
                  by_cases hclock : clock = 0
                  · simp only [hclock, if_true, panValueFfiClockTimeout,
                      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨heq, _⟩ := hrun
                    exfalso
                    apply hnot (fun _ => none) globals memory ffi
                    exact heq.symm
                  · simp only [hclock, if_false, Option.bind_eq_bind, Option.bind_some] at hrun
                    cases hcallee : evalPanValueFfiClockProg context primitive handler structs functions baseAddress
                        topAddress bytesInWord fuel calleeLocals globals memory ffi (decPanClock clock) body
                        (memoryAccess := memoryAccess) (contracts := contracts)
                        (memoryHandler := memoryHandler) with
                    | none =>
                        simp only [hcallee, Option.bind_eq_bind, Option.bind_none] at hrun
                        exact absurd hrun (by simp)
                    | some pair2 =>
                        obtain ⟨calleeOutcome, calleeClock⟩ := pair2
                        simp only [hcallee, Option.bind_eq_bind, Option.bind_some] at hrun
                        have hdecShift : decPanClock (clock + extra) = decPanClock clock + extra :=
                          decPanClock_add clock extra hclock
                        cases calleeOutcome with
                        | timeout l g m f =>
                            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                            obtain ⟨heq, _⟩ := hrun
                            exfalso
                            apply hnot (fun _ => none) g m f
                            exact heq.symm
                        | control calleeResult =>
                            cases calleeResult with
                            | normal l g m f
                            | broke l g m f
                            | continued l g m f =>
                                simp only [Option.bind_eq_bind, Option.bind_none] at hrun
                                exact absurd hrun (by simp)
                            | returned l g m f values =>
                                by_cases hret : (panValueReturnValid structs contracts function values &&
                                    panValueValuesWithinLimit structs values) = true
                                · simp only [hret, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                                  have hret' := Bool.and_eq_true_iff.mp hret
                                  have hbodyNot : ∀ l' g' m' f',
                                      PanValueFfiClockOutcome.control
                                        (.returned l g m f values) ≠ .timeout l' g' m' f' := by
                                    intro l' g' m' f' heq
                                    cases heq
                                  have hbodyShift := hbodyIH body calleeLocals
                                    (.control (.returned l g m f values)) calleeClock extra hcallee hbodyNot
                                  cases info with
                                  | none =>
                                      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                                      have hrun' := hrun
                                      cases hrun'
                                      simp [evalPanValueFfiClockCall, hvalues, hlookup, hparams, hbind,
                                        hret, hret', hclock, hbodyShift, hdecShift]
                                      constructor <;> assumption
                                  | some ipair =>
                                      obtain ⟨destination, sndOpt⟩ := ipair
                                      simp only [Option.bind_eq_bind, Option.bind_some] at hrun
                                      cases hassign : assignPanValueCallResult locals g destination values structs with
                                      | none =>
                                          simp only [hassign, Option.bind_eq_bind, Option.bind_none] at hrun
                                          exact absurd hrun (by simp)
                                      | some apair =>
                                          simp only [hassign, Option.bind_eq_bind, Option.bind_some] at hrun
                                          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                                          cases hrun
                                          simp [evalPanValueFfiClockCall, hvalues, hlookup, hparams, hbind,
                                            hret, hret', hclock, hbodyShift, hdecShift, hassign]
                                          constructor <;> assumption
                                · simp only [hret, if_false, Option.bind_eq_bind, Option.bind_none] at hrun
                                  exact absurd hrun (by simp)
                            | raised l g m f ex v =>
                                by_cases hexc : (panValueExceptionValid structs contracts ex v &&
                                    panValuePayloadWithinLimit structs v) = true
                                · simp only [hexc, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                                  have hexc' := Bool.and_eq_true_iff.mp hexc
                                  cases info with
                                  | none =>
                                      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                                      have hbodyNot : ∀ l' g' m' f',
                                          PanValueFfiClockOutcome.control
                                            (.raised l g m f ex v) ≠ .timeout l' g' m' f' := by
                                        intro l' g' m' f' heq
                                        cases heq
                                      have hbodyShift := hbodyIH body calleeLocals
                                        (.control (.raised l g m f ex v)) calleeClock extra hcallee hbodyNot
                                      cases hrun
                                      simp [evalPanValueFfiClockCall, hvalues, hlookup, hparams, hbind,
                                        hexc, hexc', hclock, hbodyShift, hdecShift]
                                      constructor <;> assumption
                                  | some ipair =>
                                      obtain ⟨destination, sndOpt⟩ := ipair
                                      cases sndOpt with
                                      | none =>
                                          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                                          have hbodyNot : ∀ l' g' m' f',
                                              PanValueFfiClockOutcome.control
                                                (.raised l g m f ex v) ≠ .timeout l' g' m' f' := by
                                            intro l' g' m' f' heq
                                            cases heq
                                          have hbodyShift := hbodyIH body calleeLocals
                                            (.control (.raised l g m f ex v)) calleeClock extra hcallee hbodyNot
                                          cases hrun
                                          simp [evalPanValueFfiClockCall, hvalues, hlookup, hparams, hbind,
                                            hexc, hexc', hclock, hbodyShift, hdecShift]
                                          constructor <;> assumption
                                      | some htriple =>
                                          obtain ⟨caught, handlerVariable, handlerProgram⟩ := htriple
                                          by_cases hcaught : (caught == ex) = true
                                          · simp only [hcaught, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                                            by_cases hvalid : panValueHandlerValid structs contracts locals handlerVariable v = true
                                            · simp only [hvalid, if_true] at hrun
                                              have hbodyNot : ∀ l' g' m' f',
                                                  PanValueFfiClockOutcome.control
                                                    (.raised l g m f ex v) ≠ .timeout l' g' m' f' := by
                                                intro l' g' m' f' heq
                                                cases heq
                                              have hbodyShift := hbodyIH body calleeLocals
                                                (.control (.raised l g m f ex v)) calleeClock extra hcallee hbodyNot
                                              have hhandlerShift := hhandlerIH calleeClock g m f v handlerVariable
                                                handlerProgram outcome resultClock extra hrun hnot
                                              simp_all [evalPanValueFfiClockCall, hvalues, hlookup, hparams, hbind,
                                                hexc, hexc', hcaught, hvalid, hclock, hbodyShift, hhandlerShift,
                                                hdecShift]
                                            · simp only [hvalid, if_false, Option.bind_eq_bind, Option.bind_none] at hrun
                                              exact absurd hrun (by simp)
                                          · simp only [hcaught, if_false, Option.pure_def,
                                              Option.some.injEq, Prod.mk.injEq] at hrun
                                            have hbodyNot : ∀ l' g' m' f',
                                                PanValueFfiClockOutcome.control
                                                  (.raised l g m f ex v) ≠ .timeout l' g' m' f' := by
                                              intro l' g' m' f' heq
                                              cases heq
                                            have hbodyShift := hbodyIH body calleeLocals
                                              (.control (.raised l g m f ex v)) calleeClock extra hcallee hbodyNot
                                            cases hrun
                                            simp [evalPanValueFfiClockCall, hvalues, hlookup, hparams, hbind,
                                              hexc, hexc', hcaught, hclock, hbodyShift, hdecShift]
                                            intro hEq
                                            subst caught
                                            simp at hcaught
                                · simp only [hexc, if_false, Option.bind_eq_bind, Option.bind_none] at hrun
                                  exact absurd hrun (by simp)
                            | finalFfi l g m f ev =>
                                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                                have hbodyNot : ∀ l' g' m' f',
                                    PanValueFfiClockOutcome.control (.finalFfi l g m f ev) ≠ .timeout l' g' m' f' := by
                                  intro l' g' m' f' heq
                                  cases heq
                                have hbodyShift := hbodyIH body calleeLocals
                                  (.control (.finalFfi l g m f ev)) calleeClock extra hcallee hbodyNot
                                cases hrun
                                simp [evalPanValueFfiClockCall, hvalues, hlookup, hparams, hbind,
                                  hclock, hbodyShift, hdecShift]
                                constructor <;> assumption
            · simp only [hparams, if_false, Option.bind_eq_bind, Option.bind_none] at hrun
              exact absurd hrun (by simp)
  · intro memoryAccess contracts memoryHandler locals globals memory ffi clock program
      outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg] at hrun
    exact absurd hrun (by simp)
  · intro fuel locals globals memory ffi clock name shape value body memoryAccess contracts memoryHandler
      hbodyIH outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg] at hrun
    cases hvalue : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord value
        (memoryAccess := memoryAccess) with
    | none =>
        simp only [hvalue, Option.bind_eq_bind, Option.bind_none] at hrun
        exact absurd hrun (by simp)
    | some valueResult =>
        simp only [hvalue, Option.bind_eq_bind, Option.bind_some] at hrun
        by_cases hmatch : panShapeMatches (panValueShape structs valueResult) shape = true
        · simp only [hmatch, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
          cases hbody : evalPanValueFfiClockProg context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name valueResult)
              globals memory ffi clock body
              (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
          | none =>
              simp only [hbody, Option.bind_eq_bind, Option.bind_none] at hrun
              exact absurd hrun (by simp)
          | some pair =>
              obtain ⟨bodyOutcome, bodyClock⟩ := pair
              simp only [hbody, Option.bind_eq_bind, Option.bind_some] at hrun
              have hbodyNotTimeout : ∀ l g m f, bodyOutcome ≠
                  .timeout l g m f := by
                cases bodyOutcome with
                | timeout l g m f =>
                    intro l' g' m' f' heq
                    cases heq
                    cases hrun
                    exact hnot _ _ _ _ rfl
                | control result =>
                    intro l g m f heq
                    cases heq
              have hbodyShift := hbodyIH valueResult bodyOutcome bodyClock extra hbody hbodyNotTimeout
              cases hbodyHigh : evalPanValueFfiClockProg context primitive handler structs functions
                  baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name valueResult)
                  globals memory ffi (clock + extra) body
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler) with
              | none => exact absurd hbodyShift (by simp [hbodyHigh])
              | some pairHigh =>
                  obtain ⟨bodyOutcomeHigh, bodyClockHigh⟩ := pairHigh
                  have hbodyHighEq : bodyOutcomeHigh = bodyOutcome ∧
                      bodyClockHigh = bodyClock + extra := by
                    simpa [hbodyHigh] using congrArg id hbodyShift
                  obtain ⟨houtcome, hclock⟩ := hbodyHighEq
                  subst bodyOutcomeHigh
                  subst bodyClockHigh
                  cases hrun
                  simp [evalPanValueFfiClockProg, hvalue, hmatch, hbodyHigh]
        · simp only [hmatch, if_false, Option.bind_eq_bind, Option.bind_none] at hrun
          exact absurd hrun (by simp)
  · intro fuel locals globals memory ffi clock first second memoryAccess contracts memoryHandler
      hfirstIH hsecondIH outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg] at hrun
    cases hfirst : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock first
        (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
    | none =>
        simp only [hfirst, Option.bind_eq_bind, Option.bind_none] at hrun
        exact absurd hrun (by simp)
    | some pair =>
        obtain ⟨firstOutcome, firstClock⟩ := pair
        simp only [hfirst, Option.bind_eq_bind, Option.bind_some] at hrun
        have hfirstNot : ∀ l g m f, firstOutcome ≠ .timeout l g m f := by
          cases firstOutcome with
          | timeout l g m f =>
              intro l' g' m' f' heq
              cases heq
              cases hrun
              exact hnot _ _ _ _ rfl
          | control result =>
              intro l g m f heq
              cases heq
        have hfirstShift := hfirstIH firstOutcome firstClock extra hfirst hfirstNot
        cases firstOutcome with
        | timeout l g m f =>
            have htop : outcome = .timeout l g m f := by
              have hp := (by
                simpa [Option.pure_def, Option.some.injEq, Prod.mk.injEq] using hrun.symm :
                  outcome = .timeout l g m f ∧ resultClock = firstClock)
              exact hp.1
            exact False.elim (hnot l g m f htop)
        | control firstResult =>
            cases firstResult with
            | normal nl ng nm nf =>
                cases hsecond : evalPanValueFfiClockProg context primitive handler structs functions
                    baseAddress topAddress bytesInWord fuel nl ng nm nf firstClock second
                    (memoryAccess := memoryAccess) (contracts := contracts)
                    (memoryHandler := memoryHandler) with
                | none =>
                    simp only [hsecond, Option.bind_eq_bind, Option.bind_none] at hrun
                    exact absurd hrun (by simp)
                | some pair2 =>
                    obtain ⟨secondOutcome, secondClock⟩ := pair2
                    simp only [hsecond, Option.bind_eq_bind, Option.bind_some] at hrun
                    have hpair : (secondOutcome, secondClock) = (outcome, resultClock) :=
                      Option.some.inj hrun
                    have hsecondNot : ∀ l g m f, secondOutcome ≠ .timeout l g m f := by
                      intro l g m f heq
                      exact hnot l g m f
                        ((congrArg Prod.fst hpair).symm.trans heq)
                    have hsecondShift := hsecondIH firstClock nl ng nm nf secondOutcome secondClock
                      extra hsecond hsecondNot
                    cases hpair
                    simp [evalPanValueFfiClockProg, hfirstShift, hsecondShift]
            | broke nl ng nm nf
            | continued nl ng nm nf
            | returned l g m f vs
            | raised l g m f ex v
            | finalFfi l g m f ev =>
                cases hrun
                simp [evalPanValueFfiClockProg, hfirstShift]
  · intro fuel locals globals memory ffi clock condition thenBranch elseBranch memoryAccess contracts memoryHandler
      hthenIH outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg] at hrun
    cases hcond : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord condition
        (memoryAccess := memoryAccess) with
    | none =>
        simp only [hcond, Option.bind_eq_bind, Option.bind_none] at hrun
        exact absurd hrun (by simp)
    | some condValue =>
        simp only [hcond, Option.bind_eq_bind, Option.bind_some] at hrun
        cases condValue with
        | word w =>
            simp only [evalPanValueFfiClockProg, hcond, Option.bind_eq_bind, Option.bind_some]
            by_cases hw : (w != 0) = true
            · simpa [hw] using hthenIH w outcome resultClock extra hrun hnot
            · simpa [hw] using hthenIH w outcome resultClock extra hrun hnot
        | rStruct fields =>
            simp only [Option.bind_eq_bind, Option.bind_none] at hrun
            exact absurd hrun (by simp)
        | nStruct name fields =>
            simp only [Option.bind_eq_bind, Option.bind_none] at hrun
            exact absurd hrun (by simp)
  · intro fuel locals globals memory ffi clock info function arguments memoryAccess contracts memoryHandler
      hcallIH outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg] at hrun
    simp only [evalPanValueFfiClockProg]
    exact hcallIH outcome resultClock extra hrun hnot
  · intro fuel locals globals memory ffi clock name shape function arguments body memoryAccess contracts memoryHandler
      hcallIH hbodyIH outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg] at hrun
    cases hcall : evalPanValueFfiClockCall context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock none function arguments
        (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
    | none =>
        simp only [hcall, Option.bind_eq_bind, Option.bind_none] at hrun
        exact absurd hrun (by simp)
    | some pair =>
        obtain ⟨callOutcome, nextClock⟩ := pair
        simp only [hcall, Option.bind_eq_bind, Option.bind_some] at hrun
        cases callOutcome with
        | timeout l g m f =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨heq, _⟩ := hrun
            exfalso
            apply hnot l g m f
            exact heq.symm
        | control callResult =>
            cases callResult with
            | returned l g m f vs =>
                cases vs with
                | nil =>
                    simp only [Option.bind_eq_bind, Option.bind_none] at hrun
                    exact absurd hrun (by simp)
                | cons v rest =>
                    cases rest with
                    | cons v2 rest2 =>
                        simp only [Option.bind_eq_bind, Option.bind_none] at hrun
                        exact absurd hrun (by simp)
                    | nil =>
                        by_cases hmatch : panShapeMatches (panValueShape structs v) shape = true
                        · simp only [hmatch, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                          cases hbody : evalPanValueFfiClockProg context primitive handler structs functions
                              baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name v)
                              g m f nextClock body
                              (memoryAccess := memoryAccess) (contracts := contracts)
                              (memoryHandler := memoryHandler) with
                          | none =>
                              simp only [hbody, Option.bind_eq_bind, Option.bind_none] at hrun
                              exact absurd hrun (by simp)
                          | some bodyPair =>
                              obtain ⟨bodyOutcome, bodyClock⟩ := bodyPair
                              simp only [hbody, Option.bind_eq_bind, Option.bind_some] at hrun
                              have hcallNot : ∀ l' g' m' f',
                                  PanValueFfiClockOutcome.control
                                    (.returned l g m f [v]) ≠ .timeout l' g' m' f' := by
                                intro l' g' m' f' heq
                                cases heq
                              have hcallShift := hcallIH
                                (.control (.returned l g m f [v])) nextClock extra hcall hcallNot
                              have hbodyNot : ∀ l' g' m' f', bodyOutcome ≠ .timeout l' g' m' f' := by
                                cases bodyOutcome with
                                | timeout l' g' m' f' =>
                                    intro l'' g'' m'' f'' heq
                                    cases heq
                                    cases hrun
                                    exact hnot _ _ _ _ rfl
                                | control result =>
                                    intro l' g' m' f' heq
                                    cases heq
                              have hbodyShift := hbodyIH nextClock g m f v bodyOutcome bodyClock
                                extra hbody hbodyNot
                              cases hrun
                              simp [evalPanValueFfiClockProg, evalPanValueFfiClockCall,
                                hcallShift, hbodyShift, hmatch]
                        · simp only [hmatch, if_false, Option.bind_eq_bind, Option.bind_none] at hrun
                          exact absurd hrun (by simp)
            | raised l g m f ex v =>
                have hcallNot : ∀ l' g' m' f',
                    PanValueFfiClockOutcome.control (.raised l g m f ex v) ≠ .timeout l' g' m' f' := by
                  intro l' g' m' f' heq
                  cases heq
                have hcallShift := hcallIH
                  (.control (.raised l g m f ex v)) nextClock extra hcall hcallNot
                cases hrun
                simp [evalPanValueFfiClockProg, evalPanValueFfiClockCall, hcallShift]
            | finalFfi l g m f ev =>
                have hcallNot : ∀ l' g' m' f',
                    PanValueFfiClockOutcome.control (.finalFfi l g m f ev) ≠ .timeout l' g' m' f' := by
                  intro l' g' m' f' heq
                  cases heq
                have hcallShift := hcallIH
                  (.control (.finalFfi l g m f ev)) nextClock extra hcall hcallNot
                cases hrun
                simp [evalPanValueFfiClockProg, evalPanValueFfiClockCall, hcallShift]
            | normal l g m f
            | broke l g m f
            | continued l g m f =>
                simp only [Option.bind_eq_bind, Option.bind_none] at hrun
                exact absurd hrun (by simp)
  · intro fuel locals globals memory ffi clock conditionExp body memoryAccess contracts memoryHandler
      hbodyIH hrecIH outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg] at hrun
    cases hcond : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord conditionExp
        (memoryAccess := memoryAccess) with
    | none =>
        simp only [hcond, Option.bind_eq_bind, Option.bind_none] at hrun
        exact absurd hrun (by simp)
    | some condValue =>
        simp only [hcond, Option.bind_eq_bind, Option.bind_some] at hrun
        cases condValue with
        | rStruct fields
        | nStruct name fields =>
            simp only [Option.bind_eq_bind, Option.bind_none] at hrun
            exact absurd hrun (by simp)
        | word w =>
            by_cases hz : (w == 0) = true
            · simp only [hz, if_true, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨hres, hclock'⟩ := hrun
              simp [evalPanValueFfiClockProg, hcond, hz, hres, hclock']
            · simp only [hz, if_false, Option.bind_eq_bind, Option.bind_some] at hrun
              by_cases hclock : (clock == 0) = true
              · simp only [hclock, if_true, panValueFfiClockTimeout,
                  Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                have hp : PanValueFfiClockOutcome.timeout (fun _ => none) globals memory ffi = outcome ∧
                    clock = resultClock := by
                  simpa [panValueFfiClockTimeout, Option.pure_def,
                    Option.some.injEq, Prod.mk.injEq] using hrun
                exfalso
                apply hnot (fun _ => none) globals memory ffi
                exact hp.1.symm
              · have hclockNat : clock ≠ 0 := by
                  intro hzclock
                  subst clock
                  simp at hclock
                simp only [hclock, if_false, Option.bind_eq_bind, Option.bind_some] at hrun
                cases hbody : evalPanValueFfiClockProg context primitive handler structs functions baseAddress
                    topAddress bytesInWord fuel locals globals memory ffi (decPanClock clock) body
                    (memoryAccess := memoryAccess) (contracts := contracts)
                    (memoryHandler := memoryHandler) with
                | none =>
                    simp only [hbody, Option.bind_eq_bind, Option.bind_none] at hrun
                    exact absurd hrun (by simp)
                | some bodyPair =>
                    obtain ⟨bodyOutcome, bodyClock⟩ := bodyPair
                    simp only [hbody, Option.bind_eq_bind, Option.bind_some] at hrun
                    have hdecShift : decPanClock (clock + extra) = decPanClock clock + extra :=
                      decPanClock_add clock extra hclockNat
                    cases bodyOutcome with
                    | timeout l g m f =>
                        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                        have hp : PanValueFfiClockOutcome.timeout l g m f = outcome ∧
                            bodyClock = resultClock := by
                          simpa [Option.pure_def, Option.some.injEq, Prod.mk.injEq] using hrun
                        exfalso
                        apply hnot l g m f
                        exact hp.1.symm
                    | control bodyResult =>
                        have hbodyNot : ∀ l' g' m' f',
                            PanValueFfiClockOutcome.control bodyResult ≠ .timeout l' g' m' f' := by
                          intro l' g' m' f' heq
                          cases heq
                        have hbodyShift := hbodyIH (.control bodyResult) bodyClock extra hbody hbodyNot
                        cases bodyResult with
                        | normal nl ng nm nf
                        | continued nl ng nm nf =>
                            cases hrec : evalPanValueFfiClockProg context primitive handler structs functions
                                baseAddress topAddress bytesInWord fuel nl ng nm nf bodyClock
                                (.while conditionExp body)
                                (memoryAccess := memoryAccess) (contracts := contracts)
                                (memoryHandler := memoryHandler) with
                            | none =>
                                simp only [hrec, Option.bind_eq_bind, Option.bind_none] at hrun
                                exact absurd hrun (by simp)
                            | some recPair =>
                                obtain ⟨recOutcome, recClock⟩ := recPair
                                simp only [hrec, Option.bind_eq_bind, Option.bind_some] at hrun
                                have hpair : (recOutcome, recClock) = (outcome, resultClock) := by
                                  simpa [Option.pure_def] using hrun
                                have hrecNot : ∀ l' g' m' f', recOutcome ≠ .timeout l' g' m' f' := by
                                  intro l' g' m' f' heq
                                  exact hnot l' g' m' f'
                                    ((congrArg Prod.fst hpair).symm.trans heq)
                                have hrecShift := hrecIH bodyClock nl ng nm nf recOutcome recClock
                                  extra hrec hrecNot
                                cases hpair
                                simp [evalPanValueFfiClockProg, hcond, hz, hclock, hclockNat, hdecShift,
                                  hbodyShift, hrecShift]
                        | broke nl ng nm nf =>
                            simp [Option.pure_def] at hrun
                            cases hrun
                            simp [evalPanValueFfiClockProg, hcond, hz, hclock, hclockNat, hdecShift, hbodyShift]
                            constructor <;> assumption
                        | returned l g m f vs
                        | raised l g m f ex v
                        | finalFfi l g m f ev =>
                            simp [Option.pure_def] at hrun
                            cases hrun
                            simp [evalPanValueFfiClockProg, hcond, hz, hclock, hclockNat, hdecShift, hbodyShift]
                            constructor <;> assumption
  · intro memoryAccess contracts memoryHandler _fuel locals globals memory ffi outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg] at hrun
    simp only [if_true, panValueFfiClockTimeout] at hrun
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨heq, _⟩ := hrun
    exfalso
    apply hnot (fun _ => none) globals memory ffi
    exact heq.symm
  · intro memoryAccess contracts memoryHandler _fuel locals globals memory ffi clock hclock
      outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg, if_neg hclock,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨hres, hclock'⟩ := hrun
    have hhigh : clock + extra ≠ 0 := by omega
    simp only [evalPanValueFfiClockProg, if_neg hhigh, Option.pure_def]
    rw [decPanClock_add clock extra hclock]
    simp [hres, hclock']
  · intro _fuel locals globals memory ffi clock program memoryAccess contracts memoryHandler
      hdec hseq hite hcall hdecCall hwhile htick outcome resultClock extra hrun hnot
    simp only [evalPanValueFfiClockProg, hdec, hseq, hite, hcall, hdecCall, hwhile, htick,
      evalPanValueFfiClockLeaf, Function.comp_def] at hrun
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨pair, hsource, heq⟩ := hrun
    obtain ⟨r, s⟩ := pair
    cases heq
    simp [evalPanValueFfiClockProg, hdec, hseq, hite, hcall, hdecCall, hwhile, htick,
      evalPanValueFfiClockLeaf, Function.comp_def]
    exact ⟨s, hsource⟩

/-! The successful part of `evaluate_add_clock_io_events_mono` is equality in
    this evaluator: once the full clock-shift theorem identifies the outcome,
    the extra clock is not observable through `panResultEvents`. -/
theorem evalPanValueFfiClock_shift_panResultEvents
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α))) (function : FunName)
    (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (outcome : PanValueFfiClockOutcome α σ) (resultClock extra : Nat)
    (hrun : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info
      function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (outcome, resultClock))
    (hnotimeout : ∀ l g m f, outcome ≠ .timeout l g m f) :
    panResultEvents
        (evalPanValueFfiClockCall context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info
          function arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)) =
      panResultEvents
        (evalPanValueFfiClockCall context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi
          (clock + extra) info function arguments (memoryAccess := memoryAccess)
          (contracts := contracts) (memoryHandler := memoryHandler)) := by
  have hshift := (evalPanValueFfiClock_shift context primitive handler structs
    functions baseAddress topAddress bytesInWord).1 fuel locals globals memory ffi
    clock info function arguments memoryAccess contracts memoryHandler outcome
    resultClock extra hrun hnotimeout
  rw [hrun, hshift]
  cases outcome with
  | timeout => rfl
  | control result => cases result <;> rfl

/-! The corresponding successful top-level program case is the clocked
    evaluator step used by Cake's `evaluate_add_clock_io_events_mono`. -/
theorem evalPanValueFfiClockProg_shift_panResultEvents
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (outcome : PanValueFfiClockOutcome α σ) (resultClock extra : Nat)
    (hrun : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      program (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (outcome, resultClock))
    (hnotimeout : ∀ l g m f, outcome ≠ .timeout l g m f) :
    panResultEvents
        (evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
          program (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)) =
      panResultEvents
        (evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi
          (clock + extra) program (memoryAccess := memoryAccess)
          (contracts := contracts) (memoryHandler := memoryHandler)) := by
  have hshift := (evalPanValueFfiClock_shift context primitive handler structs
    functions baseAddress topAddress bytesInWord).2 fuel locals globals memory ffi
    clock program memoryAccess contracts memoryHandler outcome resultClock extra
    hrun hnotimeout
  rw [hrun, hshift]
  cases outcome with
  | timeout => rfl
  | control result => cases result <;> rfl

/-! Cake's `evaluate_add_clock_io_events_mono` has a timeout branch in which
    the smaller-clock run contributes only its incoming FFI trace.  The
    larger-clock run may continue, so that branch is a prefix statement rather
    than the equality proved above.  For a non-timeout run, the full clock
    shift identifies the larger result and the event prefix is inherited from
    the smaller run. -/
theorem evalPanValueFfiClockProg_shift_ioEvents_prefix
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (hstateful : panValueFfiStatefulHandlerPreservesIoEvents handler)
    (hmemory : ∀ (memoryHandler : PanValueMemoryFfiHandler α σ),
      panValueFfiMemoryHandlerPreservesIoEvents memoryHandler)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (outcome : PanValueFfiClockOutcome α σ) (resultClock extra : Nat)
    (highOutcome : PanValueFfiClockOutcome α σ) (highClock : Nat)
    (hrun : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      program (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (outcome, resultClock))
    (hrunHigh : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (clock + extra) program (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (highOutcome, highClock)) :
    ffi.ioEvents <+: (panResultFfi (highOutcome, highClock)).ioEvents := by
  cases outcome with
  | timeout timeoutLocals timeoutGlobals timeoutMemory timeoutFfi =>
      exact (evalPanValueFfiClockProg_ioEvents_prefix_of_handlerPreserves
        context primitive handler structs functions baseAddress topAddress bytesInWord
        hstateful hmemory fuel locals globals memory ffi (clock + extra) program
        memoryAccess contracts memoryHandler highOutcome highClock hrunHigh)
  | control controlResult =>
      have hlow :=
        (evalPanValueFfiClockProg_ioEvents_prefix_of_handlerPreserves
          context primitive handler structs functions baseAddress topAddress bytesInWord
          hstateful hmemory fuel locals globals memory ffi clock program memoryAccess
          contracts memoryHandler (.control controlResult) resultClock hrun)
      have hshift :=
        (evalPanValueFfiClock_shift context primitive handler structs functions
          baseAddress topAddress bytesInWord).2 fuel locals globals memory ffi clock
          program memoryAccess contracts memoryHandler (.control controlResult) resultClock extra hrun
          (by
            intro timeoutLocals timeoutGlobals timeoutMemory timeoutFfi htimeout
            cases htimeout)
      have hpair : (highOutcome, highClock) =
          (.control controlResult, resultClock + extra) :=
        Option.some.inj (hrunHigh.symm.trans hshift)
      cases hpair
      cases controlResult <;> exact hlow
 
/-! The source-facing evaluator derives its Lean termination fuel from the
    input clock.  Consequently the fixed-fuel shift theorem above is not by
    itself enough to transport `panSemEvaluate`: after shifting the clock, the
    source entry point also asks for a larger fuel bound.  Fuel monotonicity
    supplies that final step.  This is the direct analogue of Cake's
    `evaluate_add_clock_eq` event observation for successful, non-timeout
    source evaluations. -/
theorem panSemEvaluate_clock_shift_panResultEvents
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α) (extra : Nat)
    (outcome : PanValueFfiClockOutcome α σ) (resultClock : Nat)
    (hrun : panSemEvaluate context primitive handler state program =
      some (outcome, resultClock))
    (hnotimeout : ∀ l g m f, outcome ≠ .timeout l g m f) :
    panResultEvents (panSemEvaluate context primitive handler state program) =
      panResultEvents
        (panSemEvaluate context primitive handler
          { state with clock := state.clock + extra } program) := by
  have hrun' : evalPanValueFfiClockProg context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord
      (panSemEvaluateFuel state program) state.locals state.globals state.memory
      state.ffi state.clock program
      (memoryAccess := state.memoryAccess) (contracts := state.contracts)
      (memoryHandler := state.memoryHandler) = some (outcome, resultClock) := by
    simpa [panSemEvaluate, panSemEvaluateWithFuel] using hrun
  have hevents := evalPanValueFfiClockProg_shift_panResultEvents
      context primitive handler state.structs state.functions state.baseAddress
      state.topAddress state.bytesInWord (panSemEvaluateFuel state program)
      state.locals state.globals state.memory state.ffi state.clock program
      state.memoryAccess state.contracts state.memoryHandler outcome resultClock extra
      hrun' hnotimeout
  have hshift : evalPanValueFfiClockProg context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord
      (panSemEvaluateFuel state program) state.locals state.globals state.memory
      state.ffi (state.clock + extra) program
      (memoryAccess := state.memoryAccess) (contracts := state.contracts)
      (memoryHandler := state.memoryHandler) = some (outcome, resultClock + extra) := by
    exact (evalPanValueFfiClock_shift context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord).2
      (panSemEvaluateFuel state program) state.locals state.globals state.memory
      state.ffi state.clock program state.memoryAccess state.contracts
      state.memoryHandler outcome resultClock extra hrun' hnotimeout
  have hfuel :
      panSemEvaluateFuel state program ≤
        panSemEvaluateFuel { state with clock := state.clock + extra } program := by
    simp [panSemEvaluateFuel, Nat.add_assoc, Nat.add_comm]
  have hshift' : evalPanValueFfiClockProg context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord
      (panSemEvaluateFuel { state with clock := state.clock + extra } program)
      state.locals state.globals state.memory state.ffi (state.clock + extra) program
      (memoryAccess := state.memoryAccess) (contracts := state.contracts)
      (memoryHandler := state.memoryHandler) = some (outcome, resultClock + extra) := by
    exact evalPanValueFfiClockProg_fuel_mono context primitive handler state.structs
      state.functions state.baseAddress state.topAddress state.bytesInWord
      (hfuel := hfuel) state.locals state.globals state.memory state.ffi
      (state.clock + extra) program state.memoryAccess state.contracts
      state.memoryHandler hshift
  have hrun'' :
      panSemEvaluate context primitive handler
          { state with clock := state.clock + extra } program =
        some (outcome, resultClock + extra) := by
    simpa [panSemEvaluate, panSemEvaluateWithFuel] using hshift'
  rw [hrun'] at hevents
  rw [hshift] at hevents
  calc
    panResultEvents (panSemEvaluate context primitive handler state program) =
        panResultEvents (some (outcome, resultClock)) :=
      congrArg panResultEvents hrun
    _ = panResultEvents (some (outcome, resultClock + extra)) := hevents
    _ = panResultEvents
        (panSemEvaluate context primitive handler
          { state with clock := state.clock + extra } program) :=
      (congrArg panResultEvents hrun'').symm
 
 

/-! The evaluator shift also transports the full source-facing result
    projection.  This is the direct clocked top-level bridge used when a
    correctness relation needs the same control/state result at a larger
    clock, with only the residual clock changed. -/
theorem evalPanValueFfiClockProg_shift_projection
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α) (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (outcome : PanValueFfiClockOutcome α σ) (resultClock extra : Nat)
    (projection : PanValueFfiClockResultProjection α σ)
    (hrun : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      program (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some (outcome, resultClock))
    (hnotimeout : ∀ l g m f, outcome ≠ .timeout l g m f)
    (hprojection :
      (evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        program (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler)).map panValueFfiClockResultProjection =
        some projection) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (clock + extra) program (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, resultClock + extra) ∧
    (evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (clock + extra) program (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler)).map
        panValueFfiClockResultProjection =
      some (panValueFfiClockResultProjection_shiftClock extra projection) := by
  have hshift := (evalPanValueFfiClock_shift context primitive handler structs
    functions baseAddress topAddress bytesInWord).2 fuel locals globals memory ffi
    clock program memoryAccess contracts memoryHandler outcome resultClock extra
    hrun hnotimeout
  constructor
  · exact hshift
  · rw [hrun] at hprojection
    rw [hshift]
    cases outcome with
    | timeout locals globals memory ffi =>
        cases hnotimeout locals globals memory ffi rfl
    | control result =>
        cases result <;>
          simp only [Option.map_some, Option.some.injEq] at hprojection
        all_goals subst projection <;> rfl

end Flapjack
