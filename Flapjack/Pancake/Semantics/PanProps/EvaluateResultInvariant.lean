import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite
import Flapjack.Pancake.Semantics.PanProps

/-!
Return and Raise result-payload invariant leaves for the finite-support PanSem
evaluator. These are untagged proof support for the full
`evaluate_is_wf_shape_invariant` path.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (ExpHOL ProgHOL MlS)

namespace PanSemStateFiniteExact

/-- A successful finite-support `Return` result has a well-formed payload when
    all values initially readable from locals and globals are well-formed. -/
theorem evalPanSemFiniteReturnPayloadWf {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (hlocals : ∀ name value, context.state.locals.lookup name = some value →
      isWfShapeValueHOLExact context.state.structs value = true)
    (hglobals : ∀ name value, context.state.globals.lookup name = some value →
      isWfShapeValueHOLExact context.state.structs value = true)
    (expression : ExpHOL width) (value : ValueHOL width)
    (output : FiniteEvalContext width σ)
    (heval : evalPanSemRecursiveCallFiniteContext (.return expression : ProgHOL width) context =
      some (some (.returned value), output)) :
    isWfShapeValueHOLExact context.state.structs value = true := by
  letI : DecidablePred context.state.toExact.memaddrs := by
    simpa [PanSemStateFiniteExact.toExact] using context.memaddrsDecidable
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  cases hvalue : evalHOLExact context.state.toExact expression with
  | none => simp [hvalue] at heval
  | some returned =>
      by_cases hsize :
          Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.state.structs
            (shapeOfHOLExact returned) ≤ 32
      · have hpayload : returned = value := by
          have hproject := congrArg (Option.map Prod.fst) heval
          simp [hvalue, hsize] at hproject
          exact hproject
        subst value
        exact evalHOLExact_isWfShapeValueHOLExact context.state.toExact
          (by simpa [PanSemStateFiniteExact.toExact] using hlocals)
          (by simpa [PanSemStateFiniteExact.toExact] using hglobals)
          expression returned hvalue
      · simp [hvalue, hsize] at heval

/-- A successful finite-support `Raise` result has a well-formed payload when
    all values initially readable from locals and globals are well-formed. -/
theorem evalPanSemFiniteRaisePayloadWf {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (hlocals : ∀ name value, context.state.locals.lookup name = some value →
      isWfShapeValueHOLExact context.state.structs value = true)
    (hglobals : ∀ name value, context.state.globals.lookup name = some value →
      isWfShapeValueHOLExact context.state.structs value = true)
    (exception : MlS) (expression : ExpHOL width) (value : ValueHOL width)
    (output : FiniteEvalContext width σ)
    (heval : evalPanSemRecursiveCallFiniteContext (.raise exception expression : ProgHOL width) context =
      some (some (.exception exception value), output)) :
    isWfShapeValueHOLExact context.state.structs value = true := by
  letI : DecidablePred context.state.toExact.memaddrs := by
    simpa [PanSemStateFiniteExact.toExact] using context.memaddrsDecidable
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  cases hvalue : evalHOLExact context.state.toExact expression with
  | none => simp [hvalue] at heval
  | some raised =>
      cases hshape : context.state.eshapes.lookup exception with
      | none => simp [hvalue, hshape] at heval
      | some shape =>
          by_cases heq : shapeEqHOL (shapeOfHOLExact raised) shape
          · by_cases hsize :
                Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.state.structs
                  (shapeOfHOLExact raised) ≤ 32
            · have hpayload : raised = value := by
                have hproject := congrArg (Option.map Prod.fst) heval
                simp [hvalue, hshape, heq, hsize] at hproject
                exact hproject
              subst value
              exact evalHOLExact_isWfShapeValueHOLExact context.state.toExact
                (by simpa [PanSemStateFiniteExact.toExact] using hlocals)
                (by simpa [PanSemStateFiniteExact.toExact] using hglobals)
                expression raised hvalue
            · simp [hvalue, hshape, heq, hsize] at heval
          · simp [hvalue, hshape, heq] at heval

end PanSemStateFiniteExact

end Flapjack
