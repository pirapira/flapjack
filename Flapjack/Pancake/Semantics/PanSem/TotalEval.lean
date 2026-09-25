import Flapjack.Pancake.Semantics.PanSem.TotalSteps
import Flapjack.Pancake.Semantics.PanSem.TotalMeasure
import Flapjack.Pancake.Semantics.PanSem.LookupCode

/-!
# Measured total PanSem evaluator assembly

This module assembles the existing HOL-shaped result/state constructor steps
into a recursive evaluator over production `Prog` and the complete,
finite-support `PanSemState`. Recursive source calls resolve through the
state-owned code map. The recursion measure is the source clock followed by
`panSemProgFuel`; it is not an externally supplied fuel argument.

The evaluator is currently an untagged Flapjack evaluator. In particular, the
String-keyed names and the pending exact expression-evaluator bridge mean this
definition is not claimed as the polymorphic HOL `evaluate_def` port yet.
-/

namespace Flapjack

variable {σ : Type v}

/-- Convert the state-owned `lookup_code` result into the argument order used by
    the total Call/DecCall clause assemblers. -/
def panSemTotalCodeLookup [BEq String]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function : FunName) (arguments : List (PanValue (RiscV.Word 64))) :
    Option (Prog (RiscV.Word 64) ×
      (VarName → Option (PanValue (RiscV.Word 64))) × Shape) :=
  match lookupPanSemCodeCall state.structs state.code function arguments with
  | none => none
  | some (body, returnShape, locals) => some (body, locals, returnShape)

/-- Total result×state evaluator over the complete RISC-V `Prog` syntax.
    `If` and `Seq` recurse on source subprograms; `While`, `Call`, and `DecCall`
    recurse at the HOL-decremented clock; `Dec` restores the previous local
    after evaluating its body. Call lookup reads `state.code` at each dispatch.

    This definition intentionally has no `@[hol]` tag: names still use
    `String`, and exact `eval_def` agreement depends on the separate
    state-derived HOL expression evaluator bridge. -/
def panSemEvaluateTotalRiscV64 [NeZero 64]
    [BEq (RiscV.Word 64)] [DecidableEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)] [BEq String] [LawfulBEq String]
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    Prog (RiscV.Word 64) →
      PanSemState (RiscV.Word 64) (FfiState σ) →
        Option (PanSemHOLResult (RiscV.Word 64)) ×
          PanSemState (RiscV.Word 64) (FfiState σ)
  | .skip, state => panSemEvaluateClockLeaf .skip state
  | .break, state => panSemEvaluateClockLeaf .break state
  | .continue, state => panSemEvaluateClockLeaf .continue state
  | .tick, state => panSemEvaluateClockLeaf .tick state
  | .assign kind name value, state =>
      panSemTotalAssignClause state kind name value
  | .primitive name operator arguments, state =>
      panSemTotalPrimitiveClause state name operator arguments primitive
  | .store address value, state => panSemTotalStoreClause state address value
  | .store32 address value, state => panSemTotalStore32Clause state address value
  | .storeByte address value, state => panSemTotalStoreByteClause state address value
  | .raise exception value, state => panSemTotalRaiseClause state exception value
  | .return value, state => panSemTotalReturnClause state value
  | .annot _tag _text, state => (none, state)
  | .dec name shape value body, state =>
      match evalPanSemStateExp state value with
      | none => (some .error, state)
      | some evaluated =>
          if panShapeMatches shape (panSemShapeOf evaluated) then
            let bodyState := panSemTotalDecBind state name evaluated
            let bodyResult := panSemEvaluateTotalRiscV64 primitive body bodyState
            (bodyResult.1, { bodyResult.2 with
              locals := resVar bodyResult.2.locals (name, state.locals name) })
          else (some .error, state)
  | .seq first second, state =>
      let firstResult := panSemEvaluateTotalRiscV64 primitive first state
      let fixedState := panSemFixClock state.clock firstResult.2
      match firstResult.1 with
      | none => panSemEvaluateTotalRiscV64 primitive second fixedState
      | some result => (some result, fixedState)
  | .ite condition thenBranch elseBranch, state =>
      match evalPanSemStateExp state condition with
      | some (.word value) =>
          if value = 0 then panSemEvaluateTotalRiscV64 primitive elseBranch state
          else panSemEvaluateTotalRiscV64 primitive thenBranch state
      | _ => (some .error, state)
  | .while condition body, state =>
      match evalPanSemStateExp state condition with
      | some (.word value) =>
          if value = 0 then (none, state)
          else if state.clock = 0 then (some .timeOut, panEmptyLocals state)
          else
            let decState := { state with clock := decPanClock state.clock }
            let bodyResult := panSemEvaluateTotalRiscV64 primitive body decState
            let fixedState := panSemFixClock decState.clock bodyResult.2
            match bodyResult.1 with
            | none => panSemEvaluateTotalRiscV64 primitive (.while condition body) fixedState
            | some .continue =>
                panSemEvaluateTotalRiscV64 primitive (.while condition body) fixedState
            | some .break => (none, fixedState)
            | other => (other, fixedState)
      | _ => (some .error, state)
  | .call info function arguments, state =>
      match evalPanSemStateExps state arguments with
      | none => (some .error, state)
      | some values =>
          match panSemTotalCodeLookup state function values with
          | none => (some .error, state)
          | some (callee, newLocals, returnShape) =>
              if state.clock = 0 then (some .timeOut, panEmptyLocals state)
              else
                let entry := { state with
                  clock := decPanClock state.clock
                  locals := newLocals }
                let bodyResult := panSemEvaluateTotalRiscV64 primitive callee entry
                let fixedState := panSemFixClock entry.clock bodyResult.2
                match bodyResult.1 with
                | none | some .break | some .continue => (some .error, fixedState)
                | some (.returned value) =>
                    if panShapeMatches (panSemShapeOf value) returnShape then
                      match info with
                      | none => (some (.returned value), panEmptyLocals fixedState)
                      | some (none, _) =>
                          (none, { fixedState with locals := state.locals })
                      | some (some (kind, name), _) =>
                          if panValueAssignmentValid state.structs state.locals
                              state.globals kind name value then
                            (none, match kind with
                              | .local => { fixedState with
                                  locals := updatePanValueMap state.locals name value }
                              | .global => { fixedState with
                                  locals := state.locals
                                  globals := updatePanValueMap fixedState.globals name value })
                          else (some .error, fixedState)
                    else (some .error, fixedState)
                | some (.exception exceptionId value) =>
                    match info with
                    | none => (some (.exception exceptionId value), panEmptyLocals fixedState)
                    | some (_, none) =>
                        (some (.exception exceptionId value), panEmptyLocals fixedState)
                    | some (_, some (handlerId, handlerVar, handlerProg)) =>
                        if exceptionId == handlerId then
                          match state.exceptionShapes exceptionId with
                          | some shape =>
                              if panShapeMatches (panSemShapeOf value) shape &&
                                  panValueAssignmentValid state.structs state.locals state.globals
                                    .local handlerVar value then
                                panSemEvaluateTotalRiscV64 primitive handlerProg
                                  { fixedState with locals :=
                                    updatePanValueMap state.locals handlerVar value }
                              else (some .error, fixedState)
                          | none => (some .error, fixedState)
                        else
                          (some (.exception exceptionId value), panEmptyLocals fixedState)
                | some other => (some other, panEmptyLocals fixedState)
  | .decCall name shape function arguments continuation, state =>
      match evalPanSemStateExps state arguments with
      | none => (some .error, state)
      | some values =>
          match panSemTotalCodeLookup state function values with
          | none => (some .error, state)
          | some (callee, newLocals, returnShape) =>
              if state.clock = 0 then (some .timeOut, panEmptyLocals state)
              else
                let entry := { state with
                  clock := decPanClock state.clock
                  locals := newLocals }
                let bodyResult := panSemEvaluateTotalRiscV64 primitive callee entry
                let fixedState := panSemFixClock entry.clock bodyResult.2
                match bodyResult.1 with
                | none | some .break | some .continue => (some .error, fixedState)
                | some (.returned value) =>
                    if panShapeMatches shape (panSemShapeOf value) &&
                        panShapeMatches shape returnShape then
                      let bound := { fixedState with
                        locals := updatePanValueMap state.locals name value }
                      let continuationResult :=
                        panSemEvaluateTotalRiscV64 primitive continuation bound
                      (continuationResult.1,
                        { continuationResult.2 with
                          locals := resVar continuationResult.2.locals
                            (name, state.locals name) })
                    else (some .error, fixedState)
                | some other => (some other, panEmptyLocals fixedState)
  | .extCall function configuration configurationLength array arrayLength, state =>
      panSemTotalExtCallClause state function configuration configurationLength array arrayLength
  | .shMemLoad size kind name address, state =>
      panSemTotalShMemLoadClause state size kind name address
  | .shMemStore size address value, state =>
      panSemTotalShMemStoreClause state size address value
termination_by program state => panSemEvalMeasure state program
decreasing_by
  all_goals
    simp_wf
    simp [panSemEvalMeasure, panSemProgFuel, panSemFixClock, decPanClock,
      panSemTotalDecBind]
    omega

end Flapjack
