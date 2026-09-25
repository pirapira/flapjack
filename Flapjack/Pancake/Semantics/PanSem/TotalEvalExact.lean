import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.AssignPrimitiveExact
import Flapjack.Pancake.Semantics.PanSem.StoreExact
import Flapjack.Pancake.Semantics.PanSem.ReturnRaiseExact
import Flapjack.Pancake.Semantics.PanSem.TickShMemExact
import Flapjack.Pancake.Semantics.PanSem.ExtCallExact
import Flapjack.Pancake.Semantics.PanSem.DecCallExact
import Flapjack.Pancake.Semantics.PanSem.ClockExact

/-!
# Exact-state PanSem dispatcher fragments

The nonrecursive dispatcher assembles the reviewed clause definitions over the exact
`PanSemStateExact` / `ProgHOL` / `ExpHOL` carriers. It handles the
nonrecursive clauses whose exact helpers are available: `Skip`, `Assign`,
`Primitive`, the three stores, `ShMemLoad`, `ShMemStore`, `Break`, `Continue`,
`Return`, `Raise`, `Tick`, `ExtCall`, and `Annot`.

The outer `Option` means that a constructor has no assembled clause in the
nonrecursive dispatcher; it is distinct from the inner HOL result option. The
recursive evaluator below assembles `Dec`, `Seq`, `If`, `While`, `Call`, and
`DecCall`, plus the `Assign` and `Primitive` clauses whose memory-set fields
are proved preserved. Store clauses are assembled below with the same
preservation proof. `ExtCall`, `ShMemLoad`, and `ShMemStore` are routed through
their exact clauses after proving both memory predicates unchanged.
This file does not
claim the complete recursive HOL `evaluate_def` and has no `@[hol]` tag.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (ExpHOL ProgHOL)

/-- Dispatch exact `ProgHOL` constructors to their reviewed nonrecursive
    `evaluate_def` clauses. `none` marks a recursive or not-yet-reviewed
    constructor, rather than a HOL evaluation result. -/
def evalPanSemNonrecursiveHOLExact {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs] :
    Option (Option (PanSemResultExact width) × PanSemStateExact width σ) := by
  exact match program with
  | .skip => some (none, state)
  | .dec _ _ _ _ => none
  | .assign kind name source =>
      some (assignStepHOLExact state kind name source
        (fun _ expression => evalHOLExact state expression))
  | .primitive name operator arguments =>
      some (primitiveStepHOLExact state name operator arguments
        (fun _ expressions => evalListHOLExact state expressions))
  | .store address value =>
      some (storeStepHOLExact state address value
        (fun _ expression => evalHOLExact state expression))
  | .store32 address value =>
      some (store32StepHOLExact state address value
        (fun _ expression => evalHOLExact state expression))
  | .storeByte address value =>
      some (storeByteStepHOLExact state address value
        (fun _ expression => evalHOLExact state expression))
  | .seq _ _ => none
  | .ite _ _ _ => none
  | .while _ _ => none
  | .break => some (some .break, state)
  | .continue => some (some .continue, state)
  | .call _ _ _ => none
  | .decCall _ _ _ _ _ => none
  | .extCall function configuration configurationLength array arrayLength =>
      some (extCallStepHOLExact state
        (fun _ expression => evalHOLExact state expression)
        function configuration configurationLength array arrayLength)
  | .raise exception value =>
      some (raiseStepHOLExact state exception value
        (fun _ expression => evalHOLExact state expression))
  | .return value =>
      some (returnStepHOLExact state value
        (fun _ expression => evalHOLExact state expression))
  | .shMemLoad size kind name address =>
      some (shMemLoadClauseHOLExact state size kind name address
        (fun _ expression => evalHOLExact state expression))
  | .shMemStore size address value =>
      some (shMemStoreClauseHOLExact state size address value
        (fun _ expression => evalHOLExact state expression))
  | .tick => some (tickStepHOLExact state)
  | .annot _ _ => some (none, state)

/-! Internal recursion carries decidability for the exact state's memory sets
    alongside the state. HOL states store arbitrary sets, so these instances
    cannot be reconstructed after a state update by computation. -/
structure PanSemExactEvalContext (width : Nat) (σ : Type) [NeZero width] where
  state : PanSemStateExact width σ
  memaddrsDecidable : DecidablePred state.memaddrs
  shMemaddrsDecidable : DecidablePred state.shMemaddrs

/-- Reuse exact memory-set decisions when a HOL state update preserves both
    set fields. -/
def PanSemExactEvalContext.withState {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (state : PanSemStateExact width σ)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs) :
    PanSemExactEvalContext width σ :=
  { state := state
    memaddrsDecidable := fun address => by
      rw [hmem]
      exact context.memaddrsDecidable address
    shMemaddrsDecidable := fun address => by
      rw [hshared]
      exact context.shMemaddrsDecidable address }

/-- Exact recursive Dec/Seq/If/While/Call/DecCall and Assign evaluator over the
    state-owned HOL code map.
    Its outer `Option` marks constructors not yet assembled in this fragment;
    it is not a HOL result. Seq applies HOL `fix_clock` to its first result,
    recurs on the second program only for HOL `NONE`, and propagates terminal
    results. `If` selects and recursively evaluates one branch. `While` decrements
    the clock before its body and recurses only on normal or Continue outcomes.
    `Dec` installs its binding for the body and restores the prior local afterwards.
    `Assign` and `Primitive` use reviewed nonrecursive clauses and preserve
    both memory predicates. Store clauses are assembled below with the same
    preservation proof. `ExtCall`, `ShMemLoad`, and `ShMemStore` use their exact
    clauses and preserve both memory predicates. The whole-state carrier still
    admits unrestricted function maps, so this definition is not tagged as the
    finite-map HOL `evaluate_def`. -/
def evalPanSemRecursiveCallContextHOLExact {width : Nat} {σ : Type} [NeZero width] :
    ProgHOL width → PanSemExactEvalContext width σ →
      Option (Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
  | program, context => by
      let state := context.state
      letI : DecidablePred state.memaddrs := context.memaddrsDecidable
      letI : DecidablePred state.shMemaddrs := context.shMemaddrsDecidable
      exact match program with
      | .dec name shape initializer body =>
          match evalHOLExact state initializer with
          | none => some (some .error, context)
          | some value =>
              if shapeEqHOL shape (shapeOfHOLExact value) then
                let bodyState := setVarHOLExact name value state
                let bodyContext := context.withState bodyState rfl rfl
                match evalPanSemRecursiveCallContextHOLExact body bodyContext with
                | none => none
                | some (result, postContext) =>
                    let restored := { postContext.state with
                      locals := resVarHOLExact postContext.state.locals
                        (name, state.locals name) }
                    some (result, postContext.withState restored rfl rfl)
              else some (some .error, context)
      | .seq first second =>
          match evalPanSemRecursiveCallContextHOLExact first context with
          | none => none
          | some (firstResult, firstContext) =>
              let fixed := fixClockHOLExact state (firstResult, firstContext.state)
              let fixedContext := firstContext.withState fixed.2 rfl rfl
              match firstResult with
              | none => evalPanSemRecursiveCallContextHOLExact second fixedContext
              | some _ => some (firstResult, fixedContext)
      | .ite condition thenBranch elseBranch =>
          match evalHOLExact state condition with
          | some (.val (.word value)) =>
              if value != 0 then
                evalPanSemRecursiveCallContextHOLExact thenBranch context
              else
                evalPanSemRecursiveCallContextHOLExact elseBranch context
          | _ => some (some .error, context)
      | .while condition body =>
          match evalHOLExact state condition with
          | some (.val (.word word)) =>
              if word ≠ 0 then
                if state.clock = 0 then
                  some (some .timeOut,
                    context.withState (emptyLocalsHOLExact state) rfl rfl)
                else
                  let entry := decClockHOLExact state
                  let entryContext := context.withState entry rfl rfl
                  match evalPanSemRecursiveCallContextHOLExact body entryContext with
                  | none => none
                  | some (bodyResult, bodyContext) =>
                      let fixed := fixClockHOLExact entry (bodyResult, bodyContext.state)
                      let fixedContext := bodyContext.withState fixed.2 rfl rfl
                      match bodyResult with
                      | some .continue | none =>
                          evalPanSemRecursiveCallContextHOLExact
                            (.while condition body) fixedContext
                      | some .break => some (none, fixedContext)
                      | _ => some (bodyResult, fixedContext)
              else some (none, context)
          | _ => some (some .error, context)
      | .call info function arguments =>
          match evalListHOLExact state arguments with
          | none => some (some .error, context)
          | some values =>
              match lookupCodeHOLExact state.code function values with
              | none => some (some .error, context)
              | some (body, calleeLocals, returnShape) =>
                  if state.clock = 0 then
                    some (some .timeOut,
                      context.withState (emptyLocalsHOLExact state) rfl rfl)
                  else
                    let entry : PanSemStateExact width σ :=
                      { state with clock := state.clock - 1, locals := calleeLocals }
                    let entryContext := context.withState entry rfl rfl
                    match evalPanSemRecursiveCallContextHOLExact body entryContext with
                    | none => none
                    | some (bodyResult, bodyContext) =>
                        let fixed := fixClockHOLExact entry (bodyResult, bodyContext.state)
                        let fixedContext := bodyContext.withState fixed.2 rfl rfl
                        match bodyResult with
                        | none => some (some .error, fixedContext)
                        | some .break => some (some .error, fixedContext)
                        | some .continue => some (some .error, fixedContext)
                        | some (.returned value) =>
                            if shapeEqHOL (shapeOfHOLExact value) returnShape then
                              match info with
                              | none =>
                                  some (some (.returned value),
                                    fixedContext.withState
                                      (emptyLocalsHOLExact fixedContext.state) rfl rfl)
                              | some (none, _) =>
                                  some (none, fixedContext.withState
                                    { fixedContext.state with locals := state.locals } rfl rfl)
                              | some (some (kind, name), _) =>
                                  if isValidValueHOLExact state kind name value then
                                    some (none, fixedContext.withState
                                      (setKvarHOLExact kind name value
                                        { fixedContext.state with locals := state.locals })
                                      (by cases kind <;> rfl) (by cases kind <;> rfl))
                                  else some (some .error, fixedContext)
                            else some (some .error, fixedContext)
                        | some (.exception exceptionId value) =>
                            match info with
                            | none =>
                                some (some (.exception exceptionId value),
                                  fixedContext.withState
                                    (emptyLocalsHOLExact fixedContext.state) rfl rfl)
                            | some (_, none) =>
                                some (some (.exception exceptionId value),
                                  fixedContext.withState
                                    (emptyLocalsHOLExact fixedContext.state) rfl rfl)
                            | some (_, some (handlerId, handlerVar, handlerProgram)) =>
                                if exceptionId = handlerId then
                                  match state.eshapes exceptionId with
                                  | some shape =>
                                      if shapeEqHOL (shapeOfHOLExact value) shape &&
                                          isValidValueHOLExact state .local handlerVar value then
                                        let handlerState := setVarHOLExact handlerVar value
                                          { fixedContext.state with locals := state.locals }
                                        let handlerContext := fixedContext.withState
                                          handlerState rfl rfl
                                        evalPanSemRecursiveCallContextHOLExact handlerProgram
                                          handlerContext
                                      else some (some .error, fixedContext)
                                  | none => some (some .error, fixedContext)
                                else
                                  some (some (.exception exceptionId value),
                                    fixedContext.withState
                                      (emptyLocalsHOLExact fixedContext.state) rfl rfl)
                        | some other =>
                            some (some other, fixedContext.withState
                              (emptyLocalsHOLExact fixedContext.state) rfl rfl)
      | .decCall resultName shape function arguments continuation =>
          match evalListHOLExact state arguments with
          | none => some (some .error, context)
          | some values =>
              match lookupCodeHOLExact state.code function values with
              | none => some (some .error, context)
              | some (body, calleeLocals, returnShape) =>
                  if state.clock = 0 then
                    some (some .timeOut,
                      context.withState (emptyLocalsHOLExact state) rfl rfl)
                  else
                    let entry : PanSemStateExact width σ :=
                      { state with clock := state.clock - 1, locals := calleeLocals }
                    let entryContext := context.withState entry rfl rfl
                    match evalPanSemRecursiveCallContextHOLExact body entryContext with
                    | none => none
                    | some (bodyResult, bodyContext) =>
                        let fixed := fixClockHOLExact entry (bodyResult, bodyContext.state)
                        let fixedContext := bodyContext.withState fixed.2 rfl rfl
                        match bodyResult with
                        | none => some (some .error, fixedContext)
                        | some .break => some (some .error, fixedContext)
                        | some .continue => some (some .error, fixedContext)
                        | some (.returned value) =>
                            if shapeEqHOL (shapeOfHOLExact value) shape &&
                                shapeEqHOL (shapeOfHOLExact value) returnShape then
                              let continuationState := setVarHOLExact resultName value
                                { fixedContext.state with locals := state.locals }
                              let continuationContext := fixedContext.withState
                                continuationState rfl rfl
                              match evalPanSemRecursiveCallContextHOLExact continuation
                                  continuationContext with
                              | none => none
                              | some (continuationResult, continuationPost) =>
                                  let restored := { continuationPost.state with
                                    locals := resVarHOLExact continuationPost.state.locals
                                      (resultName, state.locals resultName) }
                                  some (continuationResult,
                                    continuationPost.withState restored rfl rfl)
                            else some (some .error, fixedContext)
                        | some other =>
                            some (some other, fixedContext.withState
                              (emptyLocalsHOLExact fixedContext.state) rfl rfl)
      | .assign kind name source =>
          let output := assignStepHOLExact state kind name source
            (fun _ expression => evalHOLExact state expression)
          have hmem : output.2.memaddrs = state.memaddrs := by
            cases hEval : evalHOLExact state source with
            | none => simp [output, assignStepHOLExact, hEval]
            | some value =>
                by_cases hvalid : isValidValueHOLExact state kind name value = true
                · cases kind <;>
                    simp [output, assignStepHOLExact, hEval, hvalid, setKvarHOLExact]
                · simp [output, assignStepHOLExact, hEval, hvalid]
          have hshared : output.2.shMemaddrs = state.shMemaddrs := by
            cases hEval : evalHOLExact state source with
            | none => simp [output, assignStepHOLExact, hEval]
            | some value =>
                by_cases hvalid : isValidValueHOLExact state kind name value = true
                · cases kind <;>
                    simp [output, assignStepHOLExact, hEval, hvalid, setKvarHOLExact]
                · simp [output, assignStepHOLExact, hEval, hvalid]
          some (output.1, context.withState output.2 hmem hshared)
      | .primitive name operator arguments =>
          let output := primitiveStepHOLExact state name operator arguments
            (fun _ expressions => evalListHOLExact state expressions)
          have hmem : output.2.memaddrs = state.memaddrs := by
            cases hEval : evalListHOLExact state arguments with
            | none => simp [output, primitiveStepHOLExact, hEval]
            | some values =>
                cases hPrim : panPrimopHOLExact (width := width) operator values with
                | none => simp [output, primitiveStepHOLExact, hEval, hPrim]
                | some value =>
                    by_cases hvalid : isValidValueHOLExact state .local name value = true
                    · simp [output, primitiveStepHOLExact, hEval, hPrim, hvalid,
                        setVarHOLExact]
                    · simp [output, primitiveStepHOLExact, hEval, hPrim, hvalid]
          have hshared : output.2.shMemaddrs = state.shMemaddrs := by
            cases hEval : evalListHOLExact state arguments with
            | none => simp [output, primitiveStepHOLExact, hEval]
            | some values =>
                cases hPrim : panPrimopHOLExact (width := width) operator values with
                | none => simp [output, primitiveStepHOLExact, hEval, hPrim]
                | some value =>
                    by_cases hvalid : isValidValueHOLExact state .local name value = true
                    · simp [output, primitiveStepHOLExact, hEval, hPrim, hvalid,
                        setVarHOLExact]
                    · simp [output, primitiveStepHOLExact, hEval, hPrim, hvalid]
          some (output.1, context.withState output.2 hmem hshared)
      | .store address value =>
          let output := storeStepHOLExact state address value
            (fun _ expression => evalHOLExact state expression)
          have hmem : output.2.memaddrs = state.memaddrs := by
            simp only [output, storeStepHOLExact]
            split
            · split
              · split <;> rfl
              · rfl
            · rfl
          have hshared : output.2.shMemaddrs = state.shMemaddrs := by
            simp only [output, storeStepHOLExact]
            split
            · split
              · split <;> rfl
              · rfl
            · rfl
          some (output.1, context.withState output.2 hmem hshared)
      | .store32 address value =>
          let output := store32StepHOLExact state address value
            (fun _ expression => evalHOLExact state expression)
          have hmem : output.2.memaddrs = state.memaddrs := by
            simp only [output, store32StepHOLExact]
            split
            · split
              · split <;> rfl
              · rfl
            · rfl
          have hshared : output.2.shMemaddrs = state.shMemaddrs := by
            simp only [output, store32StepHOLExact]
            split
            · split
              · split <;> rfl
              · rfl
            · rfl
          some (output.1, context.withState output.2 hmem hshared)
      | .storeByte address value =>
          let output := storeByteStepHOLExact state address value
            (fun _ expression => evalHOLExact state expression)
          have hmem : output.2.memaddrs = state.memaddrs := by
            simp only [output, storeByteStepHOLExact]
            split
            · split
              · split <;> rfl
              · rfl
            · rfl
          have hshared : output.2.shMemaddrs = state.shMemaddrs := by
            simp only [output, storeByteStepHOLExact]
            split
            · split
              · split <;> rfl
              · rfl
            · rfl
          some (output.1, context.withState output.2 hmem hshared)
      | other =>
          match other with
          | .skip => some (none, context)
          | .break => some (some .break, context)
          | .continue => some (some .continue, context)
          | .return value =>
              match evalHOLExact state value with
              | none => some (some .error, context)
              | some returned =>
                  if Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
                      (shapeOfHOLExact returned) ≤ 32 then
                    some (some (.returned returned),
                      context.withState (emptyLocalsHOLExact state) rfl rfl)
                  else some (some .error, context)
          | .raise exception value =>
              match evalHOLExact state value with
              | none => some (some .error, context)
              | some raised =>
                  match state.eshapes exception with
                  | none => some (some .error, context)
                  | some shape =>
                      if shapeEqHOL (shapeOfHOLExact raised) shape then
                        if Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
                            (shapeOfHOLExact raised) ≤ 32 then
                          some (some (.exception exception raised),
                            context.withState (emptyLocalsHOLExact state) rfl rfl)
                        else some (some .error, context)
                      else some (some .error, context)
          | .tick =>
              if state.clock = 0 then
                some (some .timeOut,
                  context.withState (emptyLocalsHOLExact state) rfl rfl)
              else
                some (none, context.withState (decClockHOLExact state) rfl rfl)
          | .extCall function configuration configurationLength array arrayLength =>
              let evalExpression := fun (_ : PanSemStateExact width σ)
                  (expression : ExpHOL width) => evalHOLExact state expression
              let output := extCallStepHOLExact state evalExpression function
                configuration configurationLength array arrayLength
              have hmem : output.2.memaddrs = state.memaddrs :=
                extCallStepHOLExact_memaddrs state evalExpression function
                  configuration configurationLength array arrayLength
              have hshared : output.2.shMemaddrs = state.shMemaddrs :=
                  extCallStepHOLExact_shMemaddrs state evalExpression function
                  configuration configurationLength array arrayLength
              some (output.1, context.withState output.2 hmem hshared)
          | .shMemLoad size kind name address =>
              let evalExpression := fun (_ : PanSemStateExact width σ)
                  (expression : ExpHOL width) => evalHOLExact state expression
              let output := shMemLoadClauseHOLExact state size kind name address
                evalExpression
              have hdomains :=
                shMemLoadClauseHOLExact_preservesDomains state size kind name address
                  evalExpression
              some (output.1, context.withState output.2 hdomains.1 hdomains.2)
          | .shMemStore size address value =>
              let evalExpression := fun (_ : PanSemStateExact width σ)
                  (expression : ExpHOL width) => evalHOLExact state expression
              let output := shMemStoreClauseHOLExact state size address value
                evalExpression
              have hdomains :=
                shMemStoreClauseHOLExact_preservesDomains state size address value
                  evalExpression
              some (output.1, context.withState output.2 hdomains.1 hdomains.2)
          | .annot _ _ => some (none, context)
          | .dec _ _ _ _ | .assign _ _ _ | .primitive _ _ _ | .store _ _ |
            .store32 _ _ | .storeByte _ _ | .seq _ _ | .ite _ _ _ |
            .while _ _ | .call _ _ _ | .decCall _ _ _ _ _ => none
termination_by _program context => (context.state.clock, sizeOf _program)
decreasing_by
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp only [PanSemExactEvalContext.withState]
    by_cases hlt : fixed.2.clock < state.clock
    · apply Prod.Lex.left
      exact hlt
    · have hle : fixed.2.clock ≤ state.clock :=
        fixClockHOLExact_clock_le state (firstResult, firstContext.state)
      have heq : fixed.2.clock = state.clock := by omega
      rw [heq]
      apply Prod.Lex.right
      simp_wf
      omega
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp only [PanSemExactEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide)
  · simp only [PanSemExactEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (fixClockHOLExact_clock_le entry (bodyResult, bodyContext.state))
      (Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide))
  · simp only [PanSemExactEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide)
  · simp only [PanSemExactEvalContext.withState, setVarHOLExact]
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (fixClockHOLExact_clock_le entry (bodyResult, bodyContext.state))
      (Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide))
  · simp only [PanSemExactEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide)
  · simp only [PanSemExactEvalContext.withState, setVarHOLExact]
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (fixClockHOLExact_clock_le entry (bodyResult, bodyContext.state))
      (Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide))

/-- Plain-state view of the recursive context evaluator. -/
def evalPanSemRecursiveCallHOLExact {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs] :
    Option (Option (PanSemResultExact width) × PanSemStateExact width σ) :=
  match evalPanSemRecursiveCallContextHOLExact program
      ⟨state, inferInstance, inferInstance⟩ with
  | none => none
  | some (result, context) => some (result, context.state)

end Flapjack
