import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

/-!
Flapjack-specific finite-support evaluator invariant support for the HOL
`evaluate_is_wf_shape_invariant` path. The structural-context preservation
lemmas and Return/Raise payload leaves here are components of that result, not
standalone HOL declarations, so they remain untagged.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (ExpHOL ProgHOL MlS ShapeHOL)

private theorem fupdateList_eq_lookupCodeFold {width : Nat} [NeZero width]
    (initial : FiniteMap MlS (ValueHOL width))
    (entries : List (MlS × ValueHOL width)) :
    FUPDATE_LIST initial entries =
      List.foldl
        (fun (map : MlS → Option (ValueHOL width)) (entry : MlS × ValueHOL width) =>
          fun current => if current = entry.1 then some entry.2 else map current)
        initial entries := by
  induction entries generalizing initial with
  | nil => rfl
  | cons entry entries ih =>
      simp only [FUPDATE_LIST_cons, List.foldl_cons]
      have hUpdate : FUPDATE initial entry = fun current =>
          if current = entry.1 then some entry.2 else initial current := by
        funext current
        unfold FUPDATE
        by_cases h : current = entry.1
        · subst current
          have heq : (entry.1 == entry.1) = true := beq_iff_eq.mpr rfl
          rw [if_pos rfl, if_pos heq]
        · have h' : entry.1 ≠ current := fun heq => h heq.symm
          have hbeq : (entry.1 == current) = false := by
            cases heq : (entry.1 == current) with
            | false => rfl
            | true => exact False.elim (h' (beq_iff_eq.mp heq))
          have hnot : ¬ ((entry.1 == current) = true) := by
            rw [hbeq]
            decide
          simp only [if_neg h, if_neg hnot]
      rw [hUpdate]
      exact ih _

/-- The finite PanProps lookup wrapper and recursive finite PanSem evaluator use
    the same HOL `lookup_code` checks and produce extensionally identical
    callee-local lookups. This connects the existing PanProps invariant step to
    the recursive evaluator's exact lookup result. -/
private theorem lookupCodeHOLFinite_projection_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    (fname : MlS) (arguments : List (ValueHOL width)) :
    (Flapjack.PanPropsEvalStateFiniteExact.lookupCodeHOLFinite state fname arguments).map
        (fun result : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL =>
          (result.1, result.2.1.lookup, result.2.2)) =
      Flapjack.lookupCodeHOLExact state.code.lookup fname arguments := by
  unfold Flapjack.PanPropsEvalStateFiniteExact.lookupCodeHOLFinite
    Flapjack.lookupCodeHOLExact
  cases hcode : state.code.lookup fname with
  | none => rfl
  | some codeEntry =>
      rcases codeEntry with ⟨parameters, body, returnShape⟩
      by_cases hvalid : (parameters.map Prod.fst).Nodup ∧
          parameters.length = arguments.length ∧
          ((parameters.zip arguments).all
            (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true
      · simp [hvalid, HolFiniteMapExact.updateList,
          HolFiniteMapExact.empty, fupdateList_eq_lookupCodeFold]
      · simp only [if_neg hvalid, Option.map_none]

/-- Successful recursive `lookup_code` installs only values whose shapes were
    checked against the current well-formed locals/globals. This is the
    PanSem-carrier instance of HOL `lookup_code_wf_shape_invariant_step`. -/
theorem lookupCodeHOLExact_calleeLocalsWf {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs]
    (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (fname : MlS) (body : ProgHOL width) (calleeLocals : MlS → Option (ValueHOL width))
    (returnShape : ShapeHOL)
    (hargs : state.evalListHOLFinite arguments = some values)
    (hlookup : Flapjack.lookupCodeHOLExact state.code.lookup fname values =
      some (body, calleeLocals, returnShape))
    (hlocals : ∀ name value, state.locals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true)
    (hglobals : ∀ name value, state.globals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true) :
    ∀ name value, calleeLocals name = some value →
      isWfShapeValueHOLExact state.structs value = true := by
  let propsState : PanPropsEvalStateFiniteExact width σ := {
    locals := state.locals
    globals := state.globals
    structs := state.structs
    code := state.code
    eshapes := state.eshapes
    memory := state.memory
    memaddrs := state.memaddrs
    shMemaddrs := state.shMemaddrs
    clock := state.clock
    be := state.be
    ffi := state.ffi
    baseAddr := state.baseAddr
    topAddr := state.topAddr
  }
  have hargsProps : propsState.evalListHOL arguments = some values := by
    change evalListHOLExact propsState.toExact arguments = some values
    change evalListHOLExact state.toExact arguments = some values
    exact hargs
  have hproject := lookupCodeHOLFinite_projection_eq propsState fname values
  rw [hlookup] at hproject
  cases hfiniteLookup : PanPropsEvalStateFiniteExact.lookupCodeHOLFinite
      propsState fname values with
  | none => simp [hfiniteLookup] at hproject
  | some found =>
      rcases found with ⟨foundBody, foundLocals, foundReturnShape⟩
      have htuple : (foundBody, foundLocals.lookup, foundReturnShape) =
          (body, calleeLocals, returnShape) := by
        simpa [hfiniteLookup] using hproject
      have hbodyEq : foundBody = body := congrArg Prod.fst htuple
      have hlocalsEq : foundLocals.lookup = calleeLocals :=
        congrArg (fun result => result.2.1) htuple
      have hreturnEq : foundReturnShape = returnShape :=
        congrArg (fun result => result.2.2) htuple
      have hlookupProps : PanPropsEvalStateFiniteExact.lookupCodeHOLFinite
          propsState fname values = some (body, foundLocals, returnShape) := by
        rw [hfiniteLookup]
        exact congrArg some (by
          rw [hbodyEq, hreturnEq])
      have hlocalsProps : ∀ name value, propsState.locals.lookup name = some value →
          isWfShapeValueHOLExact propsState.structs value = true := by
        simpa [propsState] using hlocals
      have hglobalsProps : ∀ name value, propsState.globals.lookup name = some value →
          isWfShapeValueHOLExact propsState.structs value = true := by
        simpa [propsState] using hglobals
      have hcallee := PanPropsEvalStateFiniteExact.lookupCodeWfShapeInvariantStep
        propsState arguments values fname body foundLocals returnShape
        ⟨hargsProps, hlookupProps, hlocalsProps, hglobalsProps⟩
      intro name value hvalue
      apply hcallee name value
      simpa [hlocalsEq] using hvalue

private def valuesHOLWf {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (lookup : MlS → Option (ValueHOL width)) : Prop :=
  ∀ name value, lookup name = some value →
    isWfShapeValueHOLExact structs value = true

private theorem valuesHOLWf_update {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (lookup : HolFiniteMapExact MlS (ValueHOL width)) (name : MlS)
    (newValue : ValueHOL width)
    (hold : valuesHOLWf structs lookup.lookup)
    (hnew : isWfShapeValueHOLExact structs newValue = true) :
    valuesHOLWf structs (lookup.update (name, newValue)).lookup := by
  intro current value hlookup
  rw [HolFiniteMapExact.lookup_update_pointwise] at hlookup
  by_cases hname : current = name
  · subst current
    have hvalue : newValue = value := by simpa using hlookup
    subst value
    exact hnew
  · have hsource : lookup.lookup current = some value := by
      simpa [hname] using hlookup
    exact hold current value hsource

private theorem valuesHOLWf_empty {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact) :
    valuesHOLWf structs (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL width)).lookup := by
  intro name value hlookup
  simp at hlookup

private theorem valuesHOLWf_resVarEq {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (map1 map2 : HolFiniteMapExact MlS (ValueHOL width)) (name : MlS)
    (h1 : valuesHOLWf structs map1.lookup) (h2 : valuesHOLWf structs map2.lookup) :
    valuesHOLWf structs (HolFiniteMapExact.resVarEq map1 (name, map2.lookup name)).lookup := by
  let predicate : MlS × ValueHOL width → Bool := fun pair =>
    isWfShapeValueHOLExact structs pair.2
  have hmaps : feveryHOL predicate map1 ∧ feveryHOL predicate map2 := by
    constructor
    · intro key value hvalue
      simpa [predicate] using h1 key value hvalue
    · intro key value hvalue
      simpa [predicate] using h2 key value hvalue
  have hresult := feveryResVarFlookupHOL predicate
    ⟨map1, map2⟩ name hmaps
  intro key value hvalue
  exact hresult key value hvalue

private theorem evalHOLFinite_isWf {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
    (hlocals : valuesHOLWf state.structs state.locals.lookup)
    (hglobals : valuesHOLWf state.structs state.globals.lookup)
    (expression : ExpHOL width) (value : ValueHOL width)
    (heval : state.evalHOLFinite expression = some value) :
    isWfShapeValueHOLExact state.structs value = true := by
  have hExact := evalHOLExact_isWfShapeValueHOLExact state.toExact
    (by simpa [valuesHOLWf, PanSemStateFiniteExact.toExact] using hlocals)
    (by simpa [valuesHOLWf, PanSemStateFiniteExact.toExact] using hglobals)
    expression value
  apply hExact
  simpa using heval

private theorem evalListHOLFinite_mem_isWf {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
    (hlocals : valuesHOLWf state.structs state.locals.lookup)
    (hglobals : valuesHOLWf state.structs state.globals.lookup) :
    ∀ expressions values, state.evalListHOLFinite expressions = some values →
      ∀ value, value ∈ values → isWfShapeValueHOLExact state.structs value = true := by
  intro expressions
  induction expressions with
  | nil =>
      intro values heval value hmem
      simp [PanSemStateFiniteExact.evalListHOLFinite, evalListHOLExact] at heval
      subst values
      simp at hmem
  | cons expression rest ih =>
      intro values heval value hmem
      letI : DecidablePred state.toExact.memaddrs := by
        simpa [PanSemStateFiniteExact.toExact] using
          (inferInstance : DecidablePred state.memaddrs)
      change evalListHOLExact state.toExact (expression :: rest) = some values at heval
      cases hhead : evalHOLExact state.toExact expression with
      | none => simp [evalListHOLExact, hhead] at heval
      | some head =>
          cases htail : evalListHOLExact state.toExact rest with
          | none => simp [evalListHOLExact, hhead, htail] at heval
          | some tail =>
              have hValues : values = head :: tail := by
                simpa [evalListHOLExact, hhead, htail] using heval.symm
              subst values
              simp only [List.mem_cons] at hmem
              rcases hmem with hheadMem | htailMem
              · subst value
                have hheadFinite : state.evalHOLFinite expression = some head := by
                  simpa using hhead
                exact evalHOLFinite_isWf state hlocals hglobals expression head hheadFinite
              · apply ih tail
                · simpa [PanSemStateFiniteExact.evalListHOLFinite] using htail
                · exact htailMem

private def panSemResultHOLWf {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact) :
    Option (PanSemResultExact width) → Prop
  | some (.returned value) => isWfShapeValueHOLExact structs value = true
  | some (.exception _ value) => isWfShapeValueHOLExact structs value = true
  | _ => True

private def panSemStateVarsHOLWf {width : Nat} {σ : Type} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (state : PanSemStateFiniteExact width σ) : Prop :=
  valuesHOLWf structs state.locals.lookup ∧ valuesHOLWf structs state.globals.lookup

private theorem panSemStateVarsHOLWf_emptyLocals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (h : panSemStateVarsHOLWf state.structs state) :
    panSemStateVarsHOLWf state.structs (PanSemStateFiniteExact.emptyLocalsHOLFinite state) := by
  exact ⟨valuesHOLWf_empty state.structs, h.2⟩

private theorem panSemStateVarsHOLWf_setVar {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width)
    (h : panSemStateVarsHOLWf state.structs state)
    (hvalue : isWfShapeValueHOLExact state.structs value = true) :
    panSemStateVarsHOLWf state.structs
      (PanSemStateFiniteExact.setVarHOLFinite name value state) := by
  exact ⟨valuesHOLWf_update state.structs state.locals name value h.1 hvalue, h.2⟩

private theorem panSemStateVarsHOLWf_setGlobal {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width)
    (h : panSemStateVarsHOLWf state.structs state)
    (hvalue : isWfShapeValueHOLExact state.structs value = true) :
    panSemStateVarsHOLWf state.structs
      (PanSemStateFiniteExact.setGlobalHOLFinite name value state) := by
  exact ⟨h.1, valuesHOLWf_update state.structs state.globals name value h.2 hvalue⟩

private theorem panSemStateVarsHOLWf_setKvar {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (kind : VarKind) (name : MlS)
    (value : ValueHOL width) (h : panSemStateVarsHOLWf state.structs state)
    (hvalue : isWfShapeValueHOLExact state.structs value = true) :
    panSemStateVarsHOLWf state.structs
      (PanSemStateFiniteExact.setKvarHOLFinite kind name value state) := by
  cases kind
  · simpa [panSemStateVarsHOLWf, PanSemStateFiniteExact.setKvarHOLFinite] using
      panSemStateVarsHOLWf_setVar state name value h hvalue
  · simpa [panSemStateVarsHOLWf, PanSemStateFiniteExact.setKvarHOLFinite] using
      panSemStateVarsHOLWf_setGlobal state name value h hvalue

private theorem panSemStateVarsHOLWf_restoreLocal {width : Nat} {σ : Type} [NeZero width]
    (after caller : PanSemStateFiniteExact width σ) (name : MlS)
    (hafter : panSemStateVarsHOLWf after.structs after)
    (hcaller : valuesHOLWf after.structs caller.locals.lookup) :
    valuesHOLWf after.structs
        (HolFiniteMapExact.resVarEq after.locals
          (name, caller.locals.lookup name)).lookup ∧
      valuesHOLWf after.structs after.globals.lookup := by
  exact ⟨valuesHOLWf_resVarEq after.structs after.locals caller.locals name
      hafter.1 hcaller, hafter.2⟩

namespace PanSemStateFiniteExact

/-- Assign clauses change only variable maps, never the structural context. -/
@[simp] theorem assignStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (assignStepHOLExact state kind name source evalExpression).2.structs = state.structs := by
  unfold assignStepHOLExact
  cases hvalue : evalExpression state source with
  | none => rfl
  | some value =>
      by_cases hvalid : isValidValueHOLExact state kind name value = true
      · cases kind <;> simp [hvalid, setKvarHOLExact]
      · simp [hvalid]

/-- Primitive clauses change only local variables, never the structural
    context. -/
@[simp] theorem primitiveStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (name : MlS)
    (operator : PrimOp) (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width))) :
    (primitiveStepHOLExact state name operator arguments evalExpressions).2.structs =
      state.structs := by
  unfold primitiveStepHOLExact
  cases hvalues : evalExpressions state arguments with
  | none => simp
  | some values =>
      cases hprimop : panPrimopHOLExact operator values with
      | none => simp [hprimop]
      | some value =>
          by_cases hvalid : isValidValueHOLExact state .local name value = true
          · simp [hprimop, hvalid, setVarHOLExact]
          · simp [hprimop, hvalid]

/-- Store clauses update memory only, never the structural context. -/
@[simp] theorem storeStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (destination source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (storeStepHOLExact state destination source evalExpression).2.structs = state.structs := by
  unfold storeStepHOLExact
  repeat' (first | split | simp)

/-- Store32 clauses update memory only, never the structural context. -/
@[simp] theorem store32StepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (store32StepHOLExact state address value evalExpression).2.structs = state.structs := by
  unfold store32StepHOLExact
  repeat' (first | split | simp)

/-- StoreByte clauses update memory only, never the structural context. -/
@[simp] theorem storeByteStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (storeByteStepHOLExact state address value evalExpression).2.structs = state.structs := by
  unfold storeByteStepHOLExact
  repeat' (first | split | simp)

/-- ExtCall clauses update memory, FFI, or locals, but not the structural
    context. -/
@[simp] theorem extCallStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width) :
    (extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2).2.structs =
      state.structs := by
  unfold extCallStepHOLExact
  all_goals (repeat' (first | split))
  all_goals simp [emptyLocalsHOLExact]

/-- Tick clauses update clock or locals, but not the structural context. -/
@[simp] theorem tickStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) :
    (tickStepHOLExact state).2.structs = state.structs := by
  unfold tickStepHOLExact
  split <;> simp [emptyLocalsHOLExact, decClockHOLExact]

/-- Shared-memory load clauses preserve the structural context. -/
@[simp] theorem shMemLoadClauseHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (shMemLoadClauseHOLExact state operator kind name address evalExpression).2.structs =
      state.structs := by
  unfold shMemLoadClauseHOLExact
  unfold shMemLoadHOLExact
  all_goals (repeat' (first | split))
  all_goals simp [emptyLocalsHOLExact, setKvarHOLExact]
  all_goals cases kind <;> rfl

/-- Shared-memory store clauses preserve the structural context. -/
@[simp] theorem shMemStoreClauseHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (shMemStoreClauseHOLExact state operator address value evalExpression).2.structs =
      state.structs := by
  unfold shMemStoreClauseHOLExact
  unfold shMemStoreHOLExact
  all_goals (repeat' (first | split))
  all_goals simp

/-- Return clauses clear locals but preserve the structural context. -/
@[simp] theorem returnStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (returnStepHOLExact state expression evalExpression).2.structs = state.structs := by
  unfold returnStepHOLExact
  cases hvalue : evalExpression state expression with
  | none => simp
  | some value =>
      by_cases hsize :
          Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
              (shapeOfHOLExact value) ≤ 32
      · simp [hsize, emptyLocalsHOLExact]
      · simp [hsize]

/-- Raise clauses clear locals but preserve the structural context. -/
@[simp] theorem raiseStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (exception : MlS)
    (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (raiseStepHOLExact state exception expression evalExpression).2.structs = state.structs := by
  unfold raiseStepHOLExact
  cases hvalue : evalExpression state expression with
  | none => simp
  | some value =>
      cases hshape : state.eshapes exception with
      | none => simp
      | some shape =>
          by_cases heq : shapeEqHOL (shapeOfHOLExact value) shape = true
          · by_cases hsize :
                Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
                    (shapeOfHOLExact value) ≤ 32
            · simp [heq, hsize, emptyLocalsHOLExact]
            · simp [heq, hsize]
          · simp [heq]

/-- Every exact nonrecursive clause leaves the structural field unchanged. -/
theorem evalPanSemNonrecursiveHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : evalPanSemNonrecursiveHOLExact program state = some (result, output)) :
    output.structs = state.structs := by
  have hmap :
      (evalPanSemNonrecursiveHOLExact program state).map
          (fun pair : Option (PanSemResultExact width) × PanSemStateExact width σ =>
            pair.2.structs) =
        (evalPanSemNonrecursiveHOLExact program state).map
          (fun _ : Option (PanSemResultExact width) × PanSemStateExact width σ =>
            state.structs) := by
    cases program <;> simp [evalPanSemNonrecursiveHOLExact]
  have hproj := congrArg
    (Option.map fun pair : Option (PanSemResultExact width) × PanSemStateExact width σ =>
      pair.2.structs) heval
  rw [hmap, heval, Option.map_some] at hproj
  exact (Option.some.inj hproj).symm

/-- Finite-support rendering preserves the structural context in every
    nonrecursive clause. -/
theorem evalPanSemNonrecursiveHOLFinite_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (program : ProgHOL width) (result : Option (PanSemResultExact width))
    (output : PanSemStateFiniteExact width σ)
    (heval : evalPanSemNonrecursiveHOLFinite state program = some (result, output)) :
    output.structs = state.structs := by
  unfold evalPanSemNonrecursiveHOLFinite at heval
  split at heval
  · simp at heval
  · rename_i exactOutput hexact
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    change exactOutput.2.structs = state.structs
    simpa [PanSemStateFiniteExact.toExact, PanSemStateFiniteExact.ofExact] using
      evalPanSemNonrecursiveHOLExact_structs_eq program state.toExact
        exactOutput.1 exactOutput.2 hexact

/-- The clause-shaped finite-support evaluator preserves the source structural
    context on every successful evaluation. -/
theorem evalPanSemRecursiveCallFiniteContext_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (context : FiniteEvalContext width σ) :
    ∀ result output,
      evalPanSemRecursiveCallFiniteContext program context = some (result, output) →
        output.state.structs = context.state.structs := by
  fun_induction evalPanSemRecursiveCallFiniteContext program context
  case case28 =>
    intro result output heval
    try rcases heval with ⟨rfl, rfl⟩
    cases (show VarKind from by assumption) <;>
      try simp_all (config := { zetaDelta := true })
        [FiniteEvalContext.withState, fixClockHOLFinite,
          setVarHOLFinite, setKvarHOLFinite,
          setGlobalHOLFinite, PanSemStateFiniteExact.toExact]
  case case66 =>
    let ctx : FiniteEvalContext width σ := by assumption
    intro result output heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred ctx.state.memaddrs := ctx.memaddrsDecidable
    letI : DecidablePred ctx.state.shMemaddrs := ctx.shMemaddrsDecidable
    simp only [FiniteEvalContext.withState]
    apply evalPanSemNonrecursiveHOLFinite_structs_eq
    assumption
  all_goals
    intro result output heval <;>
      (try rcases heval with ⟨rfl, rfl⟩) <;>
      simp_all (config := { zetaDelta := true })
        [FiniteEvalContext.withState, fixClockHOLFinite, decClockHOLFinite,
          emptyLocalsHOLFinite, setVarHOLFinite,
          PanSemStateFiniteExact.toExact, PanSemStateFiniteExact.ofExact]

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
