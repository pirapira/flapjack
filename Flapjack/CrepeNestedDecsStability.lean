import Flapjack.CrepeDeclarationRelation
import Flapjack.CrepeExpressionStability

/-!
Stable evaluation of the expression prefix generated for a Pancake
declaration.  `nestedDecs` evaluates each expression after installing the
previous values in fresh locals; if those locals do not occur in the
expressions, the prefix has the same result as one flat expression-list
evaluation.
-/

namespace Flapjack

def updateCrepLocalList (locals : Nat → Option α) :
    List Nat → List α → Nat → Option α
  | [], [] => locals
  | name :: names, value :: values =>
      updateCrepLocalList (updateCrepLocal locals name value) names values
  | _, _ => locals

theorem updateCrepLocalList_of_not_mem
    (locals : Nat → Option α) (names : List Nat) (values : List α)
    (name : Nat) (hlength : names.length = values.length)
    (hnot : name ∉ names) :
    updateCrepLocalList locals names values name = locals name := by
  induction names generalizing locals values with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at hlength
  | cons head names ih =>
      cases values with
      | nil => simp at hlength
      | cons value values =>
          have hlengthTail : names.length = values.length := by
            simp at hlength
            exact hlength
          have hhead : name ≠ head := by
            intro heq
            apply hnot
            simp [heq]
          have htail : name ∉ names := by
            intro hmem
            apply hnot
            simp [hmem]
          simp only [updateCrepLocalList]
          rw [ih (locals := updateCrepLocal locals head value)
            (values := values) hlengthTail htail]
          simp [updateCrepLocal, hhead]

theorem readCrepLocals_updateCrepLocalList
    [OfNat α 0]
    (locals : Nat → Option α) (names : List Nat) (values : List α)
    (hlength : names.length = values.length)
    (hdistinct : CrepDistinctNames names) :
    readCrepLocals (updateCrepLocalList locals names values) names =
      some values := by
  induction names generalizing locals values with
  | nil =>
      cases values with
      | nil => simp [readCrepLocals]
      | cons value values => simp at hlength
  | cons name names ih =>
      rcases hdistinct with ⟨hnot, htailDistinct⟩
      cases values with
      | nil => simp at hlength
      | cons value values =>
          have hlengthTail : names.length = values.length := by
            simp at hlength
            exact hlength
          have htail := ih (locals := updateCrepLocal locals name value)
            (values := values) hlengthTail htailDistinct
          have hnameValue := updateCrepLocalList_of_not_mem
            (updateCrepLocal locals name value) names values name
            hlengthTail hnot
          simp only [updateCrepLocalList, readCrepLocals]
          simp [hnameValue, updateCrepLocal, htail]

theorem readCrepLocals_updateCrepLocalList_of_not_mem
    (locals : Nat → Option α) (names : List Nat) (values : List α)
    (slots : List Nat) (hlength : names.length = values.length)
    (hnot : ∀ name ∈ names, name ∉ slots) :
    readCrepLocals (updateCrepLocalList locals names values) slots =
      readCrepLocals locals slots := by
  induction names generalizing locals values slots with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at hlength
  | cons name names ih =>
      cases values with
      | nil => simp at hlength
      | cons value values =>
          have hlengthTail : names.length = values.length := by
            simp at hlength
            exact hlength
          have hname : name ∉ slots := hnot name (by simp)
          have htail : ∀ current ∈ names, current ∉ slots := by
            intro current hcurrent
            exact hnot current (by simp [hcurrent])
          simp only [updateCrepLocalList]
          rw [ih (locals := updateCrepLocal locals name value)
            (values := values) (slots := slots) hlengthTail htail
            ]
          exact readCrepLocals_update_of_not_mem locals name value slots hname

theorem crepNestedDecsEval_of_evalExps_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat)
    (expressions : List (CrepExp α)) (body : CrepProg α)
    (result : CrepControlResult α) (values : List α)
    (hlength : names.length = expressions.length)
    (hnot : ∀ name ∈ names, ∀ expression ∈ expressions,
      name ∉ crepExpVars expression)
    (heval : evalCrepFullExps state.locals state.memory
      baseAddress topAddress expressions = some values)
    (hbody : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := updateCrepLocalList state.locals names values } body =
      some result) :
    CrepNestedDecsEval functions primitive ffi sharedMem
      baseAddress topAddress fuel state names expressions body result := by
  induction names generalizing state expressions values with
  | nil =>
      cases expressions with
      | nil =>
          cases values with
          | nil =>
              simpa [CrepNestedDecsEval, updateCrepLocalList] using hbody
          | cons value values =>
              simp [evalCrepFullExps] at heval
      | cons expression expressions =>
          simp at hlength
  | cons name names ih =>
      cases expressions with
      | nil =>
          simp at hlength
      | cons expression expressions =>
          cases values with
          | nil =>
              cases hhead : evalCrepFullExp state.locals state.memory
                  baseAddress topAddress expression with
              | none => simp [evalCrepFullExps, hhead] at heval
              | some headValue =>
                  cases htail : evalCrepFullExps state.locals state.memory
                      baseAddress topAddress expressions with
                  | none => simp [evalCrepFullExps, hhead, htail] at heval
                  | some tailValues =>
                      simp [evalCrepFullExps, hhead, htail] at heval
          | cons value values =>
              have hlengthTail : names.length = expressions.length := by
                simp at hlength
                exact hlength
              cases hhead : evalCrepFullExp state.locals state.memory
                  baseAddress topAddress expression with
              | none =>
                  simp [evalCrepFullExps, hhead] at heval
              | some headValue =>
                  cases htail : evalCrepFullExps state.locals state.memory
                      baseAddress topAddress expressions with
                  | none =>
                      simp [evalCrepFullExps, hhead, htail] at heval
                  | some tailValues =>
                      have hvalues : headValue :: tailValues = value :: values := by
                        simpa [evalCrepFullExps, hhead, htail] using heval
                      cases hvalues
                      have htailStable :
                          evalCrepFullExps
                            (updateCrepLocal state.locals name value)
                            state.memory baseAddress topAddress expressions =
                            some values := by
                        exact evalCrepFullExps_update_of_forall_not_mem
                          state.locals state.memory baseAddress topAddress expressions
                          name value
                          (fun current hcurrent =>
                            hnot name (by simp) current (by simp [hcurrent]))
                          values htail
                      have hnotTail : ∀ current ∈ names, ∀ currentExpression ∈ expressions,
                          current ∉ crepExpVars currentExpression := by
                        intro current hcurrent currentExpression hcurrentExpression
                        exact hnot current (by simp [hcurrent]) currentExpression
                          (by simp [hcurrentExpression])
                      have hbodyTail :
                          evalCrepFullProg functions primitive ffi sharedMem
                            baseAddress topAddress fuel
                            { state with
                                locals := (updateCrepLocalList
                                  (updateCrepLocal state.locals name value)
                                  names values) } body = some result := by
                        simpa [updateCrepLocalList] using hbody
                      refine ⟨value, hhead, ?_⟩
                      exact ih (state := { state with
                          locals := updateCrepLocal state.locals name value })
                        (expressions := expressions) (values := values)
                        hlengthTail hnotTail htailStable hbodyTail

/-! Cake `pan_to_crepProps$evaluate_nested_decs_load_globals` specializes the
    ordinary nested-declaration argument to the generated global loads.  The
    generated expressions are local-free, so loading them once and installing
    their values in the declaration locals is stable under the recursive
    prefix evaluation.  This is the compact-state counterpart of that source
    theorem; the state-aware theorem can be obtained by the analogous
    specialization of the state relation. -/
theorem crepNestedDecsEval_loadGlobals_of_evalExps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress address stride : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat) (count : Nat)
    (body : CrepProg α) (result : CrepControlResult α) (values : List α)
    (hcount : names.length = count)
    (heval : evalCrepFullExps state.locals state.memory
      baseAddress topAddress (loadGlobals address stride count) = some values)
    (hbody : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := updateCrepLocalList state.locals names values } body =
      some result) :
    CrepNestedDecsEval functions primitive ffi sharedMem
      baseAddress topAddress fuel state names
      (loadGlobals address stride count) body result := by
  apply crepNestedDecsEval_of_evalExps_stable
  · exact hcount.trans (loadGlobals_length address stride count).symm
  · intro name hname expression hexpression hvariable
    have hmem : name ∈ (loadGlobals address stride count).flatMap crepExpVars :=
      List.mem_flatMap.mpr ⟨expression, hexpression, hvariable⟩
    rw [loadGlobals_crepExpVars_empty] at hmem
    simp at hmem
  · exact heval
  · exact hbody

/-! The evaluator-facing form of the same Cake nested-global-load theorem. -/
theorem evalCrepFullProg_nestedDecs_loadGlobals_of_evalExps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress address stride : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat) (count : Nat)
    (body : CrepProg α) (result : CrepControlResult α) (values : List α)
    (hcount : names.length = count)
    (hdistinct : CrepDistinctNames names)
    (heval : evalCrepFullExps state.locals state.memory
      baseAddress topAddress (loadGlobals address stride count) = some values)
    (hbody : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := updateCrepLocalList state.locals names values } body =
      some result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + names.length) state
      (nestedDecs names (loadGlobals address stride count) body) =
      some (restoreCrepResultList state.locals names result) := by
  have hnested := crepNestedDecsEval_loadGlobals_of_evalExps
    functions primitive ffi sharedMem baseAddress topAddress address stride fuel
    state names count body result values hcount heval hbody
  exact evalCrepFullProg_nestedDecs_of_eval
    functions primitive ffi sharedMem baseAddress topAddress fuel state names
    (loadGlobals address stride count) body result hdistinct hnested

theorem crepNestedDecsEval_body_of_evalExps_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat)
    (expressions : List (CrepExp α)) (body : CrepProg α)
    (result : CrepControlResult α) (values : List α)
    (hlength : names.length = expressions.length)
    (hnot : ∀ name ∈ names, ∀ expression ∈ expressions,
      name ∉ crepExpVars expression)
    (heval : evalCrepFullExps state.locals state.memory
      baseAddress topAddress expressions = some values)
    (hnested : CrepNestedDecsEval functions primitive ffi sharedMem
      baseAddress topAddress fuel state names expressions body result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := updateCrepLocalList state.locals names values } body =
      some result := by
  induction names generalizing state expressions values with
  | nil =>
      cases expressions with
      | nil =>
          cases values with
          | nil =>
              simpa [CrepNestedDecsEval, updateCrepLocalList] using hnested
          | cons value values =>
              simp [evalCrepFullExps] at heval
      | cons expression expressions =>
          simp at hlength
  | cons name names ih =>
      cases expressions with
      | nil =>
          simp at hlength
      | cons expression expressions =>
          cases values with
          | nil =>
              cases hhead : evalCrepFullExp state.locals state.memory
                  baseAddress topAddress expression with
              | none => simp [evalCrepFullExps, hhead] at heval
              | some headValue =>
                  cases htail : evalCrepFullExps state.locals state.memory
                      baseAddress topAddress expressions with
                  | none => simp [evalCrepFullExps, hhead, htail] at heval
                  | some tailValues =>
                      simp [evalCrepFullExps, hhead, htail] at heval
          | cons value values =>
              have hlengthTail : names.length = expressions.length := by
                simp at hlength
                exact hlength
              rcases hnested with ⟨targetValue, htargetValue, htailNested⟩
              cases hhead : evalCrepFullExp state.locals state.memory
                  baseAddress topAddress expression with
              | none =>
                  simp [evalCrepFullExps, hhead] at heval
              | some headValue =>
                  cases htail : evalCrepFullExps state.locals state.memory
                      baseAddress topAddress expressions with
                  | none =>
                      simp [evalCrepFullExps, hhead, htail] at heval
                  | some tailValues =>
                      have hvalues : headValue :: tailValues = value :: values := by
                        simpa [evalCrepFullExps, hhead, htail] using heval
                      cases hvalues
                      have htargetEq : targetValue = value := by
                        exact Option.some.inj (htargetValue.symm.trans hhead)
                      cases htargetEq
                      have htailStable :
                          evalCrepFullExps
                            (updateCrepLocal state.locals name value)
                            state.memory baseAddress topAddress expressions =
                            some values := by
                        exact evalCrepFullExps_update_of_forall_not_mem
                          state.locals state.memory baseAddress topAddress expressions
                          name value
                          (fun current hcurrent =>
                            hnot name (by simp) current (by simp [hcurrent]))
                          values htail
                      have hnotTail : ∀ current ∈ names,
                          ∀ currentExpression ∈ expressions,
                            current ∉ crepExpVars currentExpression := by
                        intro current hcurrent currentExpression hcurrentExpression
                        exact hnot current (by simp [hcurrent]) currentExpression
                          (by simp [hcurrentExpression])
                      exact ih (state := { state with
                          locals := updateCrepLocal state.locals name value })
                        (expressions := expressions) (values := values)
                        hlengthTail hnotTail htailStable htailNested


theorem crepNestedDecsStateEval_body_of_evalExps_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat)
    (expressions : List (CrepExp α)) (body : CrepProg α)
    (result : CrepControlResult α) (values : List α)
    (hlength : names.length = expressions.length)
    (hnot : ∀ name ∈ names, ∀ expression ∈ expressions,
      name ∉ crepExpVars expression)
    (heval : evalCrepFullExpsState state
      baseAddress topAddress expressions = some values)
    (hnested : CrepNestedDecsStateEval functions primitive ffi sharedMem
      baseAddress topAddress fuel state names expressions body result) :
    evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := updateCrepLocalList state.locals names values } body =
      some result := by
  induction names generalizing state expressions values with
  | nil =>
      cases expressions with
      | nil =>
          cases values with
          | nil =>
              simpa [CrepNestedDecsStateEval, updateCrepLocalList] using hnested
          | cons value values =>
              simp [evalCrepFullExpsState] at heval
      | cons expression expressions =>
          simp at hlength
  | cons name names ih =>
      cases expressions with
      | nil =>
          simp at hlength
      | cons expression expressions =>
          cases values with
          | nil =>
              cases hhead : evalCrepFullExpState state
                  baseAddress topAddress expression with
              | none => simp [evalCrepFullExpsState, hhead] at heval
              | some headValue =>
                  cases htail : evalCrepFullExpsState state
                      baseAddress topAddress expressions with
                  | none => simp [evalCrepFullExpsState, hhead, htail] at heval
                  | some tailValues =>
                      simp [evalCrepFullExpsState, hhead, htail] at heval
          | cons value values =>
              have hlengthTail : names.length = expressions.length := by
                simp at hlength
                exact hlength
              rcases hnested with ⟨targetValue, htargetValue, htailNested⟩
              cases hhead : evalCrepFullExpState state
                  baseAddress topAddress expression with
              | none =>
                  simp [evalCrepFullExpsState, hhead] at heval
              | some headValue =>
                  cases htail : evalCrepFullExpsState state
                      baseAddress topAddress expressions with
                  | none =>
                      simp [evalCrepFullExpsState, hhead, htail] at heval
                  | some tailValues =>
                      have hvalues : headValue :: tailValues = value :: values := by
                        simpa [evalCrepFullExpsState, hhead, htail] using heval
                      cases hvalues
                      have htargetEq : targetValue = value := by
                        exact Option.some.inj (htargetValue.symm.trans hhead)
                      cases htargetEq
                      have htailStable :
                          evalCrepFullExpsState
                            { state with locals := updateCrepLocal state.locals name value } baseAddress topAddress expressions =
                            some values := by
                        exact evalCrepFullExpsState_update_of_forall_not_mem
                          state baseAddress topAddress expressions
                          name value
                          (fun current hcurrent =>
                            hnot name (by simp) current (by simp [hcurrent]))
                          values htail
                      have hnotTail : ∀ current ∈ names,
                          ∀ currentExpression ∈ expressions,
                            current ∉ crepExpVars currentExpression := by
                        intro current hcurrent currentExpression hcurrentExpression
                        exact hnot current (by simp [hcurrent]) currentExpression
                          (by simp [hcurrentExpression])
                      exact ih (state := { state with
                          locals := updateCrepLocal state.locals name value })
                        (expressions := expressions) (values := values)
                        hlengthTail hnotTail htailStable htailNested

/-! The state relation is preserved when the target installs a list of fresh
locals (the shape produced by `nestedDecs`), as long as none of the fresh
slots occurs in any variable slot list recorded in the compile context.  This
is the target-side companion of `panValueCrepLocalsRel_update_word` and is the
reusable ingredient for the deep store/declaration instances, whose compiled
programs begin with `nestedDecs`. -/

theorem panValueCrepLocalsRel_updateCrepLocalList_fresh
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (names : List Nat) (values : List α)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlength : names.length = values.length)
    (hfresh : ∀ name shape slots,
      lookupInfo name context.vars = some (shape, slots) →
        ∀ slot, slot ∈ names → slot ∉ slots) :
    panValueCrepLocalsRel structs context sourceLocals
      (updateCrepLocalList crepLocals names values) := by
  intro name currentValue shape slots hsource hlookup
  have hold := hrel name currentValue shape slots hsource hlookup
  refine ⟨hold.1, ?_⟩
  rw [readCrepLocals_updateCrepLocalList_of_not_mem crepLocals names values slots
    hlength (fun slot hslot => hfresh name shape slots hlookup slot hslot)]
  exact hold.2

/-! Cake's `local_rel_gt_vmax_preserved`
    (`pan_to_crepProofScript.sml:2245-2260`) is the one-slot instance of
    fresh-local preservation.  The Cake context invariant
    `ctxt_max_el_leq` is represented here by the explicit `hbound` premise:
    every slot recorded for a related source local is at most `maxVar`.
    Keeping that premise visible makes the theorem applicable to contexts
    assembled by the Lean port without hiding the source proof obligation. -/
theorem panValueCrepLocalsRel_update_fresh_slot
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (slot : Nat) (value : α)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hslot : context.maxVar < slot)
    (hbound : ∀ name shape slots,
      lookupInfo name context.vars = some (shape, slots) →
        ∀ current, current ∈ slots → current ≤ context.maxVar) :
    panValueCrepLocalsRel structs context sourceLocals
      (updateCrepLocal crepLocals slot value) := by
  intro name currentValue shape slots hsource hlookup
  have hold := hrel name currentValue shape slots hsource hlookup
  refine ⟨hold.1, ?_⟩
  have hnot : slot ∉ slots := by
    intro hmem
    have hle := hbound name shape slots hlookup slot hmem
    omega
  have hsame := readCrepLocals_update_of_not_mem
    crepLocals slot value slots hnot
  exact hsame.trans hold.2

theorem panValueCrepStateRel_updateCrepLocalList_fresh
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepState : CrepState α)
    (names : List Nat) (values : List α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory crepState)
    (hlength : names.length = values.length)
    (hfresh : ∀ name shape slots,
      lookupInfo name context.vars = some (shape, slots) →
        ∀ slot, slot ∈ names → slot ∉ slots) :
    panValueCrepStateRel structs context sourceLocals sourceGlobals sourceMemory
      { crepState with
          locals := updateCrepLocalList crepState.locals names values } :=
  ⟨hrel.1,
    panValueCrepLocalsRel_updateCrepLocalList_fresh structs context sourceLocals
      crepState.locals names values hrel.2.1 hlength hfresh,
    hrel.2.2⟩

end Flapjack
