import Flapjack.Compile
import Flapjack.CrepeContextBounds
import Flapjack.CrepeAllocationNameLemmas
import Flapjack.PanToCrepCorrectnessBoundary

namespace Flapjack

/-! Structural well-founded induction principle for `Prog`.

    `Prog` is a nested inductive type (`call` stores an `Option` of a product
    containing a `Prog`), so Lean's `induction` tactic is unsupported and the
    automatically generated `compileProg.induct` is unusable (it is reported
    to have free variables).  This principle recovers structural induction on
    `sizeOf`, which is what the assigned-memory bound obligation needs. -/
theorem prog_sizeOf_induction (motive : Prog α → Prop)
    (step : ∀ program, (∀ sub, sizeOf sub < sizeOf program → motive sub) →
      motive program) :
    ∀ program, motive program := by
  intro program
  exact (measure sizeOf).wf.fix
    (fun program rec => step program (fun sub hlt => rec sub hlt)) program

/-- A variable is a context slot when it is stored in the slot list of some
    entry of the compilation context's variable map. -/
def CrepContextSlot [BEq String] (context : CompileContext α) (x : Nat) : Prop :=
  ∃ name shape slots, lookupInfo name context.vars = some (shape, slots) ∧ x ∈ slots

/-! Cake's `ctxt_max_el_leq` (`pan_to_crepProofScript.sml:1493`) in the
    `CrepContextSlot` presentation: every slot recorded by a context entry is
    bounded by the context maximum.  The assigned-free-vars induction uses
    this form when turning a context lookup into the contradiction
    `x ≤ maxVar < x`. -/
theorem crepContextSlot_le_max [BEq String]
    (context : CompileContext α)
    (hmax : panValueCtxtMax context.maxVar context.vars)
    {x : Nat} (hslot : CrepContextSlot context x) :
    x ≤ context.maxVar := by
  rcases hslot with ⟨name, shape, slots, hlookup, hx⟩
  exact hmax.2 name shape slots hlookup x hx

/-- Every slot drawn from the callee's return shape lies strictly above the
    context maximum (or the list is empty). -/
theorem functionReturnNames_bound (context : CompileContext α) (function : FunName) :
    ∀ x ∈ functionReturnNames context function, context.maxVar < x := by
  intro x hx
  cases hlookup : lookupInfo function context.functions with
  | none => simp [functionReturnNames, hlookup] at hx
  | some info =>
      obtain ⟨params, returnShape⟩ := info
      simp [functionReturnNames, hlookup] at hx
      exact allocatedNames_gt context returnShape hx

/-- `wrapRt` returns its argument unchanged whenever it succeeds. -/
theorem wrapRt_some_eq_some {info x : Shape × List Nat}
    (h : wrapRt (some info) = some x) : x = info := by
  obtain ⟨shape, slots⟩ := info
  cases shape with
  | one =>
      cases slots with
      | nil => simp [wrapRt] at h
      | cons slot rest =>
          have h' : some (.one, slot :: rest) = some x := by simpa [wrapRt] using h
          exact (Option.some.inj h').symm
  | comb shapes =>
      have h' : some (.comb shapes, slots) = some x := by simpa [wrapRt] using h
      exact (Option.some.inj h').symm
  | named name' =>
      have h' : some (.named name', slots) = some x := by simpa [wrapRt] using h
      exact (Option.some.inj h').symm

/-- The mapped slot list recovered from a successful `wrapRt` is the original
    second component. -/
theorem wrapRt_map_snd_of_some {info : Shape × List Nat} {names : List Nat}
    (h : (wrapRt (some info)).map Prod.snd = some names) : info.2 = names := by
  obtain ⟨x, hx, hfx⟩ := Option.map_eq_some_iff.mp h
  have hxinfo : x = info := wrapRt_some_eq_some hx
  subst hxinfo
  exact hfx

/-- The `.local` branch of `callDestinationNames`, exposed as an `Option.bind`
    so the standard `Option` reasoning lemmas apply. -/
theorem callDestinationNames_local_eq (context : CompileContext α) (name : VarName) :
    callDestinationNames context .local name =
      (lookupInfo name context.vars).bind
        (fun info => (wrapRt (some info)).map Prod.snd) := by
  unfold callDestinationNames
  cases lookupInfo name context.vars <;> rfl

/-- A successful local call-destination lookup returns exactly the slot list
    stored for that variable in the context. -/
theorem callDestinationNames_local_of_some
    (context : CompileContext α) (name : VarName) (names : List Nat)
    (h : callDestinationNames context .local name = some names) :
    ∃ shape slots, lookupInfo name context.vars = some (shape, slots) ∧ names = slots := by
  rw [callDestinationNames_local_eq] at h
  obtain ⟨info, hinfo, hmap⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨info.1, info.2, hinfo, (wrapRt_map_snd_of_some hmap).symm⟩

/-! When `compileProg` extends a Cake context with a fresh declaration, every
    slot visible through the extended finite-map view is either an old context
    slot or one of the newly allocated slots.  This is the context-map half of
    the `not_mem_context_assigned_mem_gt` induction. -/
theorem crepContextSlot_extended_or_gt [BEq String]
    (context : CompileContext α) (name : VarName) (shape : Shape)
    (slots : List Nat)
    (hslots : ∀ x ∈ slots, context.maxVar < x)
    {x : Nat}
    (h : CrepContextSlot
      { context with
        vars := (name, (shape, slots)) :: context.vars
        maxVar := context.maxVar + Shape.shapeSize shape } x) :
    CrepContextSlot context x ∨ context.maxVar < x := by
  rcases h with ⟨queriedName, queriedShape, queriedSlots, hlookup, hx⟩
  cases hname : (name == queriedName) with
  | false =>
      simp only [lookupInfo, hname] at hlookup
      exact Or.inl ⟨queriedName, queriedShape, queriedSlots, hlookup, hx⟩
  | true =>
      simp only [lookupInfo, hname] at hlookup
      have hpair : (shape, slots) = (queriedShape, queriedSlots) := by
        simpa using hlookup
      have hslotsEq : slots = queriedSlots := congrArg Prod.snd hpair
      exact Or.inr (hslots x (by rw [hslotsEq]; exact hx))

/-! The declaration branch of Cake's
    `not_mem_context_assigned_mem_gt` (`pan_to_crepProofScript.sml:1260`):
    once the recursive body has no assigned free occurrence of `x`, the fresh
    slots introduced by the declaration nest cannot introduce one either. -/
theorem not_mem_crepAssignedFreeVars_compileProg_dec
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (name : VarName) (shape : Shape)
    (value : Exp α) (body : Prog α) (x : Nat)
    (expressions : List (CrepExp α)) (valueShape : Shape)
    (hvalue : compileExp context value = (expressions, valueShape))
    (hbody : x ∉ crepAssignedFreeVars
      (compileProg
        { context with
          vars := (name, (valueShape, allocatedNames context valueShape)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize valueShape } body)) :
    x ∉ crepAssignedFreeVars (compileProg context (.dec name shape value body)) := by
  simp only [compileProg, hvalue]
  by_cases hlength : (allocatedNames context valueShape).length = expressions.length
  · rw [if_pos hlength]
    exact not_mem_crepAssignedFreeVars_nestedDecs
      (allocatedNames context valueShape) expressions _ hlength hbody
  · simp [hlength, crepAssignedFreeVars]

/-! The declaration-call branch has the same shape as the Cake proof's
    declaration nest: the generated return slots are bound by `nestedDecs`,
    leaving only the recursively compiled body as a possible assigned-free
    source. -/
theorem not_mem_crepAssignedFreeVars_compileProg_decCall
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (name : VarName) (shape : Shape)
    (function : FunName) (arguments : List (Exp α)) (body : Prog α) (x : Nat)
    (hbody : x ∉ crepAssignedFreeVars
      (compileProg
        { context with
          vars := (name, (shape, allocatedNames context shape)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize shape } body))
    (hfresh : x ∉ allocatedNames context shape) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.decCall name shape function arguments body)) := by
  simp only [compileProg]
  apply not_mem_crepAssignedFreeVars_nestedDecs
  · simp
  · simp only [crepAssignedFreeVars, List.mem_append]
    intro hx
    rcases hx with hx | hx
    · exact hfresh hx
    · exact hbody hx

/-! The primitive branch of the Cake bound proof: the destination slots come
    from the context, while the generated argument temporaries are hidden by
    the surrounding declaration nest. -/
theorem not_mem_crepAssignedFreeVars_compileProg_primitive
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (name : VarName) (operator : PrimOp)
    (arguments : List (Exp α)) (x : Nat)
    (hslot : ∀ shape slots,
      lookupInfo name context.vars = some (shape, slots) → x ∉ slots) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.primitive name operator arguments)) := by
  simp only [compileProg]
  cases hlookup : lookupInfo name context.vars with
  | none => simp [crepAssignedFreeVars]
  | some info =>
      obtain ⟨shape, slots⟩ := info
      apply not_mem_crepAssignedFreeVars_nestedDecs
      · simp [freshNames]
      · simp only [crepAssignedFreeVars]
        exact hslot shape slots hlookup

/-! The store branch of Cake's `not_mem_context_assigned_mem_gt`:
    successful shared stores assign no local variables, and the declaration
    temporaries surrounding the address/value evaluation therefore cannot
    contribute an assigned-free variable.  Malformed expression shapes use
    the compiler's `Skip` fallback and are immediate. -/
theorem not_mem_crepAssignedFreeVars_compileProg_store
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (address value : Exp α) (x : Nat) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.store address value)) := by
  simp only [compileProg]
  cases haddress : compileExp context address with
  | mk addressExpressions addressShape =>
      cases addressExpressions with
      | nil => simp [crepAssignedFreeVars]
      | cons compiledAddress rest =>
          cases hvalue : compileExp context value with
          | mk values valueShape =>
              simp only
              by_cases hlength : values.length = Shape.shapeSize valueShape
              · rw [if_pos hlength]
                apply not_mem_crepAssignedFreeVars_nestedDecs
                · simp [freshNames_length, hlength]
                · simp [crepAssignedFreeVars_nestedSeq_stores]
              · simp [hlength, crepAssignedFreeVars]

/-! The local-assignment branch of Cake's assigned-free bound.  When the
    destination and expression variables are distinct, the generated zip of
    assignments exposes the destination slot list directly.  Otherwise Cake
    introduces fresh temporaries, whose declaration nest hides the same slot
    list while preserving the assignment result. -/
theorem not_mem_crepAssignedFreeVars_compileProg_assign_local
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (name : VarName) (value : Exp α) (x : Nat)
    (hslot : ∀ shape slots,
      lookupInfo name context.vars = some (shape, slots) → x ∉ slots) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.assign .local name value)) := by
  simp only [compileProg]
  cases hlookup : lookupInfo name context.vars with
  | none => simp [crepAssignedFreeVars]
  | some info =>
      obtain ⟨shape, names⟩ := info
      cases hcompile : compileExp context value with
      | mk expressions valueShape =>
          simp only
          by_cases hlength : names.length = expressions.length
          · rw [if_pos hlength]
            by_cases hdistinct : distinctLists names (expressions.flatMap crepExpVars)
            · rw [if_pos hdistinct]
              rw [crepAssignedFreeVars_nestedSeq_assign_zipWith names expressions hlength]
              exact hslot shape names hlookup
            · rw [if_neg hdistinct]
              apply not_mem_crepAssignedFreeVars_nestedDecs
              · simp [freshNames_length, hlength]
              · rw [← List.zipWith_map_right (f := fun temporary =>
                    (CrepExp.var (α := α) temporary))
                    (g := fun destination expression =>
                      CrepProg.assign destination expression)]
                rw [crepAssignedFreeVars_nestedSeq_assign_zipWith names
                      ((freshNames context names.length 1).map
                        (fun temporary => CrepExp.var temporary))
                      (by simp [freshNames_length])]
                exact hslot shape names hlookup
          · rw [if_neg hlength]
            simp [crepAssignedFreeVars]

/-! ExtCall introduces four fresh declarations around a Crepe `extCall`, which
    has no assigned-free locals.  This is the corresponding `ExtCall` branch
    of Cake's induction; malformed expressions take the `Skip` fallback. -/
theorem not_mem_crepAssignedFreeVars_compileProg_extCall
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (function : FunName)
    (configuration configurationLength array arrayLength : Exp α) (x : Nat) :
    x ∉ crepAssignedFreeVars
      (compileProg context
        (.extCall function configuration configurationLength array arrayLength)) := by
  simp only [compileProg]
  cases hconfiguration : firstCompiledExp context configuration with
  | none => simp [crepAssignedFreeVars]
  | some compiledConfiguration =>
      cases hconfigurationLength : firstCompiledExp context configurationLength with
      | none => simp [crepAssignedFreeVars]
      | some compiledConfigurationLength =>
          cases harray : firstCompiledExp context array with
          | none => simp [crepAssignedFreeVars]
          | some compiledArray =>
              cases harrayLength : firstCompiledExp context arrayLength with
              | none => simp [crepAssignedFreeVars]
              | some compiledArrayLength =>
                  simp only
                  apply not_mem_crepAssignedFreeVars_nestedDecs
                  · simp
                  · simp [crepAssignedFreeVars]

/-! Raising stores the payload in globals through a declaration nest, then
    raises.  Both the store-global sequence and the raise have empty
    assigned-free sets, so the branch is independent of the chosen exception
    code and payload shape. -/
theorem not_mem_crepAssignedFreeVars_compileProg_raise
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (exception : ExceptionId) (value : Exp α) (x : Nat) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.raise exception value)) := by
  simp only [compileProg]
  cases hexception : lookupInfo exception context.exceptions with
  | none => simp [crepAssignedFreeVars]
  | some code =>
      cases hcompile : compileExp context value with
      | mk expressions valueShape =>
          simp only
          by_cases hlength : expressions.length = Shape.shapeSize valueShape
          · rw [if_pos hlength]
            simp only [crepAssignedFreeVars, List.append_nil]
            apply not_mem_crepAssignedFreeVars_nestedDecs
            · simp [freshNames_length, hlength]
            · rw [crepAssignedFreeVars_nestedSeq_storeGlobals]
              simp
          · rw [if_neg hlength]
            simp [crepAssignedFreeVars]

/-! `ShMemStore` binds its single temporary around the generated `shMem`
    instruction.  Unlike the sufficient nested-declaration lemma used for
    stores, this branch uses the exact declaration-filter equation because
    the temporary is itself assigned by the body and is then removed. -/
theorem not_mem_crepAssignedFreeVars_compileProg_shMemStore
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (size : OpSize)
    (address value : Exp α) (x : Nat) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.shMemStore size address value)) := by
  simp only [compileProg]
  cases haddress : firstCompiledExpAnyShape context address with
  | none => simp [crepAssignedFreeVars]
  | some compiledAddress =>
      cases hvalue : firstCompiledExpAnyShape context value with
      | none => simp [crepAssignedFreeVars]
      | some compiledValue =>
          simp only
          rw [crepAssignedFreeVars_nestedDecs_append
            [maxCrepExpVar [compiledAddress] + 1] [compiledValue]
            (.shMem (storeMemOp size) (maxCrepExpVar [compiledAddress] + 1)
              compiledAddress) (by simp)]
          simp [crepAssignedFreeVars]

/-- `crepNestedSeq` of `assign` statements built from a zip of names with
    variables introduced by `freshNames` still has exactly `names` as its
    assigned free variables. -/
theorem crepAssignedFreeVars_assignVar_zipWith {α : Type} (names temporaries : List Nat)
    (h : names.length = temporaries.length) :
    crepAssignedFreeVars
        (crepNestedSeq
          (names.zipWith (fun name temporary => CrepProg.assign name (.var (α := α) temporary))
            temporaries)) = names := by
  rw [← List.zipWith_map_right (f := fun t => (CrepExp.var (α := α) t))
        (g := fun name value => CrepProg.assign name value)]
  exact crepAssignedFreeVars_nestedSeq_assign_zipWith names
    (temporaries.map (fun t => (CrepExp.var (α := α) t))) (by rw [h, List.length_map])

/-- A successful call-destination lookup (for either variable kind) returns
    exactly the slot list stored for that variable in the context. -/
theorem callDestinationNames_some_slot (context : CompileContext α) (kind : VarKind)
    (name : VarName) (names : List Nat)
    (h : callDestinationNames context kind name = some names) :
    ∃ shape slots, lookupInfo name context.vars = some (shape, slots) ∧ names = slots := by
  cases kind with
  | «global» => simp [callDestinationNames] at h
  | «local» => exact callDestinationNames_local_of_some context name names h

end Flapjack
