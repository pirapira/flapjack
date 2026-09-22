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

/-! Fixed-width stores lower directly to Crepe store instructions (or `Skip`)
    and therefore have no assigned-free locals. -/
theorem not_mem_crepAssignedFreeVars_compileProg_store32
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (address value : Exp α) (x : Nat) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.store32 address value)) := by
  simp only [compileProg]
  cases haddress : compileExp context address with
  | mk addressExpressions addressShape =>
      cases addressExpressions with
      | nil => simp [crepAssignedFreeVars]
      | cons compiledAddress rest =>
          cases hvalue : compileExp context value with
          | mk values valueShape =>
              cases values with
              | nil => simp [crepAssignedFreeVars]
              | cons compiledValue rest => simp [crepAssignedFreeVars]

theorem not_mem_crepAssignedFreeVars_compileProg_storeByte
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (address value : Exp α) (x : Nat) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.storeByte address value)) := by
  simp only [compileProg]
  cases haddress : compileExp context address with
  | mk addressExpressions addressShape =>
      cases addressExpressions with
      | nil => simp [crepAssignedFreeVars]
      | cons compiledAddress rest =>
          cases hvalue : compileExp context value with
          | mk values valueShape =>
              cases values with
              | nil => simp [crepAssignedFreeVars]
              | cons compiledValue rest => simp [crepAssignedFreeVars]

/-! A local shared-memory load assigns the first slot of its destination;
    Cake's context-slot hypothesis rules that slot out.  Unknown/global
    destinations and malformed addresses use `Skip`. -/
theorem not_mem_crepAssignedFreeVars_compileProg_shMemLoad_local
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (size : OpSize) (name : VarName)
    (address : Exp α) (x : Nat)
    (hslot : ∀ shape slots,
      lookupInfo name context.vars = some (shape, slots) → x ∉ slots) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.shMemLoad size .local name address)) := by
  simp only [compileProg]
  cases hlookup : lookupInfo name context.vars with
  | none => simp [crepAssignedFreeVars]
  | some info =>
      obtain ⟨shape, names⟩ := info
      cases hnames : names with
      | nil => simp [crepAssignedFreeVars]
      | cons destination rest =>
          cases haddress : firstCompiledExpAnyShape context address with
          | none => simp [crepAssignedFreeVars]
          | some compiledAddress =>
              simp only
              intro hx
              have hlookup' : lookupInfo name context.vars =
                  some (shape, destination :: rest) := by
                simpa [hnames] using hlookup
              have hdestination : x = destination := by
                simpa [crepAssignedFreeVars] using hx
              apply hslot shape (destination :: rest) hlookup'
              simp [hdestination]

/-! Structural sequence composition for the recursive `compileProg` proof. -/
theorem not_mem_crepAssignedFreeVars_compileProg_seq
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (first second : Prog α) (x : Nat)
    (hfirst : x ∉ crepAssignedFreeVars (compileProg context first))
    (hsecond : x ∉ crepAssignedFreeVars (compileProg context second)) :
    x ∉ crepAssignedFreeVars (compileProg context (.seq first second)) := by
  simp only [compileProg, crepAssignedFreeVars, List.mem_append]
  intro h
  rcases h with h | h
  · exact hfirst h
  · exact hsecond h

/-! Conditional composition: the compiled condition does not assign locals;
    only the two recursive branches contribute to `crepAssignedFreeVars`. -/
theorem not_mem_crepAssignedFreeVars_compileProg_ite
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (condition : Exp α)
    (thenBranch elseBranch : Prog α) (x : Nat)
    (hthen : x ∉ crepAssignedFreeVars (compileProg context thenBranch))
    ( helse : x ∉ crepAssignedFreeVars (compileProg context elseBranch)) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.ite condition thenBranch elseBranch)) := by
  simp only [compileProg]
  cases hcondition : compileExp context condition with
  | mk expressions conditionShape =>
      cases expressions with
      | nil => simp [crepAssignedFreeVars]
      | cons compiledCondition rest =>
          simp only
          simp only [crepAssignedFreeVars, List.mem_append]
          intro h
          rcases h with h | h
          · exact hthen h
          · exact helse h

/-! While-loop composition: the condition is an expression and the body is
    the only possible source of assigned-free locals. -/
theorem not_mem_crepAssignedFreeVars_compileProg_while
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (condition : Exp α) (body : Prog α) (x : Nat)
    (hbody : x ∉ crepAssignedFreeVars (compileProg context body)) :
    x ∉ crepAssignedFreeVars
      (compileProg context (.while condition body)) := by
  simp only [compileProg]
  cases hcondition : compileExp context condition with
  | mk expressions conditionShape =>
      cases expressions with
      | nil => simp [crepAssignedFreeVars]
      | cons compiledCondition rest =>
          simp only
          simpa [crepAssignedFreeVars] using hbody

/-! Terminal source constructors lower to Crepe instructions with empty
    assigned-free sets (or to `Skip`). -/
theorem not_mem_crepAssignedFreeVars_compileProg_return
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (value : Exp α) (x : Nat) :
    x ∉ crepAssignedFreeVars (compileProg context (.return value)) := by
  simp [compileProg, crepAssignedFreeVars]

theorem not_mem_crepAssignedFreeVars_compileProg_break
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (x : Nat) :
    x ∉ crepAssignedFreeVars (compileProg context .break) := by
  simp [compileProg, crepAssignedFreeVars]

theorem not_mem_crepAssignedFreeVars_compileProg_continue
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (x : Nat) :
    x ∉ crepAssignedFreeVars (compileProg context .continue) := by
  simp [compileProg, crepAssignedFreeVars]

theorem not_mem_crepAssignedFreeVars_compileProg_tick
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (x : Nat) :
    x ∉ crepAssignedFreeVars (compileProg context .tick) := by
  simp [compileProg, crepAssignedFreeVars]

theorem not_mem_crepAssignedFreeVars_compileProg_annot
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (tag text : String) (x : Nat) :
    x ∉ crepAssignedFreeVars (compileProg context (.annot tag text)) := by
  simp [compileProg, crepAssignedFreeVars]

/-! Call lowering without an exception handler.  A standalone call binds the
    callee's fresh return slots; an assigned call either keeps its context
    destination slots or falls back to a call with no assigned result. -/
theorem not_mem_crepAssignedFreeVars_compileProg_call_no_handler
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α))
    (destination : Option (VarKind × VarName)) (x : Nat)
    (hx : x ≤ context.maxVar)
    (hslot : ∀ name shape slots,
      lookupInfo name context.vars = some (shape, slots) → x ∉ slots) :
    x ∉ crepAssignedFreeVars
      (compileProg context
        (.call (some (destination, none)) function arguments)) := by
  simp only [compileProg]
  cases destination with
  | none =>
      simp only
      apply not_mem_crepAssignedFreeVars_nestedDecs
      · simp
      · simp only [crepAssignedFreeVars]
        intro hx
        have hreturns : x ∉ functionReturnNames context function := by
          intro hmem
          have hbound := functionReturnNames_bound context function x hmem
          omega
        exact hreturns hx
  | some destination =>
      obtain ⟨kind, name⟩ := destination
      cases hdest : callDestinationNames context kind name with
      | none =>
          simp only [hdest]
          simp [crepAssignedFreeVars]
      | some names =>
          cases kind with
          | global => simp [callDestinationNames] at hdest
          | «local» =>
              simp only [hdest, crepAssignedFreeVars]
              intro hmem
              obtain ⟨shape, slots, hlookup, hnames⟩ :=
                callDestinationNames_local_of_some context name names hdest
              apply hslot name shape slots hlookup
              rw [← hnames]
              exact hmem

/-! Known-exception call handlers.  The handler setup is either `Skip` for an
    unknown handler destination or `assignRet` for a context destination;
    both are followed by the recursively compiled handler body. -/
theorem not_mem_crepAssignedFreeVars_compileProg_call_known_handler
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α))
    (destination : Option (VarKind × VarName))
    (exception : ExceptionId) (handlerVar : VarName)
    (handlerProgram : Prog α) (code : α) (x : Nat)
    (hx : x ≤ context.maxVar)
    (hexception : lookupInfo exception context.exceptions = some code)
    (hbody : x ∉ crepAssignedFreeVars (compileProg context handlerProgram))
    (hslot : ∀ name shape slots,
      lookupInfo name context.vars = some (shape, slots) → x ∉ slots) :
    x ∉ crepAssignedFreeVars
      (compileProg context
        (.call (some (destination, some (exception, handlerVar, handlerProgram)))
          function arguments)) := by
  simp only [compileProg]
  rw [hexception]
  cases hhandlerVar : lookupInfo handlerVar context.vars with
  | none =>
      have hhandlerFree : x ∉ crepAssignedFreeVars
          (.seq (.skip : CrepProg α) (compileProg context handlerProgram)) := by
        simpa [crepAssignedFreeVars] using hbody
      cases destination with
      | none =>
          simp only
          apply not_mem_crepAssignedFreeVars_nestedDecs
          · simp
          · simp only [crepAssignedFreeVars, List.mem_append]
            intro h
            rcases h with h | h
            · have hreturns : x ∉ functionReturnNames context function := by
                intro hmem
                have hbound := functionReturnNames_bound context function x hmem
                omega
              exact hreturns h
            · rcases h with h | h
              · simp at h
              · exact hbody h
      | some destination =>
          obtain ⟨kind, name⟩ := destination
          cases hdest : callDestinationNames context kind name with
          | none =>
              simp only [hdest]
              change x ∉ crepAssignedFreeVars
                (.call (some ([], some (code,
                  .seq (.skip : CrepProg α) (compileProg context handlerProgram))))
                  function (compileArgs context arguments))
              simpa only [crepAssignedFreeVars, List.nil_append] using hhandlerFree
          | some names =>
              cases kind with
              | global => simp [callDestinationNames] at hdest
              | «local» =>
                  simp only [hdest, crepAssignedFreeVars, List.mem_append]
                  intro h
                  rcases h with h | h
                  · obtain ⟨shape, slots, hlookup, hnames⟩ :=
                      callDestinationNames_local_of_some context name names hdest
                    apply hslot name shape slots hlookup
                    rw [← hnames]
                    exact h
                  · rcases h with h | h
                    · simp at h
                    · exact hbody h
  | some info =>
      obtain ⟨shape, names⟩ := info
      have hnames : x ∉ names := hslot handlerVar shape names hhandlerVar
      have hassign : x ∉ crepAssignedFreeVars (assignRet context.bytesInWord names) := by
        rw [crepAssignedFreeVars_assignRet]
        exact hnames
      have hhandlerFree : x ∉ crepAssignedFreeVars
          (.seq (assignRet context.bytesInWord names)
            (compileProg context handlerProgram)) := by
        simp only [crepAssignedFreeVars, List.mem_append]
        intro h
        rcases h with h | h
        · exact hassign h
        · exact hbody h
      cases destination with
      | none =>
          simp only
          apply not_mem_crepAssignedFreeVars_nestedDecs
          · simp
          · simp only [crepAssignedFreeVars, List.mem_append]
            intro h
            rcases h with h | h
            · have hreturns : x ∉ functionReturnNames context function := by
                intro hmem
                have hbound := functionReturnNames_bound context function x hmem
                omega
              exact hreturns h
            · rcases h with h | h
              · exact hassign h
              · exact hbody h
      | some destination =>
          obtain ⟨kind, name⟩ := destination
          cases hdest : callDestinationNames context kind name with
          | none =>
              simp only [hdest]
              change x ∉ crepAssignedFreeVars
                (.call (some ([], some (code,
                  .seq (assignRet context.bytesInWord names)
                    (compileProg context handlerProgram))))
                  function (compileArgs context arguments))
              simpa only [crepAssignedFreeVars, List.nil_append] using hhandlerFree
          | some destinationNames =>
              cases kind with
              | global => simp [callDestinationNames] at hdest
              | «local» =>
                  simp only [hdest, crepAssignedFreeVars, List.mem_append]
                  intro h
                  rcases h with h | h
                  · obtain ⟨destinationShape, slots, hlookup, hnames⟩ :=
                      callDestinationNames_local_of_some context name destinationNames hdest
                    apply hslot name destinationShape slots hlookup
                    rw [← hnames]
                    exact h
                  · rcases h with h | h
                    · exact hassign h
                    · exact hbody h

/-- `crepNestedSeq` of `assign` statements built from a zip of names with
    variables introduced by `freshNames` still has exactly `names` as its
    assigned free variables. -/
theorem crepAssignedFreeVars_assignVar_zipWith {α : Type _} (names temporaries : List Nat)
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

/-- Free variables of a compiled call handler: the handler-setup assignment
    contributes exactly the handler's destination names, and the compiled body
    contributes its own free variables. -/
theorem crepAssignedFreeVars_seq_assignRet_compileProg [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (handlerNames : List Nat) (handlerProgram : Prog α) :
    crepAssignedFreeVars
        (.seq (assignRet context.bytesInWord handlerNames) (compileProg context handlerProgram)) =
      handlerNames ++ crepAssignedFreeVars (compileProg context handlerProgram) := by
  simp [crepAssignedFreeVars, crepAssignedFreeVars_assignRet]

/-- Looking up the freshly bound name after a context extension (`|+` update
    self case, `finite_mapTheory.FLOOKUP_UPDATE`). -/
theorem lookupInfo_cons_self [BEq String] [LawfulBEq String] (name : String)
    (value : α) (entries : InfoMap α) :
    lookupInfo name ((name, value) :: entries) = some value := by
  simp [lookupInfo]

/-- Looking up a different name after a context extension is unchanged (`|+`
    update other case, `finite_mapTheory.FLOOKUP_UPDATE`). -/
theorem lookupInfo_cons_ne [BEq String] (key name : String) (value : α)
    (entries : InfoMap α) (h : (name == key) = false) :
    lookupInfo key ((name, value) :: entries) = lookupInfo key entries := by
  simp [lookupInfo, h]

/-- Extending a compilation context with a declaration whose slot names all
    lie strictly above the current maximum introduces no context slots at or
    below that maximum.  This is the transport used by the recursive cases of
    the assigned-memory bound: when a slot variable is already bounded by
    `context.maxVar`, a slot in the extended context is a slot in the original
    one, because the fresh declaration's names all exceed the maximum. -/
theorem crepContextSlot_cons_of_le [BEq String] (context : CompileContext α)
    (name : String) (shape : Shape) (names : List Nat)
    (hnames : ∀ y ∈ names, context.maxVar < y) {x : Nat} (hx : x ≤ context.maxVar)
    (h : CrepContextSlot
      { context with vars := (name, (shape, names)) :: context.vars } x) :
    CrepContextSlot context x := by
  obtain ⟨n, sh, slots, hlookup, hmem⟩ := h
  simp only [lookupInfo] at hlookup
  split at hlookup
  · have hpair : (shape, names) = (sh, slots) := Option.some.inj hlookup
    have hslots : slots = names := (congrArg Prod.snd hpair).symm
    rw [hslots] at hmem
    exact absurd (hnames x hmem) (by omega)
  · exact ⟨n, sh, slots, hlookup, hmem⟩

/-- Membership of a compiled nested declaration body's free variables in the
    free variables of the body alone (the declared names only remove entries). -/
theorem mem_crepAssignedFreeVars_nestedDecs {α : Type _} (names : List Nat)
    (values : List (CrepExp α)) (body : CrepProg α)
    (h : names.length = values.length) {x : Nat}
    (hmem : x ∈ crepAssignedFreeVars (nestedDecs names values body)) :
    x ∈ crepAssignedFreeVars body := by
  rw [crepAssignedFreeVars_nestedDecs_append names values body h] at hmem
  exact (List.mem_filter.mp hmem).1

/-! Full structural counterpart of Cake's
    `not_mem_context_assigned_mem_gt` (`pan_to_crepProofScript.sml:1252`).
    The context maximum and slot-map hypotheses are threaded through the
    declaration constructors; all expression temporaries are hidden by the
    corresponding `nestedDecs` equations. -/
theorem not_mem_crepAssignedFreeVars_compileProg_bound
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (program : Prog α) (x : Nat)
    (hmax : panValueCtxtMax context.maxVar context.vars)
    (hslot : panValueSlotBound x context.vars)
    (hx : x ≤ context.maxVar) :
    x ∉ crepAssignedFreeVars (compileProg context program) := by
  refine (prog_sizeOf_induction (motive := fun program =>
    ∀ (context : CompileContext α) (x : Nat),
      panValueCtxtMax context.maxVar context.vars →
      panValueSlotBound x context.vars →
      x ≤ context.maxVar →
      x ∉ crepAssignedFreeVars (compileProg context program))
    (step := ?_) program) context x hmax hslot hx
  intro program ih context x hmax hslot hx
  cases program with
  | skip => simp [compileProg, crepAssignedFreeVars]
  | dec name declaredShape value body =>
      cases hcompile : compileExp context value with
      | mk expressions valueShape =>
          simp only [compileProg, hcompile]
          by_cases hlength : (allocatedNames context valueShape).length = expressions.length
          · rw [if_pos hlength]
            have hmaxAtNew : panValueCtxtMax
                (context.maxVar + Shape.shapeSize valueShape) context.vars := by
              refine ⟨by omega, ?_⟩
              intro oldName oldShape oldSlots hlookup slot hmem
              have hle := hmax.2 oldName oldShape oldSlots hlookup slot hmem
              omega
            have hmaxNext : panValueCtxtMax
                (context.maxVar + Shape.shapeSize valueShape)
                ((name, (valueShape, allocatedNames context valueShape)) :: context.vars) :=
              panValueCtxtMax_cons_of _ _ _ _ _ hmaxAtNew (by
                intro slot hmem
                exact allocatedNames_slot_le context valueShape slot hmem)
            have hslotNext : panValueSlotBound x
                ((name, (valueShape, allocatedNames context valueShape)) :: context.vars) :=
              panValueSlotBound_cons_of x name valueShape
                (allocatedNames context valueShape) context.vars hslot
                (not_mem_allocatedNames context valueShape hx)
            have hxNext : x ≤ context.maxVar + Shape.shapeSize valueShape := by omega
            have hbody := ih body (by decreasing_trivial)
              { context with
                vars := (name, (valueShape, allocatedNames context valueShape)) :: context.vars
                maxVar := context.maxVar + Shape.shapeSize valueShape }
              x hmaxNext hslotNext hxNext
            apply not_mem_crepAssignedFreeVars_nestedDecs
            · simpa [allocatedNames_length] using hlength
            · exact hbody
          · rw [if_neg hlength]
            simp [crepAssignedFreeVars]
  | assign kind name value =>
      cases kind with
      | global => simp [compileProg, crepAssignedFreeVars]
      | «local» =>
          apply not_mem_crepAssignedFreeVars_compileProg_assign_local context name value x
          intro shape slots hlookup
          exact hslot name shape slots hlookup
  | primitive name operator arguments =>
      apply not_mem_crepAssignedFreeVars_compileProg_primitive
        context name operator arguments x
      intro shape slots hlookup
      exact hslot name shape slots hlookup
  | store address value =>
      exact not_mem_crepAssignedFreeVars_compileProg_store context address value x
  | store32 address value =>
      exact not_mem_crepAssignedFreeVars_compileProg_store32 context address value x
  | storeByte address value =>
      exact not_mem_crepAssignedFreeVars_compileProg_storeByte context address value x
  | seq first second =>
      apply not_mem_crepAssignedFreeVars_compileProg_seq context first second x
      · exact ih first (by decreasing_trivial) context x hmax hslot hx
      · exact ih second (by decreasing_trivial) context x hmax hslot hx
  | ite condition thenBranch elseBranch =>
      apply not_mem_crepAssignedFreeVars_compileProg_ite context condition thenBranch elseBranch x
      · exact ih thenBranch (by decreasing_trivial) context x hmax hslot hx
      · exact ih elseBranch (by decreasing_trivial) context x hmax hslot hx
  | «while» condition body =>
      apply not_mem_crepAssignedFreeVars_compileProg_while context condition body x
      exact ih body (by decreasing_trivial) context x hmax hslot hx
  | «break» => exact not_mem_crepAssignedFreeVars_compileProg_break context x
  | «continue» => exact not_mem_crepAssignedFreeVars_compileProg_continue context x
  | call info function arguments =>
      cases info with
      | none => simp [compileProg, crepAssignedFreeVars]
      | some info =>
          obtain ⟨destination, handler⟩ := info
          cases handler with
          | none =>
              apply not_mem_crepAssignedFreeVars_compileProg_call_no_handler
                context function arguments destination x hx
              intro name shape slots hlookup
              exact hslot name shape slots hlookup
          | some handlerInfo =>
              obtain ⟨exception, handlerVar, handlerProgram⟩ := handlerInfo
              cases hlookup : lookupInfo exception context.exceptions with
              | none =>
                  simpa [compileProg, hlookup] using
                    (not_mem_crepAssignedFreeVars_compileProg_call_no_handler
                      context function arguments destination x hx (by
                        intro name shape slots hlookup
                        exact hslot name shape slots hlookup))
              | some code =>
                  apply not_mem_crepAssignedFreeVars_compileProg_call_known_handler
                    context function arguments destination exception handlerVar
                    handlerProgram code x hx hlookup
                    (ih handlerProgram (by decreasing_trivial) context x hmax hslot hx)
                  intro name shape slots hlookup
                  exact hslot name shape slots hlookup
  | decCall name shape function arguments body =>
      have hmaxAtNew : panValueCtxtMax
          (context.maxVar + Shape.shapeSize shape) context.vars := by
        refine ⟨by omega, ?_⟩
        intro oldName oldShape oldSlots hlookup slot hmem
        have hle := hmax.2 oldName oldShape oldSlots hlookup slot hmem
        omega
      have hmaxNext : panValueCtxtMax
          (context.maxVar + Shape.shapeSize shape)
          ((name, (shape, allocatedNames context shape)) :: context.vars) :=
        panValueCtxtMax_cons_of _ _ _ _ _ hmaxAtNew (by
          intro slot hmem
          exact allocatedNames_slot_le context shape slot hmem)
      have hslotNext : panValueSlotBound x
          ((name, (shape, allocatedNames context shape)) :: context.vars) :=
        panValueSlotBound_cons_of x name shape (allocatedNames context shape)
          context.vars hslot (not_mem_allocatedNames context shape hx)
      have hxNext : x ≤ context.maxVar + Shape.shapeSize shape := by omega
      have hbody := ih body (by decreasing_trivial)
        { context with
          vars := (name, (shape, allocatedNames context shape)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize shape }
        x hmaxNext hslotNext hxNext
      simp only [compileProg]
      apply not_mem_crepAssignedFreeVars_nestedDecs
      · simp
      · simp only [crepAssignedFreeVars, List.mem_append]
        intro h
        rcases h with h | h
        · exact not_mem_allocatedNames context shape hx h
        · exact hbody h
  | extCall function configuration configurationLength array arrayLength =>
      exact not_mem_crepAssignedFreeVars_compileProg_extCall context function
        configuration configurationLength array arrayLength x
  | raise exception value =>
      exact not_mem_crepAssignedFreeVars_compileProg_raise context exception value x
  | «return» value =>
      exact not_mem_crepAssignedFreeVars_compileProg_return context value x
  | shMemLoad size kind name address =>
      cases kind with
      | global => simp [compileProg, crepAssignedFreeVars]
      | «local» =>
          apply not_mem_crepAssignedFreeVars_compileProg_shMemLoad_local
            context size name address x
          intro shape slots hlookup
          exact hslot name shape slots hlookup
  | shMemStore size address value =>
      exact not_mem_crepAssignedFreeVars_compileProg_shMemStore context size address value x
  | tick => exact not_mem_crepAssignedFreeVars_compileProg_tick context x
  | annot tag text => exact not_mem_crepAssignedFreeVars_compileProg_annot context tag text x

end Flapjack
