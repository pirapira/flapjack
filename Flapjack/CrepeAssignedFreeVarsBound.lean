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

/-- Assigned-memory bound invariant: every free variable of a compiled program
    at or below the context maximum is a slot of the context.  Cake
    `not_mem_context_assigned_mem_gt` (`pan_to_crepProofScript.sml:1252`) uses
    exactly this invariant, proved by `compile_ind`. -/
theorem crepAssignedFreeVars_compileProg_bound [BEq α] [OfNat α 0] [Add α]
    (program : Prog α) :
    ∀ (context : CompileContext α) (x : Nat),
      x ∈ crepAssignedFreeVars (compileProg context program) →
      x ≤ context.maxVar → CrepContextSlot context x := by
  induction program using prog_sizeOf_induction with
  | step program ih =>
    intro context x hxmem hbnd
    cases program with
    | skip => exact absurd hxmem (by simp [compileProg, crepAssignedFreeVars])
    | «break» => exact absurd hxmem (by simp [compileProg, crepAssignedFreeVars])
    | «continue» => exact absurd hxmem (by simp [compileProg, crepAssignedFreeVars])
    | tick => exact absurd hxmem (by simp [compileProg, crepAssignedFreeVars])
    | annot tag text => exact absurd hxmem (by simp [compileProg, crepAssignedFreeVars])
    | «return» value => exact absurd hxmem (by simp [compileProg, crepAssignedFreeVars])
    | store32 address value =>
        simp only [compileProg] at hxmem
        split at hxmem <;> exact absurd hxmem (by simp [crepAssignedFreeVars])
    | storeByte address value =>
        simp only [compileProg] at hxmem
        split at hxmem <;> exact absurd hxmem (by simp [crepAssignedFreeVars])
    | extCall function configuration configurationLength array arrayLength =>
        cases hc : firstCompiledExp context configuration with
        | none =>
            simp only [compileProg, hc] at hxmem
            exact absurd hxmem (by simp [crepAssignedFreeVars])
        | some configuration' =>
            cases hcl : firstCompiledExp context configurationLength with
            | none =>
                simp only [compileProg, hc, hcl] at hxmem
                exact absurd hxmem (by simp [crepAssignedFreeVars])
            | some configurationLength' =>
                cases ha : firstCompiledExp context array with
                | none =>
                    simp only [compileProg, hc, hcl, ha] at hxmem
                    exact absurd hxmem (by simp [crepAssignedFreeVars])
                | some array' =>
                    cases hal : firstCompiledExp context arrayLength with
                    | none =>
                        simp only [compileProg, hc, hcl, ha, hal] at hxmem
                        exact absurd hxmem (by simp [crepAssignedFreeVars])
                    | some arrayLength' =>
                        rw [compileProg_extCall_of_compiled context function configuration
                            configurationLength array arrayLength configuration'
                            configurationLength' array' arrayLength' hc hcl ha hal] at hxmem
                        rw [crepAssignedFreeVars_nestedDecs_append _ _ _ (by simp)] at hxmem
                        have hmem := (List.mem_filter.mp hxmem).1
                        simp only [crepAssignedFreeVars] at hmem
                        exact absurd hmem (by simp)
    | shMemStore size address value =>
        cases haddress : firstCompiledExpAnyShape context address with
        | none =>
            simp only [compileProg, haddress] at hxmem
            exact absurd hxmem (by simp [crepAssignedFreeVars])
        | some address' =>
            cases hvalue : firstCompiledExpAnyShape context value with
            | none =>
                simp only [compileProg, haddress, hvalue] at hxmem
                exact absurd hxmem (by simp [crepAssignedFreeVars])
            | some value' =>
                rw [compileProg_shMemStore_of_compiled context size address value address'
                    value' haddress hvalue] at hxmem
                rw [crepAssignedFreeVars_nestedDecs_append [maxCrepExpVar [address'] + 1] [value'] _
                    (by simp)] at hxmem
                obtain ⟨hmem1, hmem2⟩ := List.mem_filter.mp hxmem
                simp only [crepAssignedFreeVars] at hmem1
                exact absurd hmem1 (of_decide_eq_true hmem2)
    | seq first second =>
        simp only [compileProg, crepAssignedFreeVars, List.mem_append] at hxmem
        rcases hxmem with hxmem | hxmem
        · exact ih first (by simp +arith) context x hxmem hbnd
        · exact ih second (by simp +arith) context x hxmem hbnd
    | ite condition thenBranch elseBranch =>
        cases hcondition : compileExp context condition with
        | mk compiled shape =>
            cases compiled with
            | nil =>
                simp only [compileProg, hcondition] at hxmem
                exact absurd hxmem (by simp [crepAssignedFreeVars])
            | cons condition' rest =>
                rw [compileProg_ite_of_compiled context condition thenBranch elseBranch
                    condition' rest shape hcondition] at hxmem
                simp only [crepAssignedFreeVars, List.mem_append] at hxmem
                rcases hxmem with hxmem | hxmem
                · exact ih thenBranch (by simp +arith) context x hxmem hbnd
                · exact ih elseBranch (by simp +arith) context x hxmem hbnd
    | «while» condition body =>
        cases hcondition : compileExp context condition with
        | mk compiled shape =>
            cases compiled with
            | nil =>
                simp only [compileProg, hcondition] at hxmem
                exact absurd hxmem (by simp [crepAssignedFreeVars])
            | cons condition' rest =>
                rw [compileProg_while_of_compiled context condition body condition' rest
                    shape hcondition] at hxmem
                simp only [crepAssignedFreeVars] at hxmem
                exact ih body (by simp +arith) context x hxmem hbnd
    | assign kind name value =>
        cases kind with
        | «global» => exact absurd hxmem (by simp [compileProg, crepAssignedFreeVars])
        | «local» =>
            cases hlookup : lookupInfo name context.vars with
            | none =>
                simp only [compileProg, hlookup] at hxmem
                exact absurd hxmem (by simp [crepAssignedFreeVars])
            | some info =>
                obtain ⟨shape, names⟩ := info
                cases hvalue : compileExp context value with
                | mk expressions valueShape =>
                    rw [compileProg_assign_local_of_compiled context name value shape
                        valueShape names expressions hlookup hvalue] at hxmem
                    split at hxmem
                    · split at hxmem
                      · rw [crepAssignedFreeVars_nestedSeq_assign_zipWith names expressions
                            (by assumption)] at hxmem
                        exact ⟨name, shape, names, hlookup, hxmem⟩
                      · rw [crepAssignedFreeVars_nestedDecs_append
                            (freshNames context names.length 1) expressions _
                            (by rw [freshNames_length]; assumption)] at hxmem
                        have hmem := (List.mem_filter.mp hxmem).1
                        simp only [crepAssignedFreeVars_assignVar_zipWith names
                            (freshNames context names.length 1) (by rw [freshNames_length])] at hmem
                        exact ⟨name, shape, names, hlookup, hmem⟩
                    · exact absurd hxmem (by simp [crepAssignedFreeVars])
    | primitive name operator args =>
        cases hlookup : lookupInfo name context.vars with
        | none =>
            simp only [compileProg, hlookup] at hxmem
            exact absurd hxmem (by simp [crepAssignedFreeVars])
        | some info =>
            obtain ⟨shape, names⟩ := info
            rw [compileProg_primitive_of_compiled context name operator args shape names
                (compileArgs context args) hlookup rfl] at hxmem
            rw [crepAssignedFreeVars_nestedDecs_append
                (freshNames context (compileArgs context args).length 1)
                (compileArgs context args) _ (by rw [freshNames_length])] at hxmem
            have hmem := (List.mem_filter.mp hxmem).1
            simp only [crepAssignedFreeVars] at hmem
            exact ⟨name, shape, names, hlookup, hmem⟩
    | store address value =>
        cases haddress : compileExp context address with
        | mk addressCompiled addressShape =>
            cases hvalue : compileExp context value with
            | mk values valueShape =>
                cases addressCompiled with
                | nil =>
                    simp only [compileProg, haddress, hvalue] at hxmem
                    exact absurd hxmem (by simp [crepAssignedFreeVars])
                | cons address' addressRest =>
                    rw [compileProg_store_of_compiled context address value address'
                        addressRest addressShape values valueShape haddress hvalue] at hxmem
                    split at hxmem
                    · rw [crepAssignedFreeVars_nestedDecs_append _ _ _
                          (by simp [freshNames_length])] at hxmem
                      have hmem := (List.mem_filter.mp hxmem).1
                      rw [crepAssignedFreeVars_nestedSeq_stores] at hmem
                      exact absurd hmem (by simp)
                    · exact absurd hxmem (by simp [crepAssignedFreeVars])
    | dec name shape value body =>
        cases hvalue : compileExp context value with
        | mk expressions valueShape =>
            rw [compileProg_dec_of_compiled context name shape value body expressions
                valueShape hvalue] at hxmem
            split at hxmem
            · rename_i hlen
              have hmem := mem_crepAssignedFreeVars_nestedDecs
                  (allocatedNames context valueShape) expressions
                  (compileProg { context with
                    vars := (name, (valueShape, allocatedNames context valueShape)) :: context.vars,
                    maxVar := context.maxVar + Shape.shapeSize valueShape } body)
                  hlen hxmem
              exact crepContextSlot_cons_of_le context name valueShape
                (allocatedNames context valueShape)
                (fun y hy => allocatedNames_gt context valueShape hy) hbnd
                (ih body (by simp +arith)
                  { context with
                    vars := (name, (valueShape, allocatedNames context valueShape)) :: context.vars,
                    maxVar := context.maxVar + Shape.shapeSize valueShape } x hmem
                  (Nat.le_trans hbnd (Nat.le_add_right _ _)))
            · exact absurd hxmem (by simp [crepAssignedFreeVars])
    | decCall name shape function arguments body =>
        rw [compileProg_decCall context name shape function arguments body] at hxmem
        rw [crepAssignedFreeVars_nestedDecs_append (allocatedNames context shape)
            ((allocatedNames context shape).map (fun _ => (.const 0 : CrepExp α))) _
            (by simp [allocatedNames_length])] at hxmem
        have hmem := (List.mem_filter.mp hxmem).1
        simp only [crepAssignedFreeVars, List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact absurd (allocatedNames_gt context shape hmem) (by omega)
        · exact crepContextSlot_cons_of_le context name shape (allocatedNames context shape)
            (fun y hy => allocatedNames_gt context shape hy) hbnd
            (ih body (by simp +arith)
              { context with
                vars := (name, (shape, allocatedNames context shape)) :: context.vars,
                maxVar := context.maxVar + Shape.shapeSize shape } x hmem
              (Nat.le_trans hbnd (Nat.le_add_right _ _)))
    | raise exception value =>
        cases hexception : lookupInfo exception context.exceptions with
        | none =>
            simp only [compileProg, hexception] at hxmem
            exact absurd hxmem (by simp [crepAssignedFreeVars])
        | some code =>
            cases hvalue : compileExp context value with
            | mk expressions shape =>
                rw [compileProg_raise_of_compiled context exception value code expressions
                    shape hexception hvalue] at hxmem
                split at hxmem
                · simp only [crepAssignedFreeVars, List.mem_append] at hxmem
                  rcases hxmem with hxmem | hxmem
                  · rw [crepAssignedFreeVars_nestedDecs_append
                        (freshNames context expressions.length 1) expressions _
                        (by rw [freshNames_length])] at hxmem
                    have hmem := (List.mem_filter.mp hxmem).1
                    rw [crepAssignedFreeVars_nestedSeq_storeGlobals] at hmem
                    exact absurd hmem (by simp)
                  · exact absurd hxmem (by simp)
                · exact absurd hxmem (by simp [crepAssignedFreeVars])
    | shMemLoad size kind name address =>
        cases kind with
        | «global» =>
            simp only [compileProg] at hxmem
            exact absurd hxmem (by simp [crepAssignedFreeVars])
        | «local» =>
            cases hlookup : lookupInfo name context.vars with
            | none =>
                simp only [compileProg, hlookup] at hxmem
                exact absurd hxmem (by simp [crepAssignedFreeVars])
            | some info =>
                obtain ⟨shape, slots⟩ := info
                cases slots with
                | nil =>
                    simp only [compileProg, hlookup] at hxmem
                    exact absurd hxmem (by simp [crepAssignedFreeVars])
                | cons destination rest =>
                    cases haddress : firstCompiledExpAnyShape context address with
                    | none =>
                        simp only [compileProg, hlookup, haddress] at hxmem
                        exact absurd hxmem (by simp [crepAssignedFreeVars])
                    | some address' =>
                        rw [compileProg_shMemLoad_local_of_compiled context size name address
                            shape destination rest address' hlookup haddress] at hxmem
                        simp only [crepAssignedFreeVars, List.mem_cons, List.not_mem_nil,
                          or_false] at hxmem
                        exact ⟨name, shape, destination :: rest, hlookup, by simp [hxmem]⟩
    | call info function arguments =>
        cases info with
        | none => exact absurd hxmem (by simp [compileProg, crepAssignedFreeVars])
        | some infoData =>
            obtain ⟨destination, handler⟩ := infoData
            cases handler with
            | none =>
                cases destination with
                | none =>
                    simp only [compileProg] at hxmem
                    rw [crepAssignedFreeVars_nestedDecs_append (functionReturnNames context function)
                        ((functionReturnNames context function).map (fun _ => (.const 0 : CrepExp α))) _
                        (by simp)] at hxmem
                    have hmem := (List.mem_filter.mp hxmem).1
                    simp only [crepAssignedFreeVars] at hmem
                    exact absurd (functionReturnNames_bound context function x hmem) (by omega)
                | some destData =>
                    obtain ⟨kind, name⟩ := destData
                    cases hnames : callDestinationNames context kind name with
                    | none =>
                        simp only [compileProg, hnames] at hxmem
                        exact absurd hxmem (by simp [crepAssignedFreeVars])
                    | some names =>
                        rw [compileProg_call_destination_of_compiled context function arguments
                            kind name names (compileArgs context arguments) hnames rfl] at hxmem
                        obtain ⟨shape, slots, hlookup, hslots⟩ :=
                          callDestinationNames_some_slot context kind name names hnames
                        simp only [crepAssignedFreeVars] at hxmem
                        exact ⟨name, shape, slots, hlookup, by rw [← hslots]; exact hxmem⟩
            | some handlerData =>
                obtain ⟨exception, handlerVar, handlerProgram⟩ := handlerData
                cases hexception : lookupInfo exception context.exceptions with
                | none =>
                    cases destination with
                    | none =>
                        simp only [compileProg, hexception] at hxmem
                        rw [crepAssignedFreeVars_nestedDecs_append
                            (functionReturnNames context function)
                            ((functionReturnNames context function).map
                              (fun _ => (.const 0 : CrepExp α))) _ (by simp)] at hxmem
                        have hmem := (List.mem_filter.mp hxmem).1
                        simp only [crepAssignedFreeVars] at hmem
                        exact absurd (functionReturnNames_bound context function x hmem) (by omega)
                    | some destData =>
                        obtain ⟨kind, name⟩ := destData
                        cases hnames : callDestinationNames context kind name with
                        | none =>
                            simp only [compileProg, hexception, hnames] at hxmem
                            exact absurd hxmem (by simp [crepAssignedFreeVars])
                        | some names =>
                            simp only [compileProg, hexception, hnames] at hxmem
                            obtain ⟨shape, slots, hlookup, hslots⟩ :=
                              callDestinationNames_some_slot context kind name names hnames
                            simp only [crepAssignedFreeVars] at hxmem
                            exact ⟨name, shape, slots, hlookup, by rw [← hslots]; exact hxmem⟩
                | some code =>
                    cases hhandler : lookupInfo handlerVar context.vars with
                    | none =>
                        cases destination with
                        | none =>
                            simp only [compileProg, hexception, hhandler] at hxmem
                            rw [crepAssignedFreeVars_nestedDecs_append
                                (functionReturnNames context function)
                                ((functionReturnNames context function).map
                                  (fun _ => (.const 0 : CrepExp α))) _ (by simp)] at hxmem
                            have hmem := (List.mem_filter.mp hxmem).1
                            simp [crepAssignedFreeVars, List.mem_append] at hmem
                            rcases hmem with hmem | hmem
                            · exact absurd (functionReturnNames_bound context function x hmem) (by omega)
                            · exact ih handlerProgram (by simp +arith) context x hmem hbnd
                        | some destData =>
                            obtain ⟨kind, name⟩ := destData
                            cases hnames : callDestinationNames context kind name with
                            | none =>
                                simp only [compileProg, hexception, hhandler, hnames] at hxmem
                                simp [crepAssignedFreeVars] at hxmem
                                exact ih handlerProgram (by simp +arith) context x hxmem hbnd
                            | some names =>
                                simp only [compileProg, hexception, hhandler, hnames] at hxmem
                                simp [crepAssignedFreeVars, List.mem_append] at hxmem
                                obtain ⟨shape, slots, hlookup, hslots⟩ :=
                                  callDestinationNames_some_slot context kind name names hnames
                                rcases hxmem with hxmem | hxmem
                                · exact ⟨name, shape, slots, hlookup, by rw [← hslots]; exact hxmem⟩
                                · exact ih handlerProgram (by simp +arith) context x hxmem hbnd
                    | some handlerInfo =>
                        obtain ⟨hshape, handlerNames⟩ := handlerInfo
                        cases destination with
                        | none =>
                            simp only [compileProg, hexception, hhandler] at hxmem
                            rw [crepAssignedFreeVars_nestedDecs_append
                                (functionReturnNames context function)
                                ((functionReturnNames context function).map
                                  (fun _ => (.const 0 : CrepExp α))) _ (by simp)] at hxmem
                            have hmem := (List.mem_filter.mp hxmem).1
                            simp only [crepAssignedFreeVars,
                              crepAssignedFreeVars_seq_assignRet_compileProg, List.mem_append] at hmem
                            rcases hmem with hmem | hmem | hmem
                            · exact absurd (functionReturnNames_bound context function x hmem) (by omega)
                            · exact ⟨handlerVar, hshape, handlerNames, hhandler, hmem⟩
                            · exact ih handlerProgram (by simp +arith) context x hmem hbnd
                        | some destData =>
                            obtain ⟨kind, name⟩ := destData
                            cases hnames : callDestinationNames context kind name with
                            | none =>
                                simp only [compileProg, hexception, hhandler, hnames] at hxmem
                                simp [crepAssignedFreeVars,
                                  crepAssignedFreeVars_seq_assignRet_compileProg,
                                  List.mem_append] at hxmem
                                rcases hxmem with hxmem | hxmem
                                · exact ⟨handlerVar, hshape, handlerNames, hhandler, hxmem⟩
                                · exact ih handlerProgram (by simp +arith) context x hxmem hbnd
                            | some names =>
                                simp only [compileProg, hexception, hhandler, hnames] at hxmem
                                simp [crepAssignedFreeVars,
                                  crepAssignedFreeVars_seq_assignRet_compileProg,
                                  List.mem_append] at hxmem
                                obtain ⟨shape, slots, hlookup, hslots⟩ :=
                                  callDestinationNames_some_slot context kind name names hnames
                                rcases hxmem with hxmem | hxmem | hxmem
                                · exact ⟨name, shape, slots, hlookup, by rw [← hslots]; exact hxmem⟩
                                · exact ⟨handlerVar, hshape, handlerNames, hhandler, hxmem⟩
                                · exact ih handlerProgram (by simp +arith) context x hxmem hbnd

/-- Cake `not_mem_context_assigned_mem_gt` (`pan_to_crepProofScript.sml:1252`):
    under a bounded context whose slots all avoid `x`, no free variable of the
    compiled program equals `x`. -/
theorem not_mem_context_assigned_mem_gt [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (program : Prog α) (x : Nat)
    (_hmax : panValueCtxtMax context.maxVar context.vars)
    (hslot : panValueSlotBound x context.vars) (hbnd : x ≤ context.maxVar) :
    x ∉ crepAssignedFreeVars (compileProg context program) := by
  intro hmem
  obtain ⟨name, shape, slots, hlookup, hxslot⟩ :=
    crepAssignedFreeVars_compileProg_bound program context x hmem hbnd
  exact hslot name shape slots hlookup hxslot

end Flapjack
