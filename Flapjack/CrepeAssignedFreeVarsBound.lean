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
theorem mem_crepAssignedFreeVars_nestedDecs {α : Type} (names : List Nat)
    (values : List (CrepExp α)) (body : CrepProg α)
    (h : names.length = values.length) {x : Nat}
    (hmem : x ∈ crepAssignedFreeVars (nestedDecs names values body)) :
    x ∈ crepAssignedFreeVars body := by
  rw [crepAssignedFreeVars_nestedDecs_append names values body h] at hmem
  exact (List.mem_filter.mp hmem).1

end Flapjack
