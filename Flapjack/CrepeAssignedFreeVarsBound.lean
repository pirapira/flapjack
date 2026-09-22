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

end Flapjack
