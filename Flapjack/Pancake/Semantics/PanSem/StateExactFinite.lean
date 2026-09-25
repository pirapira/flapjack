import Flapjack.Pancake.Semantics.PanSem.StateExact
import Flapjack.Pancake.Semantics.PanSem.LocalUpdatesExact
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# Finite-support refinement of the exact source-state carrier

`PanSemStateExact` (`StateExact.lean`) stores `locals`, `globals`, `code`, and
`eshapes` as unrestricted lookup functions `MlS → Option _`, whereas the HOL
`panSem$state` datatype (`cakeml/pancake/semantics/panSemScript.sml:44-62`)
stores them as finite maps (`|->`). The unrestricted functions form a strict
superset: they admit lookups with infinite support, which no HOL finite map can
have.

This file adds the field-wise finite-support prerequisite needed before the
`pan_to_crep$state_rel_def` projections can be stated exactly, and records the
classification of the existing `@[hol]` definitions in `StateExact.lean` /
`LocalUpdatesExact.lean` that currently quantify the broader carrier:

* `decClockHOLExact` / `fixClockHOLExact` only write `clock`, so their
  equations are faithful but their quantified carrier is broader than HOL's
  finite-map state; retarget to `FiniteSupport` (or an exact finite-map state)
  is tracked by bead `flapjack-pxn.18.3.7.1.3.1.1` before the parent
  `state_rel_def` can be tagged.
* `emptyLocalsHOLExact` sets `locals` to the empty map, which is exactly HOL
  `FEMPTY`, so it stays inside the finite-support subclass (proved below).
* `lookupKvarHOLExact` / `setKvarHOLExact` read and update `locals`/`globals`,
  which HOL performs with finite-map `FLOOKUP`/`FUPDATE`; their equations match
  but the unrestricted carrier again admits non-HOL states.

The reused `HolFiniteMapExact` carrier (`CrepSem/HOLState.lean`) is the
established finite-support representation with an explicit support witness; its
`finiteSupport` projection is the kernel-checked field representation.
None of the declarations in this file carry `@[hol]` tags: the finite-support
refinement is Flapjack representation infrastructure pending the coordinator's
retargeting decision for the five existing tags.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Field-wise finite support of the exact source-state carrier: each
    `MlS`-keyed map field has a finite list of keys covering every defined
    lookup, matching the HOL `|->` fields of `panSem$state`. -/
def PanSemStateExact.FiniteSupport {width : Nat} [NeZero width]
    (state : PanSemStateExact width σ) : Prop :=
  (∃ keys : List MlS, ∀ key, state.locals key ≠ none → key ∈ keys) ∧
  (∃ keys : List MlS, ∀ key, state.globals key ≠ none → key ∈ keys) ∧
  (∃ keys : List MlS, ∀ key, state.code key ≠ none → key ∈ keys) ∧
  (∃ keys : List MlS, ∀ key, state.eshapes key ≠ none → key ∈ keys)

/-- Kernel-checked finite-support projection of the reused HOL finite-map
    carrier: a `HolFiniteMapExact` exposes a support list for its lookup. -/
theorem HolFiniteMapExact.lookup_finiteSupport {α β : Type}
    (map : HolFiniteMapExact α β) :
    ∃ keys : List α, ∀ key, map.lookup key ≠ none → key ∈ keys :=
  map.finiteSupport

/-- Clearing the locals of a finite-support state keeps every map field
    finite-support (HOL `empty_locals` writes `FEMPTY` to `locals`). -/
theorem PanSemStateExact.finiteSupport_emptyLocals {width : Nat} [NeZero width]
    {σ : Type} {state : PanSemStateExact width σ} (h : state.FiniteSupport) :
    (emptyLocalsHOLExact state).FiniteSupport := by
  obtain ⟨_, hg, hc, he⟩ := h
  refine ⟨⟨[], ?_⟩, hg, hc, he⟩
  intro key hk
  simp [emptyLocalsHOLExact] at hk

/-- A single local update (HOL `set_var`) keeps finite support: the new key is
    added to the support list, all other keys are unchanged. -/
theorem PanSemStateExact.finiteSupport_setVar {width : Nat} [NeZero width]
    {σ : Type} {state : PanSemStateExact width σ} (h : state.FiniteSupport)
    (name : MlS) (value : ValueHOL width) :
    (setVarHOLExact name value state).FiniteSupport := by
  obtain ⟨⟨lkeys, hl⟩, hg, hc, he⟩ := h
  refine ⟨⟨name :: lkeys, ?_⟩, hg, hc, he⟩
  intro key hk
  simp only [setVarHOLExact] at hk
  by_cases hname : key = name
  · subst hname
    exact List.mem_cons_self
  · simp only [if_neg hname] at hk
    exact List.mem_cons_of_mem name (hl key hk)

/-- A single global update (HOL `set_global`) keeps finite support. -/
theorem PanSemStateExact.finiteSupport_setGlobal {width : Nat} [NeZero width]
    {σ : Type} {state : PanSemStateExact width σ} (h : state.FiniteSupport)
    (name : MlS) (value : ValueHOL width) :
    (setGlobalHOLExact name value state).FiniteSupport := by
  obtain ⟨hl, ⟨gkeys, hg⟩, hc, he⟩ := h
  refine ⟨hl, ⟨name :: gkeys, ?_⟩, hc, he⟩
  intro key hk
  simp only [setGlobalHOLExact] at hk
  by_cases hname : key = name
  · subst hname
    exact List.mem_cons_self
  · simp only [if_neg hname] at hk
    exact List.mem_cons_of_mem name (hg key hk)

/-- The kind-dependent update (HOL `set_kvar`) keeps finite support in both
    branches. -/
theorem PanSemStateExact.finiteSupport_setKvar {width : Nat} [NeZero width]
    {σ : Type} {state : PanSemStateExact width σ} (h : state.FiniteSupport)
    (kind : VarKind) (name : MlS) (value : ValueHOL width) :
    (setKvarHOLExact kind name value state).FiniteSupport := by
  unfold setKvarHOLExact
  split
  · exact PanSemStateExact.finiteSupport_setVar (state := state) h name value
  · exact PanSemStateExact.finiteSupport_setGlobal (state := state) h name value

end Flapjack
