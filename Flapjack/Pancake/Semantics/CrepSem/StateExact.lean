import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# Exact HOL `crepSem$state` helpers over the finite-support carrier

The raw `CrepHolState` (`Flapjack/Pancake/Semantics/CrepSem.lean`) stores
`locals`/`code` as unrestricted lookup functions, a strict superset of HOL's
finite maps, so its state-helper tags were withdrawn in the
`flapjack-pxn.18.3.7.1.3.1.1.3` audit. This module restates the state helpers
over `CrepSemHOLState`, whose `locals`/`globals`/`code` fields are
`HolFiniteMapExact` (finite support by type), so the whole-state quantification
matches HOL `('a,'ffi) crepSem$state`.

The word index is the canonical positive `BitVec width` model for a HOL word
dimension, the same representation used by the accepted `word_lab`/`crepLang$prog`
(`HolWordLab width`, `CrepProgHOL width`) ports. Statements are clause-for-clause
HOL; only the word dimension is represented by its positive cardinality.

This first slice covers the helpers that do not need finite-map operations:
`dec_clock_def`, `fix_clock_def`, `fix_clock_IMP_LESS_EQ`, and `mem_load_def`.
The update helpers (`set_var`, `set_globals`, `upd_locals`, `empty_locals`,
`res_var`) need `FUPDATE`/`FEMPTY`/`FUPDATE_LIST` on `HolFiniteMapExact` and are
tracked as follow-up slices of `flapjack-pxn.18.3.7.1.3.1.1.3.1`.

The four helpers below are **temporarily untagged**. Their finite-map
representation (`HolFiniteMapExact` fields on `CrepSemHOLState`) must be
recorded with the `@[hol]` qualifier `(fmap_as_finite_support := [locals,
globals, code])` rather than a bare tag, per the standard-translation rule. That
qualifier, its canonical witness `holFmapAsFiniteSupportWitness`, and the
`reviewed_fmap_as_finite_support` manifest status are being added under bead
`flapjack-pxn.18.3.7.1.3.1.1.2.4` (ds3 commits `01dae7ba5`/`bcca041b5`, not yet
in the integration branch). Each helper is still reviewed case-by-case for
statement/side conditions and must be re-tagged with the qualifier only after
that checker accepts it; until then no exact claim is made here.

References: `cakeml/pancake/semantics/crepSemScript.sml:48-51` (mem_load_def),
`:145-148` (dec_clock_def), `:150-152` (fix_clock_def), `:155-158`
(fix_clock_IMP_LESS_EQ). Direct HOL rows reproduced below live in
`scripts/hol-probes/crep_mem_load_probe.out`, `crep_fix_clock_probe.out`, and
`crep_dec_clock_simp_probe.out`.
-/

namespace Flapjack

/-- Port of HOL `dec_clock_def` (`crepSemScript.sml:145-148`) over the
    finite-support `CrepSemHOLState` carrier. Untagged pending the
    `fmap_as_finite_support` qualifier (`flapjack-pxn.18.3.7.1.3.1.1.2.4`). -/
def decClockCrepSemHOL {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  { state with clock := state.clock - 1 }

/-- Port of HOL `fix_clock_def` (`crepSemScript.sml:150-152`) over the
    finite-support `CrepSemHOLState` carrier. The result is polymorphic in the
    unconstrained `res` component, as in HOL. Untagged pending the
    `fmap_as_finite_support` qualifier (`flapjack-pxn.18.3.7.1.3.1.1.2.4`). -/
def fixClockCrepSemHOL {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (oldState : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ) :
    β × CrepSemHOLState width σ :=
  (step.1, { step.2 with
    clock := if oldState.clock < step.2.clock then oldState.clock else step.2.clock })

/-- Port of HOL `fix_clock_IMP_LESS_EQ` (`crepSemScript.sml:155-158`):
    `fix_clock` never increases the clock. Untagged pending the
    `fmap_as_finite_support` qualifier (`flapjack-pxn.18.3.7.1.3.1.1.2.4`). -/
theorem fixClockCrepSemHOL_IMP_LESS_EQ {width : Nat} [NeZero width] {σ : Type}
    {β : Type} (state : CrepSemHOLState width σ) (x : β × CrepSemHOLState width σ)
    (res : β) (s1 : CrepSemHOLState width σ)
    (h : fixClockCrepSemHOL state x = (res, s1)) : s1.clock ≤ state.clock := by
  obtain ⟨value, stepState⟩ := x
  simp only [fixClockCrepSemHOL, Prod.mk.injEq] at h
  obtain ⟨_, hstate⟩ := h
  subst hstate
  change (if state.clock < stepState.clock then state.clock else stepState.clock) ≤
    state.clock
  split <;> omega

/-- Port of HOL `mem_load_def` (`crepSemScript.sml:48-51`) over the
    finite-support `CrepSemHOLState` carrier: a total `word → word_lab` memory
    guarded by the `memaddrs` set. Untagged pending the
    `fmap_as_finite_support` qualifier (`flapjack-pxn.18.3.7.1.3.1.1.2.4`). -/
def memLoadCrepSemHOL {width : Nat} [NeZero width] {σ : Type}
    (address : BitVec width) (state : CrepSemHOLState width σ)
    [DecidablePred state.memaddrs] :
    Option (HolWordLab width) :=
  if state.memaddrs address then some (state.memory address) else none

end Flapjack
