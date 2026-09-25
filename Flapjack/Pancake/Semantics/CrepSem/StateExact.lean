import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# Exact HOL `crepSem$state` helpers over the finite-support carrier

The four helpers `decClockCrepSemHOL`, `fixClockCrepSemHOL`,
`fixClockCrepSemHOL_IMP_LESS_EQ`, and `memLoadCrepSemHOL` live in
`Flapjack/Pancake/Semantics/CrepSem/HOLState.lean`, the module that declares the
owning `CrepSemHOLState` structure, its exact `HolFiniteMapExact` fields, and the
canonical `CrepSemHOLState.holFmapAsFiniteSupportWitness`. The AGENTS/checker
finite-map qualifier requires a tagged declaration and its roundtrip witness to
be in the same module as the owning structure, so this module is now an
import-only re-export that keeps the original import paths working.

The four helpers are tagged `reviewed_fmap_as_finite_support` in
`HOLState.lean` under the qualifier
`(fmap_as_finite_support := [locals, globals, code])`; referring to
`Flapjack.Pancake.Semantics.CrepSem.StateExact` still brings the names into
scope through the import.

References: `cakeml/pancake/semantics/crepSemScript.sml:48-51` (`mem_load_def`),
`:145-148` (`dec_clock_def`), `:150-152` (`fix_clock_def`), `:155-158`
(`fix_clock_IMP_LESS_EQ`).
-/
