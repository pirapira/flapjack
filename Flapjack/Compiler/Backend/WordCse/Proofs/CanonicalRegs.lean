import Flapjack.Compiler.Backend.WordCse.Proofs.SemanticInvariant
import Flapjack.Compiler.Backend.WordCse.RegisterData

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact

namespace CanonicalRegsCarrier

/-- Same owning-state canonical roundtrip as the complete input invariant. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CanonicalRegsCarrier

/-! Original register-value lemmas use the full data_inv premise over the
faithful state. Its declaration closure retains the imported evaluator's
existing IEEE real-rendering assumption (docs/SOUNDNESS.md item 8), recorded
in the manifest; no additional theorem hypothesis is introduced. -/

/-- Original canonical-register get_var equality, including a missing binding's
default register, for arbitrary native knowledge and faithful WordSem state. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem canonicalRegsCorrect {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (register : Nat) (state : WordSemStateFiniteExact width C F)
    (valid : dataInv data state) :
    getVar (canonicalRegs data register) state = getVar register state := by
  cases observed : sptLookup register data.toCanonical with
  | none => simp [canonicalRegs, observed]
  | some value =>
      have aliases := valid.2.1 register value observed
      simpa [canonicalRegs, observed] using aliases.symm

/-- Original avoid-register variant, with no inequality or successful lookup
premise: both the avoid branch and ordinary canonical branch retain get_var. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs'_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem canonicalRegsAvoidCorrect {width : Nat} [NeZero width] {C : Type} {F : Type}
    (avoid : Nat) (data : Knowledge) (register : Nat) (state : WordSemStateFiniteExact width C F)
    (valid : dataInv data state) :
    getVar (canonicalRegs' avoid data register) state = getVar register state := by
  change getVar (if canonicalRegs data register = avoid then register
    else canonicalRegs data register) state = getVar register state
  split
  · rfl
  · exact canonicalRegsCorrect data register state valid

/-- Original direct sparse-local lookup equality; this retains complete
word_loc results, including locations and absent values, without a Word premise. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs_correct_bis"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem canonicalRegsCorrectBis {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (register : Nat) (state : WordSemStateFiniteExact width C F)
    (valid : dataInv data state) :
    sptLookup (canonicalRegs data register) state.locals = sptLookup register state.locals := by
  exact canonicalRegsCorrect data register state valid

end Flapjack.Compiler.Backend.WordCse
