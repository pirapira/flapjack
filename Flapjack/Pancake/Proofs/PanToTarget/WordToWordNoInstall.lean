import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSemantics

/-!
# `pan_to_targetProof`: `word_to_word_compile_no_install_no_alloc`

`word_to_word_compile_no_install_no_alloc`
(`cakeml/pancake/proofs/pan_to_targetProofScript.sml:909-938`): `word_to_word$compile`
keeps a code table free of `Install`, and of `Alloc` when the source is, for
`MustTerminate`-free sources with distinct names, as needed for the premises of
`word_to_word_compile_semantics` in `pan_to_target_compile_semantics`.
-/

namespace Flapjack.PanToTarget
open Flapjack Flapjack.WordProps Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord

/-- A code table related by `code_rel` to one without `Alloc`, with the same domain, has no
    `Alloc` (Flapjack infrastructure, the `Alloc` counterpart of `noInstallCode_of_codeRel`). -/
theorem noAllocCode_of_codeRel {width : Nat} [NeZero width]
    (code l : Spt (Nat × WordLangProgHOL (BitVec width))) (hrel : codeRel code l)
    (hdom : sptDomain code = sptDomain l) (hc : noAllocCode code) : noAllocCode l := by
  intro k n p hk
  have hm : (sptLookup k code).isSome = true := by
    have := congrFun hdom k
    simp only [sptDomain] at this
    rw [this, hk]
    rfl
  rcases hv : sptLookup k code with _ | ⟨ar, e⟩
  · rw [hv] at hm
    cases hm
  obtain ⟨col, t, kk, a, c, h⟩ := hrel k _ hv
  rw [hk] at h
  have hp : p = (compileSingle t kk a c ((k, ar, e), col)).2.2 := congrArg (·.2) (Option.some.inj h)
  have he := hc k ar e hv
  rw [hp]
  rw [noAllocSubprogsHOL_eq_notCreated] at he ⊢
  exact WordConvs.compile_single_not_created_subprogs _ t kk a c ((k, ar, e), col) he

/-- `word_to_word$compile` keeps the domain of the code table (Flapjack infrastructure for
    HOL's `domain_fromAList`/`MAP_ZIP` step). -/
theorem compile_sptDomain {width : Nat} [NeZero width] (wconf : Config)
    (aconf : AsmConfigExact width) (progs0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (col : List (Option (Spt Nat))) (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : compile wconf aconf progs0 = (col, progs)) :
    sptDomain (sptFromAList progs0) = sptDomain (sptFromAList progs) := by
  simp only [compile, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  funext n
  simp only [sptDomain, sptLookup_sptFromAList]
  rw [sptAListLookup_isSome_map_fullCompileSingle _ _ _ _ progs0 _ (compile_zip_length wconf progs0)]

/-- HOL `word_to_word_compile_no_install_no_alloc` (`pan_to_targetProofScript.sml:909-938`);
    HOL's free `wconf aconf progs0 col progs` are explicit and `ALL_DISTINCT (MAP FST progs0)`
    is `List.Nodup`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_to_word_compile_no_install_no_alloc"
  (words_as_type_indexed_bitvec)]
theorem word_to_word_compile_no_install_no_alloc {width : Nat} [NeZero width] (wconf : Config)
    (aconf : AsmConfigExact width) (progs0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (col : List (Option (Spt Nat))) (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    compile wconf aconf progs0 = (col, progs) ∧ (progs0.map Prod.fst).Nodup ∧
      noMtCode (sptFromAList progs0) ∧ noInstallCode (sptFromAList progs0) →
    noInstallCode (sptFromAList progs) ∧
      (noAllocCode (sptFromAList progs0) → noAllocCode (sptFromAList progs)) := by
  rintro ⟨hcomp, -, hmt, hni⟩
  have hrel := no_mt_code_rel_ext _ _ ⟨hmt, code_rel_ext_word_to_word aconf progs0 wconf col progs hcomp⟩
  have hdom := compile_sptDomain wconf aconf progs0 col progs hcomp
  exact ⟨noInstallCode_of_codeRel _ _ hrel hdom hni, noAllocCode_of_codeRel _ _ hrel hdom⟩

end Flapjack.PanToTarget
