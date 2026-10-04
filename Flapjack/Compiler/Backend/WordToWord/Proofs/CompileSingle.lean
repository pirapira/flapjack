import Flapjack.Compiler.Backend.WordToWord.Compile
import Flapjack.Compiler.Backend.WordAlloc.Proofs.WordAllocCorrect
import Flapjack.Compiler.Backend.WordAlloc.Proofs.FullSSACorrect
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.MaxVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.DistinctTarReg
import Flapjack.Compiler.Backend.WordSimp.Proofs.CompileExp
import Flapjack.Compiler.Backend.WordInst.Proofs.InstSelect
import Flapjack.Compiler.Backend.WordInst.Proofs.ThreeToTwo
import Flapjack.Compiler.Backend.WordCopy.Proofs.Correct
import Flapjack.Compiler.Backend.WordUnreach.Proofs
import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect
import Flapjack.Compiler.Backend.WordCse.Proofs.Conventions
import Flapjack.Pancake.Proofs.WordConvs.RemoveDead
import Flapjack.Pancake.Proofs.WordConvs.InstSelectProgram
import Flapjack.Pancake.Proofs.WordConvs.ThreeToTwo
import Flapjack.Pancake.Proofs.WordConvs.Unreach
import Flapjack.Pancake.Proofs.WordConvs.WordCse
import Flapjack.Pancake.Proofs.WordConvs.CopyProp
import Flapjack.Pancake.Proofs.WordConvs.SSAWfCutsets

/-!
# `word_to_wordProof`: one function through the wordLang passes

`FST_compile_single` and `compile_single_lem` of
`cakeml/compiler/backend/proofs/word_to_wordProofScript.sml` (25-157):
`compile_single_lem` chains the tagged correctness theorems of every pass
composed by `compile_single`, discharging their syntactic side conditions with
the tagged convention theorems, exactly as HOL does.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

namespace CompileSingleCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileSingleCarrier

/-- HOL `FST_compile_single` (`word_to_wordProofScript.sml:25-29`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "FST_compile_single"
  (words_as_type_indexed_bitvec)]
theorem FST_compile_single {width : Nat} [NeZero width] (a : Bool) (b c : Nat)
    (d : AsmConfigExact width)
    (e : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    (compileSingle a b c d e).1 = e.1.1 := by
  rcases e with ⟨⟨n, m, p⟩, col⟩
  rfl

section Helpers

variable {width : Nat} [NeZero width] {C F : Type}

/-- The width-general executed `distinctTarReg` agrees with the reviewed
    `distinct_tar_reg` read through `HolInst.ofWordLangInst` (Flapjack
    infrastructure). -/
theorem distinctTarReg_ofWordLangInst (i : WordLangInst (BitVec width)) :
    distinctTarRegExact (HolInst.ofWordLangInst i) = distinctTarReg i := by
  rcases i with _ | _ | a | _ | _
  all_goals try rfl
  cases a with
  | binop _ _ _ ri => cases ri <;> rfl
  | shift _ _ _ ri => cases ri <;> rfl
  | _ => rfl

theorem everyInst_distinctTarReg_exact (p : WordLangProgHOL (BitVec width))
    (h : everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) p = true) :
    everyInst distinctTarReg p = true := by
  have : (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) =
      (distinctTarReg : WordLangInst (BitVec width) → Bool) :=
    funext distinctTarReg_ofWordLangInst
  rwa [this] at h

theorem wordStateEqRel_trans {s t u : WordSemStateFiniteExact width C F}
    (h1 : WordAlloc.wordStateEqRel s t) (h2 : WordAlloc.wordStateEqRel t u) :
    WordAlloc.wordStateEqRel s u := by
  simp_all only [WordAlloc.wordStateEqRel, and_self]

theorem wordStateEqRel_locals (s : WordSemStateFiniteExact width C F) (l : Spt (WordLocW width)) :
    WordAlloc.wordStateEqRel s { s with locals := l } := by
  simp only [WordAlloc.wordStateEqRel, and_self]

theorem evenStartingLocals_of_domain (l : Spt (WordLocW width)) (n : Nat)
    (h : sptDomain l = (fun key => key ∈ WordAlloc.evenList n)) :
    Compiler.Backend.WordAlloc.Proofs.evenStartingLocals l := by
  intro key hk
  rw [h] at hk
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hk
  simp [isPhyVar]

open Classical in
/-- `full_ssa_cc_trans_correct` with the permuted source state written directly
    (Flapjack restatement; definitionally the tagged theorem). -/
theorem ssa_step (p : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
    (perm1 : Nat → Nat → Nat) (n : Nat)
    (hdom : sptDomain st.locals = (fun key => key ∈ Compiler.Backend.WordAlloc.evenList n)) :
    ∃ perm2 : Nat → Nat → Nat,
      if (evaluate p { st with permute := perm2 }).1 = some .error then True else
        (evaluate p { st with permute := perm2 }).1 =
            (evaluate (Compiler.Backend.WordAlloc.fullSsaCcTrans n p) { st with permute := perm1 }).1 ∧
          WordAlloc.wordStateEqRel (evaluate p { st with permute := perm2 }).2
            (evaluate (Compiler.Backend.WordAlloc.fullSsaCcTrans n p) { st with permute := perm1 }).2 ∧
          match (evaluate p { st with permute := perm2 }).1 with
          | none => True
          | some (.break _) => True
          | some (.continue _) => True
          | some _ => (evaluate p { st with permute := perm2 }).2.locals =
              (evaluate (Compiler.Backend.WordAlloc.fullSsaCcTrans n p) { st with permute := perm1 }).2.locals := by
  obtain ⟨perm2, h⟩ := Compiler.Backend.WordAlloc.fullSsaCcTransCorrect p { st with permute := perm1 } n hdom
  exact ⟨perm2, h⟩

end Helpers

open Classical in
/-- HOL `compile_single_lem` (`word_to_wordProofScript.sml:32-157`): a
function body compiled by `compile_single` reproduces every non-error run of
the source from some permutation oracle, up to `word_state_eq_rel`, with equal
locals on a returning or raising result. HOL's free `t k a c name col` are the
leading binders; `if res = SOME Error` is decided classically, as in the
accepted `word_alloc_correct`. The proof chains the tagged pass theorems in
HOL's order. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_lem"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_lem {width : Nat} [NeZero width] {C F : Type} (t : Bool) (k a : Nat)
    (c : AsmConfigExact width) (name : Nat) (col : Option (Spt Nat)) :
    ∀ (prog : WordLangProgHOL (BitVec width)) (n : Nat) (st : WordSemStateFiniteExact width C F),
      sptDomain st.locals = (fun key => key ∈ Compiler.Backend.WordAlloc.evenList n) ∧
        Compiler.Backend.WordSimp.gcFunConstOk st.gcFun →
      ∃ perm' : Nat → Nat → Nat,
        let (res, rst) := evaluate prog { st with permute := perm' }
        let (_, _, cprog) := compileSingle t k a c ((name, n, prog), col)
        if res = some .error then True
        else
          let (res', rcst) := evaluate cprog st
          res = res' ∧ WordAlloc.wordStateEqRel rst rcst ∧
            match res with
            | none => True
            | some (.break _) => True
            | some (.continue _) => True
            | some _ => rst.locals = rcst.locals := by
  intro prog n st ⟨hdom, hgc⟩
  -- the pass pipeline of `compile_single`
  let p0 := WordSimp.compileExp prog
  let p1 := WordInst.instSelect c (maxVarHOL p0 + 1) p0
  let p2 := Compiler.Backend.WordAlloc.fullSsaCcTrans n p1
  let p3 := WordAlloc.removeDeadProg p2
  let p4 := WordCopy.copyProp (WordCse.wordCommonSubexpElim p3)
  let p5 := WordInst.threeToTwoRegProg t p4
  let p6 := WordUnreach.removeUnreach p5
  let p7 := WordAlloc.removeDeadProg p6
  have hcs : compileSingle t k a c ((name, n, prog), col) =
      (name, n, WordAlloc.wordAlloc name c a k p7 col) := rfl
  -- syntactic side conditions, as in HOL
  have flat2 : flatExpConventions p2 = true :=
    WordAlloc.fullSsaCcTrans_flatExpConventions p1 n (WordConvs.instSelect_flatExpConventions _ _ _)
  have flat3 : flatExpConventions p3 = true := (WordConvs.removeDeadProgConventions
    (fun _ => true) p2 c).1 flat2
  have flat6 : flatExpConventions p6 = true :=
    WordConvs.flatExpConventions_removeUnreach _
      (WordConvs.threeToTwoRegProg_flatExpConventions _ _
        (WordConvs.flat_exp_conventions_copy_prop _
          (WordConvs.flat_exp_conventions_word_common_subexp_elim _ flat3)))
  have wf7 : wfCutsets p7 :=
    (WordConvs.removeDeadProgConventions (fun _ => true) p6 c).2.2.2.2.1
      (WordConvs.wfCutsets_removeUnreach _
        (WordConvs.threeToTwoRegProg_wfCutsets _ _
          (WordConvs.wf_cutsets_copy_prop _
            (WordConvs.wf_cutsets_word_common_subexp_elim _
              ((WordConvs.removeDeadProgConventions (fun _ => true) p2 c).2.2.2.2.1
                (WordAlloc.fullSsaCcTrans_wfCutsets n p1))))))
  have dist4 : everyInst distinctTarReg p4 = true :=
    everyInst_distinctTarReg_exact _
      (WordConvs.every_inst_distinct_tar_reg_copy_prop _
        (WordCse.every_inst_distinct_tar_reg_word_common_subexp_elim _
          ((WordConvs.removeDeadProgConventions _ p2 c).2.2.2.1
            (WordAlloc.fullSsaCcTrans_distinctTarReg n p1))))
  -- word_alloc
  obtain ⟨perm1, hA⟩ := WordAlloc.wordAllocCorrect name c a p7 k col st
    ⟨evenStartingLocals_of_domain _ _ hdom, wf7⟩
  -- SSA
  obtain ⟨perm2, hS⟩ := ssa_step p1 st perm1 n hdom
  refine ⟨perm2, ?_⟩
  rcases hrun : evaluate prog { st with permute := perm2 } with ⟨res, rst⟩
  rw [hcs]
  dsimp only
  split
  · trivial
  rename_i herr
  -- word_simp
  have e0 : evaluate p0 { st with permute := perm2 } = (res, rst) :=
    compile_exp_thm prog _ _ res ⟨hrun, herr, hgc⟩
  -- inst_select
  have hb : everyVarHOL (fun x => decide (x < maxVarHOL p0 + 1)) p0 = true :=
    everyVarMono _ p0 _ ⟨fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega,
      Compiler.Backend.WordAlloc.maxVarMax p0⟩
  obtain ⟨loc1, e1, hl1⟩ := WordInst.inst_select_thm c (maxVarHOL p0 + 1) p0
    { st with permute := perm2 } res rst st.locals ⟨e0, hb, herr, fun _ _ => rfl⟩
  have e1' : evaluate p1 { st with permute := perm2 } = (res, { rst with locals := loc1 }) := e1
  -- SSA result
  rw [e1'] at hS
  simp only [herr, if_false] at hS
  obtain ⟨hres2, heq2, hloc2⟩ := hS
  rcases e2 : evaluate p2 { st with permute := perm1 } with ⟨res2, rst2⟩
  rw [e2] at hres2 heq2 hloc2
  simp only at hres2 heq2 hloc2
  subst hres2
  -- first remove_dead
  obtain ⟨t3, e3, hl3⟩ := WordAlloc.evaluateRemoveDeadProg p2 _ rst2 res ⟨flat2, e2, herr⟩
  -- word_cse, copy_prop, three_to_two, remove_unreach
  have e3' : evaluate (WordCse.wordCommonSubexpElim p3) { st with permute := perm1 } =
      (res, { rst2 with locals := t3 }) :=
    WordCse.word_common_subexp_elim_correct p3 _ res _ ⟨e3, flat3, herr⟩
  have e4 : evaluate p4 { st with permute := perm1 } = (res, { rst2 with locals := t3 }) := by
    rw [show p4 = WordCopy.copyProp (WordCse.wordCommonSubexpElim p3) from rfl,
      WordCopy.evaluateCopyProp (by rw [e3']; exact herr), e3']
  have e5 : evaluate p5 { st with permute := perm1 } = (res, { rst2 with locals := t3 }) :=
    WordInst.evaluate_three_to_two_reg_prog p4 _ res _ t ⟨e4, herr, dist4⟩
  have e6 : evaluate p6 { st with permute := perm1 } = (res, { rst2 with locals := t3 }) :=
    WordUnreach.evaluateRemoveUnreach p5 _ res _ ⟨e5, herr⟩
  -- second remove_dead
  obtain ⟨t7, e7, hl7⟩ := WordAlloc.evaluateRemoveDeadProg p6 _ _ res ⟨flat6, e6, herr⟩
  -- word_alloc result
  rw [e7] at hA
  simp only [herr, if_false] at hA
  rcases e8 : evaluate (WordAlloc.wordAlloc name c a k p7 col) st with ⟨res', rcst⟩
  rw [e8] at hA
  obtain ⟨hres', heq', hloc'⟩ := hA
  subst hres'
  refine ⟨rfl, ?_, ?_⟩
  · refine wordStateEqRel_trans (wordStateEqRel_locals rst loc1) (wordStateEqRel_trans heq2 ?_)
    refine wordStateEqRel_trans (wordStateEqRel_locals rst2 t3) ?_
    exact wordStateEqRel_trans (wordStateEqRel_locals _ t7) heq'
  · rcases res with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp_all

end Flapjack.Compiler.Backend.WordToWord
