import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Leaf
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

/-!
# `word_to_wordProof` `compile_single_correct`: control cases

The `MustTerminate`, `Seq`, `If` and `Loop` `Resume` cases of HOL
`compile_single_correct` (`word_to_wordProofScript.sml:328-341, 592-748`). HOL
proves the theorem by complete induction on `termdep`, then `clock`, then
`prog_size`; each case piece here takes HOL's `termdep`/`clock` induction
hypothesis (`CompileSingleCorrectLowerIH`) and, for the size component, the
induction hypothesis of its immediate sub-programs at the same `termdep` and
`clock` (`CompileSingleCorrectSubIH`).
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

namespace CompileSingleCorrectControlCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileSingleCorrectControlCarrier

/-- HOL's outer induction hypotheses of `compile_single_correct`: every
    program at a state with smaller `termdep`, or equal `termdep` and smaller
    `clock` (Flapjack infrastructure naming them). -/
def CompileSingleCorrectLowerIH {width : Nat} [NeZero width] {C F : Type} (tt : Bool) (kk aa : Nat)
    (co : AsmConfigExact width) (st : WordSemStateFiniteExact width C F) : Prop :=
  ∀ (prog : WordLangProgHOL (BitVec width)) (st' : WordSemStateFiniteExact width C F),
    st'.termdep < st.termdep ∨ (st'.termdep = st.termdep ∧ st'.clock < st.clock) →
      CompileSingleCorrectAt tt kk aa co prog st'

/-- HOL's `prog_size` induction hypothesis for one immediate sub-program, at
    the same `termdep` and `clock` (Flapjack infrastructure naming it). -/
def CompileSingleCorrectSubIH {width : Nat} [NeZero width] {C F : Type} (tt : Bool) (kk aa : Nat)
    (co : AsmConfigExact width) (sub : WordLangProgHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) : Prop :=
  ∀ st' : WordSemStateFiniteExact width C F, st'.termdep = st.termdep → st'.clock = st.clock →
    CompileSingleCorrectAt tt kk aa co sub st'

open Classical in
/-- The `MustTerminate` clause of `evaluate` on a computed inner run
    (Flapjack infrastructure). -/
theorem evaluate_mustTerminate_run {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (h0 : ¬s.termdep = 0) (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
    (hA : evaluate p
      { s with
        clock := wordSemMustTerminateLimit width
        termdep := s.termdep - 1 } = (res, s1)) :
    evaluate (.mustTerminate p) s =
      if res = some .timeOut then (some .error, s)
      else (res, { s1 with clock := s.clock, termdep := s.termdep }) := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht, if_neg h0]
  simp only [hA]
  split <;> simp_all

open Classical in
/-- HOL `compile_single_correct`, `MustTerminate` case (`word_to_wordProofScript.sml:328-341`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_MustTerminate {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) (ih : CompileSingleCorrectLowerIH tt kk aa co st) :
    CompileSingleCorrectAt tt kk aa co (.mustTerminate p) st := by
  rintro l coracle cc ⟨hrel, hdom, hcomp, hco, hgc⟩
  by_cases h0 : st.termdep = 0
  · refine ⟨st.permute, ?_⟩
    rw [evaluate]
    simp [h0]
  let st' : WordSemStateFiniteExact width C F :=
    { st with
      clock := wordSemMustTerminateLimit width
      termdep := st.termdep - 1 }
  obtain ⟨perm', H⟩ := ih p st' (Or.inl (by simp [st']; omega)) l coracle cc
    ⟨hrel, hdom, hcomp, hco, hgc⟩
  refine ⟨perm', ?_⟩
  rcases hA : evaluate p { st' with permute := perm' } with ⟨res, s1⟩
  rw [hA] at H
  dsimp only at H
  rcases hB : evaluate p { st' with code := l, compileOracle := coracle, compile := cc } with ⟨res1, s2⟩
  rw [hB] at H
  dsimp only at H
  have e1 := evaluate_mustTerminate_run p { st with permute := perm' } h0 res s1 hA
  have e2 := evaluate_mustTerminate_run p { st with code := l, compileOracle := coracle, compile := cc }
    h0 res1 s2 hB
  rw [e1, e2]
  by_cases herr : res = some .error
  · subst herr; simp
  rw [if_neg herr] at H
  obtain ⟨rfl, hc, hd, hs2⟩ := H
  by_cases hto : res1 = some .timeOut
  · simp [hto]
  simp only [hto, herr, if_false]
  exact ⟨trivial, hc, hd, by rw [hs2]⟩

open Classical in
/-- The `Seq` clause of `evaluate` on a computed first run (Flapjack infrastructure). -/
theorem evaluate_seq_run {width : Nat} [NeZero width] {C F : Type}
    (c1 c2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
    (hA : evaluate c1 s = (res, s1)) :
    evaluate (.seq c1 c2) s = if res = none then evaluate c2 s1 else (res, s1) := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht]
  simp only [hA]
  split <;> simp_all

/-- The `If` clause of `evaluate` once the guard is read (Flapjack infrastructure). -/
theorem evaluate_ite_read {width : Nat} [NeZero width] {C F : Type} (cmp : Cmp) (r : Nat)
    (ri : WordRegImm (BitVec width)) (c1 c2 : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.ite cmp r ri c1 c2) s =
      match getVar r s, WordSemStateFiniteExact.getVarImm ri s with
      | some x, some y =>
          match wordSemWordCmp cmp x y with
          | some true => evaluate c1 s
          | some false => evaluate c2 s
          | none => (some .error, s)
      | _, _ => (some .error, s) := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ht _ _ _ _ _ _

open Classical in
/-- HOL `compile_single_correct`, `If` case (`word_to_wordProofScript.sml:644-653`), with the
    induction hypotheses of both branches. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_If {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) (cmp : Cmp) (r : Nat)
    (ri : WordRegImm (BitVec width)) (c1 c2 : WordLangProgHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F)
    (ih1 : CompileSingleCorrectSubIH tt kk aa co c1 st)
    (ih2 : CompileSingleCorrectSubIH tt kk aa co c2 st) :
    CompileSingleCorrectAt tt kk aa co (.ite cmp r ri c1 c2) st := by
  rintro l coracle cc hpre
  have hx : ∀ (t : WordSemStateFiniteExact width C F), t.locals = st.locals →
      getVar r t = getVar r st := fun t h => by simp only [getVar, h]
  have hy : ∀ (t : WordSemStateFiniteExact width C F), t.locals = st.locals →
      WordSemStateFiniteExact.getVarImm ri t = WordSemStateFiniteExact.getVarImm ri st := fun t h => by
    cases ri <;> simp only [WordSemStateFiniteExact.getVarImm, getVar, h]
  rcases gx : getVar r st with _ | x
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_ite_read, gx]
    simp
  rcases gy : WordSemStateFiniteExact.getVarImm ri st with _ | y
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_ite_read, gx, gy]
    simp
  rcases gc : wordSemWordCmp cmp x y with _ | b
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_ite_read, gx, gy]
    simp [gc]
  cases b
  · obtain ⟨perm', H⟩ := ih2 st rfl rfl l coracle cc hpre
    refine ⟨perm', ?_⟩
    rw [evaluate_ite_read, evaluate_ite_read, hx { st with permute := perm' } rfl,
      hy { st with permute := perm' } rfl,
      hx { st with code := l, compileOracle := coracle, compile := cc } rfl,
      hy { st with code := l, compileOracle := coracle, compile := cc } rfl, gx, gy]
    simp only [gc]
    exact H
  · obtain ⟨perm', H⟩ := ih1 st rfl rfl l coracle cc hpre
    refine ⟨perm', ?_⟩
    rw [evaluate_ite_read, evaluate_ite_read, hx { st with permute := perm' } rfl,
      hy { st with permute := perm' } rfl,
      hx { st with code := l, compileOracle := coracle, compile := cc } rfl,
      hy { st with code := l, compileOracle := coracle, compile := cc } rfl, gx, gy]
    simp only [gc]
    exact H

open Classical in
/-- HOL `compile_single_correct`, `Seq` case (`word_to_wordProofScript.sml:592-642`), with the
    first statement's induction hypothesis at the same `termdep`/`clock`, the second's at a
    state with the same `termdep` and `clock` (size) or HOL's outer hypotheses (smaller clock). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Seq {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) (c1 c2 : WordLangProgHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F)
    (ih : CompileSingleCorrectLowerIH tt kk aa co st)
    (ih1 : CompileSingleCorrectSubIH tt kk aa co c1 st)
    (ih2 : CompileSingleCorrectSubIH tt kk aa co c2 st) :
    CompileSingleCorrectAt tt kk aa co (.seq c1 c2) st := by
  rintro l coracle cc ⟨hrel, hdom, hcomp, hco, hgc⟩
  obtain ⟨perm1, H1⟩ := ih1 st rfl rfl l coracle cc ⟨hrel, hdom, hcomp, hco, hgc⟩
  rcases hA : evaluate c1 { st with permute := perm1 } with ⟨res, rst⟩
  rw [hA] at H1
  dsimp only at H1
  by_cases herr : res = some .error
  · refine ⟨perm1, ?_⟩
    rw [evaluate_seq_run c1 c2 _ res rst hA]
    simp [herr]
  rw [if_neg herr] at H1
  rcases hB : evaluate c1 { st with code := l, compileOracle := coracle, compile := cc } with ⟨res1, rst1⟩
  rw [hB] at H1
  dsimp only at H1
  obtain ⟨rfl, hc1, hd1, hs1⟩ := H1
  cases res1 with
  | some x =>
    refine ⟨perm1, ?_⟩
    rw [evaluate_seq_run c1 c2 _ _ rst hA, evaluate_seq_run c1 c2 _ _ rst1 hB]
    simp only [reduceCtorEq, if_false, herr]
    exact ⟨trivial, hc1, hd1, hs1⟩
  | none =>
    have hcl := evaluate_clock c1 _ _ _ hA
    have hconst := evaluate_consts c1 _ _ _ hA
    have P2 : CompileSingleCorrectAt tt kk aa co c2 rst := by
      rcases Nat.lt_or_ge rst.clock st.clock with hlt | hge
      · exact ih c2 rst (Or.inr ⟨hcl.2, hlt⟩)
      · exact ih2 rst hcl.2 (Nat.le_antisymm hcl.1 hge)
    have hcomp' : rst.compile =
        (fun conf progs => cc conf (progs.map (fun p => compileSingle tt kk aa co (p, none)))) := by
      rw [← hconst.2.2.2.2.1]; exact hcomp
    have hco' : rst1.compileOracle =
        Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ rst.compileOracle := by
      rw [hs1]
    have hgc' : WordSimp.gcFunConstOk rst.gcFun := by rw [← hconst.1]; exact hgc
    obtain ⟨perm2, H2⟩ := P2 rst1.code rst1.compileOracle cc ⟨hc1, hd1, hcomp', hco', hgc'⟩
    have hsw := permute_swap_lemma c1 { st with permute := perm1 } perm2
    rw [hA] at hsw
    obtain ⟨perm3, hP⟩ := hsw (by simp)
    refine ⟨perm3, ?_⟩
    rw [evaluate_seq_run c1 c2 { st with permute := perm3 } none { rst with permute := perm2 } hP,
      evaluate_seq_run c1 c2 _ none rst1 hB]
    simp only [if_true]
    have hr : ({ rst with code := rst1.code, compileOracle := rst1.compileOracle, compile := cc } :
        WordSemStateFiniteExact width C F) = rst1 := by rw [hs1]
    rw [← hr]
    exact H2

open Classical in
/-- The `Loop` clause of `evaluate` on a computed cut and body run (Flapjack
    infrastructure; HOL's `case res of SOME (Break 0) => … | _ => …` as an `if`). -/
theorem evaluate_loop_run {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : WordLangNumSetHOL) (c : WordLangProgHOL (BitVec width))
    (s s' : WordSemStateFiniteExact width C F) (hcut : cutState (names, .ln) s = some s')
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
    (hA : evaluate c s' = (res, s1)) :
    evaluate (.loop names c exitNames) s =
      if wordSemContLoop res = true then
        (if s1.clock = 0 then (some .timeOut, flushState true s1)
         else evaluate (.loop names c exitNames) (decClock s1))
      else if res = some (.break 0) then
        (match cutState (exitNames, .ln) s1 with
         | none => (some .error, s1)
         | some s2 => (none, s2))
      else (wordSemExitLoop res, s1) := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht]
  simp only [hcut, hA, wordSemSTOP]
  by_cases hc : wordSemContLoop res = true
  · simp only [hc, if_true]
  · simp only [hc, Bool.false_eq_true, if_false]
    by_cases hb : res = some (.break 0)
    · subst hb
      rw [if_pos rfl]
      rcases cutState (exitNames, .ln) s1 <;> rfl
    · rw [if_neg hb]
      cases res with
      | none => rfl
      | some r =>
        cases r <;> try rfl
        rename_i n
        cases n
        · exact absurd rfl hb
        · rfl

/-- `cutState` reads only the locals (Flapjack infrastructure). -/
theorem cutState_locals {width : Nat} [NeZero width] {C F : Type} (names : WordLangCutsetsHOL)
    (s t : WordSemStateFiniteExact width C F) (h : t.locals = s.locals) :
    cutState names t = (cutState names s).map (fun s' => { t with locals := s'.locals }) := by
  unfold cutState
  rw [h]
  split <;> rfl

open Classical in
/-- HOL `compile_single_correct`, `Loop` case (`word_to_wordProofScript.sml:655-748`), with the
    body's induction hypothesis at the same `termdep`/`clock` and HOL's outer hypotheses for the
    next iteration at a smaller clock. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Loop {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) (names : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec width)) (exitNames : WordLangNumSetHOL)
    (st : WordSemStateFiniteExact width C F)
    (ih : CompileSingleCorrectLowerIH tt kk aa co st)
    (ihb : CompileSingleCorrectSubIH tt kk aa co body st) :
    CompileSingleCorrectAt tt kk aa co (.loop names body exitNames) st := by
  rintro l coracle cc ⟨hrel, hdom, hcomp, hco, hgc⟩
  rcases hcut : wordSemCutEnv (names, .ln) st.locals with _ | env
  · refine ⟨st.permute, ?_⟩
    have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp [ht, cutState, hcut]
  let stt : WordSemStateFiniteExact width C F := { st with locals := env }
  have cutP : ∀ p, cutState (names, .ln) { st with permute := p } = some { stt with permute := p } :=
    fun p => by simp only [cutState, hcut]; rfl
  have cutT : cutState (names, .ln) { st with code := l, compileOracle := coracle, compile := cc } =
      some { stt with code := l, compileOracle := coracle, compile := cc } := by
    simp only [cutState, hcut]; rfl
  obtain ⟨perm', H⟩ := ihb stt rfl rfl l coracle cc ⟨hrel, hdom, hcomp, hco, hgc⟩
  rcases hA : evaluate body { stt with permute := perm' } with ⟨res, rst⟩
  rw [hA] at H
  dsimp only at H
  by_cases herr : res = some .error
  · refine ⟨perm', ?_⟩
    rw [evaluate_loop_run names exitNames body _ _ (cutP perm') res rst hA]
    subst herr
    simp [wordSemContLoop, wordSemExitLoop]
  rw [if_neg herr] at H
  rcases hB : evaluate body { stt with code := l, compileOracle := coracle, compile := cc } with
    ⟨res1, rst1⟩
  rw [hB] at H
  dsimp only at H
  obtain ⟨rfl, hc1, hd1, hs1⟩ := H
  have hcl := evaluate_clock body _ _ _ hA
  have hconst := evaluate_consts body _ _ _ hA
  have hclk1 : rst1.clock = rst.clock := by rw [hs1]
  by_cases hcont : wordSemContLoop res1 = true
  · by_cases hz : rst.clock = 0
    · refine ⟨perm', ?_⟩
      rw [evaluate_loop_run names exitNames body _ _ (cutP perm') res1 rst hA,
        evaluate_loop_run names exitNames body _ _ cutT res1 rst1 hB]
      simp only [hcont, if_true, hz, hclk1]
      rw [if_neg (show some WordSemResult.timeOut ≠ some WordSemResult.error by simp)]
      refine ⟨trivial, ?_, ?_, ?_⟩
      · exact hc1
      · exact hd1
      · rw [hs1]; rfl
    -- the next iteration, at a smaller clock
    have hlt : (decClock rst).clock < st.clock := by
      simp only [decClock]; have := hcl.1; simp only [stt] at this; omega
    have P2 := ih (.loop names body exitNames) (decClock rst) (Or.inr ⟨by
      simp only [decClock]; exact hcl.2, hlt⟩)
    have hcomp' : (decClock rst).compile =
        (fun conf progs => cc conf (progs.map (fun p => compileSingle tt kk aa co (p, none)))) := by
      show rst.compile = _
      rw [← hconst.2.2.2.2.1]; exact hcomp
    have hco' : rst1.compileOracle =
        Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘
          (decClock rst).compileOracle := by
      rw [hs1]; rfl
    have hgc' : WordSimp.gcFunConstOk (decClock rst).gcFun := by
      show WordSimp.gcFunConstOk rst.gcFun
      rw [← hconst.1]; exact hgc
    obtain ⟨perm2, H2⟩ := P2 rst1.code rst1.compileOracle cc ⟨hc1, hd1, hcomp', hco', hgc'⟩
    have hsw := permute_swap_lemma body { stt with permute := perm' } perm2
    rw [hA] at hsw
    obtain ⟨perm3, hP⟩ := hsw herr
    refine ⟨perm3, ?_⟩
    rw [evaluate_loop_run names exitNames body _ _ (cutP perm3) res1 _ hP,
      evaluate_loop_run names exitNames body _ _ cutT res1 rst1 hB]
    simp only [hcont, if_true, hz, hclk1, if_false]
    have hr : ({ decClock rst with
        code := rst1.code
        compileOracle := rst1.compileOracle
        compile := cc } : WordSemStateFiniteExact width C F) = decClock rst1 := by
      rw [hs1]; rfl
    rw [← hr]
    exact H2
  · refine ⟨perm', ?_⟩
    rw [evaluate_loop_run names exitNames body _ _ (cutP perm') res1 rst hA,
      evaluate_loop_run names exitNames body _ _ cutT res1 rst1 hB]
    simp only [hcont, Bool.false_eq_true, if_false]
    have hcx : cutState (exitNames, .ln) rst1 =
        (cutState (exitNames, .ln) rst).map (fun s' => { rst1 with locals := s'.locals }) :=
      cutState_locals _ rst rst1 (by rw [hs1])
    by_cases hb : res1 = some (.break 0)
    · simp only [hb, if_true]
      rw [hcx]
      rcases hx : cutState (exitNames, .ln) rst with _ | s2
      · simp
      · obtain ⟨lx, rfl⟩ := cutStateConst _ _ _ hx
        simp only [Option.map_some, if_false, reduceCtorEq]
        exact ⟨trivial, hc1, hd1, by rw [hs1]⟩
    · simp only [hb, if_false]
      split
      · trivial
      · exact ⟨trivial, hc1, hd1, hs1⟩

end Flapjack.Compiler.Backend.WordToWord
