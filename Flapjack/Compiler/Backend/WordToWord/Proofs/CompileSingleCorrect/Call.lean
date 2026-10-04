import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Control
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingle
import Flapjack.Misc.Sptree.FromList2

/-!
# `word_to_wordProof` `compile_single_correct`: the `Call` case

The `Call` `Resume` case of HOL `compile_single_correct`
(`word_to_wordProofScript.sml:347-589`). The callee body is looked up in the
source code table and, by `find_code_thm`, its `compile_single` image in the
compiled table; HOL's outer induction hypothesis runs the compiled body on both
code tables, `compile_single_lem` relates the source body to its compiled
image, and `permute_swap_lemma` aligns the final permutation.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

namespace CompileSingleCorrectCallCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileSingleCorrectCallCarrier

section Helpers

variable {width : Nat} [NeZero width] {C F : Type}

/-- The `Call` clause of `evaluate` (Flapjack restatement of the last
    `evaluate_def` conjunct). -/
theorem evaluate_call_eq (s : WordSemStateFiniteExact width C F)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) (dest : Option Nat)
    (args : List Nat) :
    evaluate (.call ret dest args handler) s =
      match WordSemStateFiniteExact.getVars args s with
      | none => (some .error, s)
      | some xs =>
          if wordSemBadDestArgs dest args then (some .error, s)
          else
            match wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
            | none => (some .error, s)
            | some (args1, prog, ss) =>
                match ret with
                | none =>
                    match handler with
                    | none =>
                        if s.clock = 0 then (some .timeOut, flushState true s)
                        else
                          match evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with
                          | (res, s) =>
                              if wordSemBadFunReturn res then (some .error, s) else (res, s)
                    | some _ => (some .error, s)
                | some (n, names, retHandler, l1, l2) =>
                    if sptDomainEmpty names.1 ∨ ¬ n.Nodup then (some .error, s)
                    else
                      match wordSemCutEnvs names s.locals with
                      | none => (some .error, s)
                      | some envs =>
                          if s.clock = 0 then
                            (some .timeOut, flushState true
                              { s with stack := [],
                                       stackMax := (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler s)).stackMax })
                          else
                            match evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with
                            | (some (.result x ys), s2) =>
                                if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then (some .error, s2)
                                else
                                  match popEnv s2 with
                                  | none => (some .error, s2)
                                  | some s1 =>
                                      if sptDomainEqUnion s1.locals envs.1 envs.2 then
                                        evaluate retHandler (setVars n ys s1)
                                      else (some .error, s1)
                            | (some (.exception x y), s2) =>
                                match handler with
                                | none => (some (.exception x y), s2)
                                | some (n, hprog, l1, l2) =>
                                    if x ≠ .loc l1 l2 then (some .error, s2)
                                    else if sptDomainEqUnion s2.locals envs.1 envs.2 then
                                      evaluate hprog (setVar n y s2)
                                    else (some .error, s2)
                            | (none, s) => (some .error, s)
                            | (some (.break _), s) => (some .error, s)
                            | (some (.continue _), s) => (some .error, s)
                            | res => res :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    s ret handler dest args

/-- States related by `word_state_eq_rel` with equal locals differ only in the
    permutation (Flapjack infrastructure). -/
theorem eqRel_permute {s t : WordSemStateFiniteExact width C F} (h : WordAlloc.wordStateEqRel s t)
    (hl : s.locals = t.locals) : ({ s with permute := t.permute } : WordSemStateFiniteExact width C F) = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  cases s; cases t
  simp_all

end Helpers

/-- `code_rel` in the existential order of `find_code_thm` (Flapjack infrastructure). -/
theorem codeRel_findCode {width : Nat} [NeZero width] {stc ttc : Spt (Nat × WordLangProgHOL (BitVec width))}
    (h : codeRel stc ttc) :
    ∀ n v, sptLookup n stc = some v →
      ∃ (t : Bool) (k a : Nat) (c : AsmConfigExact width) (col : Option (Spt Nat)),
        sptLookup n ttc = some (compileSingle t k a c ((n, v), col)).2 := by
  intro n v hv
  obtain ⟨col, t, k, a, c, hl⟩ := h n v hv
  exact ⟨t, k, a, c, col, hl⟩

open Classical in
/-- The tail-call branch of the `Call` case (Flapjack factoring of HOL's
    `(*Tail calls*)` subproof). -/
theorem compileSingleCorrect_callTail {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) (dest : Option Nat) (args : List Nat)
    (st : WordSemStateFiniteExact width C F) (ih : CompileSingleCorrectLowerIH tt kk aa co st) :
    CompileSingleCorrectAt tt kk aa co (.call none dest args none) st := by
  rintro l coracle cc ⟨hrel, hdom, hcomp, rfl, hgc⟩
  rcases hxs : WordSemStateFiniteExact.getVars args st with _ | xs
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp
  by_cases hbad : wordSemBadDestArgs dest args = true
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp [hbad]
  rcases hfc : wordSemFindCode dest (wordSemAddRetLoc none xs) st.code st.stackSize with
    _ | ⟨args1, prog, ss⟩
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp [hbad, hfc]
  obtain ⟨t, k, a, c, col, n, prog', hcs, hfcT⟩ :=
    find_code_thm st l dest none xs args1 prog ss ⟨codeRel_findCode hrel, hfc⟩
  let O := Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ st.compileOracle
  let T : WordSemStateFiniteExact width C F :=
    { st with
      code := l
      compileOracle := O
      compile := cc }
  -- the two runs of the call, from the callee runs
  have srcRun : ∀ (P : Nat → Nat → Nat) (r : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock { st with permute := P })) =
        (r, s') →
      evaluate (.call none dest args none) { st with permute := P } =
        if st.clock = 0 then (some .timeOut, flushState true { st with permute := P })
        else if wordSemBadFunReturn r then (some .error, s') else (r, s') := by
    intro P r s' h
    rw [evaluate_call_eq, show WordSemStateFiniteExact.getVars args { st with permute := P } = some xs
      from (getVars_congr st { st with permute := P } rfl args).trans hxs]
    dsimp only
    rw [if_neg hbad, show wordSemFindCode dest (wordSemAddRetLoc none xs) st.code st.stackSize =
      some (args1, prog, ss) from hfc]
    dsimp only
    split
    · rfl
    · rw [h]
  have tgtRun : ∀ (r : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate prog' (WordSemStateFiniteExact.callEnv args1 ss (decClock T)) = (r, s') →
      evaluate (.call none dest args none) T =
        if st.clock = 0 then (some .timeOut, flushState true T)
        else if wordSemBadFunReturn r then (some .error, s') else (r, s') := by
    intro r s' h
    rw [evaluate_call_eq, show WordSemStateFiniteExact.getVars args T = some xs
      from (getVars_congr st T rfl args).trans hxs]
    dsimp only
    rw [if_neg hbad, show wordSemFindCode dest (wordSemAddRetLoc none xs) l st.stackSize =
      some (args1, prog', ss) from hfcT]
    dsimp only
    split
    · rfl
    · rw [h]
  by_cases hz : st.clock = 0
  · refine ⟨st.permute, ?_⟩
    obtain ⟨r0, s0⟩ := evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock st))
    rcases h1 : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock st)) with ⟨r0, s0⟩
    rcases h2 : evaluate prog' (WordSemStateFiniteExact.callEnv args1 ss (decClock T)) with ⟨r1, s1⟩
    rw [srcRun st.permute r0 s0 h1, tgtRun r1 s1 h2]
    simp only [hz, if_true]
    rw [if_neg (show some WordSemResult.timeOut ≠ some WordSemResult.error by simp)]
    exact ⟨trivial, hrel, hdom, by simp [flushState, T, O, hz]⟩
  -- the callee state
  let stt : WordSemStateFiniteExact width C F := WordSemStateFiniteExact.callEnv args1 ss (decClock st)
  obtain ⟨perm1, H1⟩ := ih prog' stt (Or.inr ⟨rfl, by
      show st.clock - 1 < st.clock; omega⟩) l O cc ⟨hrel, hdom, hcomp, rfl, hgc⟩
  rcases hA : evaluate prog' { stt with permute := perm1 } with ⟨resA, rA⟩
  rw [hA] at H1
  dsimp only at H1
  have hcs' : compileSingle t k a c ((n, args1.length, prog), col) = (n, args1.length, prog') :=
    Prod.ext rfl hcs
  obtain ⟨perm2, H2⟩ := compile_single_lem t k a c n col prog args1.length { stt with permute := perm1 }
    ⟨sptDomainFromList2 args1, hgc⟩
  rw [hcs'] at H2
  rcases hR : evaluate prog { { stt with permute := perm1 } with permute := perm2 } with ⟨res, rst⟩
  rw [hR] at H2
  dsimp only at H2
  by_cases herr : res = some .error
  · refine ⟨perm2, ?_⟩
    rcases h2 : evaluate prog' (WordSemStateFiniteExact.callEnv args1 ss (decClock T)) with ⟨r1, s1⟩
    rw [srcRun perm2 res rst hR, tgtRun r1 s1 h2]
    subst herr
    simp only [hz, if_false, ite_self]
    simp
  rw [if_neg herr, hA] at H2
  dsimp only at H2
  obtain ⟨hres, heq, hloc⟩ := H2
  subst resA
  rw [if_neg herr] at H1
  rcases hB : evaluate prog' { stt with code := l, compileOracle := O, compile := cc } with
    ⟨resB, rB⟩
  rw [hB] at H1
  dsimp only at H1
  obtain ⟨hresB, hcB, hdB, hsB⟩ := H1
  subst resB
  have hsw := permute_swap_lemma prog { stt with permute := perm2 } rA.permute
  rw [show evaluate prog { stt with permute := perm2 } = (res, rst) from hR] at hsw
  obtain ⟨perm3, hP⟩ := hsw herr
  refine ⟨perm3, ?_⟩
  rw [srcRun perm3 res _ hP, tgtRun res rB hB]
  simp only [hz, if_false]
  by_cases hbr : wordSemBadFunReturn res = true
  · simp [hbr]
  simp only [hbr, Bool.false_eq_true, if_false]
  have hlocal : rst.locals = rA.locals := by
    rcases res with _ | r
    · exact absurd rfl hbr
    cases r <;> first | exact absurd rfl hbr | exact hloc
  have hcode : rst.code = rA.code := heq.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm
  have hst : ({ rst with permute := rA.permute } : WordSemStateFiniteExact width C F) = rA :=
    eqRel_permute heq hlocal
  rw [if_neg herr]
  refine ⟨by simp, ?_, ?_, ?_⟩
  · show codeRel rst.code rB.code; rw [hcode]; exact hcB
  · show sptDomain rst.code = sptDomain rB.code; rw [hcode]; exact hdB
  · rw [← hst] at hsB; exact hsB

section RetHelpers

variable {width : Nat} [NeZero width] {C F : Type}

/-- Pushing a frame consumes `permute 0` and shifts the permutation, so HOL's
    witness `λn. if n = 0 then s.permute 0 else q (n - 1)` leaves `q` for the
    callee (Flapjack infrastructure). -/
theorem pushEnv_shift (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (q : Nat → Nat → Nat) :
    pushEnv envs h { s with permute := fun n => if n = 0 then s.permute 0 else q (n - 1) } =
      { pushEnv envs h s with permute := q } := by
  have hq : (fun n => (fun n => if n = 0 then s.permute 0 else q (n - 1)) (n + 1)) = q := by
    funext n; simp
  cases h <;> simp only [pushEnv, wordSemEnvToList, if_pos] <;> rw [hq]

theorem pushEnv_fields (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    (pushEnv envs h s).code = s.code ∧ (pushEnv envs h s).compile = s.compile ∧
      (pushEnv envs h s).compileOracle = s.compileOracle ∧ (pushEnv envs h s).gcFun = s.gcFun ∧
      (pushEnv envs h s).clock = s.clock ∧ (pushEnv envs h s).termdep = s.termdep := by
  cases h <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `pushEnv` commutes with replacing the code table, oracle and `compile`. -/
theorem pushEnv_tgt (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (o : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C)) :
    pushEnv envs h { s with code := l, compileOracle := o, compile := cc } =
      { pushEnv envs h s with code := l, compileOracle := o, compile := cc } := by
  cases h <;> rfl

/-- `popEnv` commutes with replacing the permutation, code table, oracle and
    `compile` (Flapjack infrastructure). -/
theorem popEnv_with (s : WordSemStateFiniteExact width C F) (q : Nat → Nat → Nat)
    (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (o : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C)) :
    popEnv { s with permute := q, code := l, compileOracle := o, compile := cc } =
      (popEnv s).map (fun t => { t with permute := q, code := l, compileOracle := o, compile := cc }) := by
  unfold popEnv
  dsimp only
  split <;> rfl

theorem popEnv_permute (s : WordSemStateFiniteExact width C F) (q : Nat → Nat → Nat) :
    popEnv { s with permute := q } = (popEnv s).map (fun t => { t with permute := q }) := by
  unfold popEnv
  dsimp only
  split <;> rfl

theorem popEnv_fields {s t : WordSemStateFiniteExact width C F} (h : popEnv s = some t) :
    t.code = s.code ∧ t.compile = s.compile ∧ t.compileOracle = s.compileOracle ∧
      t.gcFun = s.gcFun ∧ t.clock = s.clock ∧ t.termdep = s.termdep := by
  unfold popEnv at h
  split at h <;> first | (cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) | simp at h

end RetHelpers

open Classical in
/-- The returning-call branch of the `Call` case (Flapjack factoring of HOL's
    non-tail-call subproof, with its `Result` and `Exception` simulations). -/
theorem compileSingleCorrect_callRet {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) (xn : List Nat) (names : WordLangCutsetsHOL)
    (xrh : WordLangProgHOL (BitVec width)) (xl1 xl2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (st : WordSemStateFiniteExact width C F) (ih : CompileSingleCorrectLowerIH tt kk aa co st) :
    CompileSingleCorrectAt tt kk aa co (.call (some (xn, names, xrh, xl1, xl2)) dest args handler) st := by
  rintro l coracle cc ⟨hrel, hdom, hcomp, rfl, hgc⟩
  rcases hxs : WordSemStateFiniteExact.getVars args st with _ | xs
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp
  by_cases hbad : wordSemBadDestArgs dest args = true
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp [hbad]
  rcases hfc : wordSemFindCode dest (wordSemAddRetLoc (some (xn, names, xrh, xl1, xl2)) xs) st.code
      st.stackSize with _ | ⟨args1, prog, ss⟩
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp [hbad, hfc]
  obtain ⟨t, k, a, c, col, n, prog', hcs, hfcT⟩ :=
    find_code_thm st l dest (some (xn, names, xrh, xl1, xl2)) xs args1 prog ss
      ⟨codeRel_findCode hrel, hfc⟩
  by_cases hnm : sptDomainEmpty names.1 ∨ ¬ xn.Nodup
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp [hbad, hfc, hnm]
  rcases hce : wordSemCutEnvs names st.locals with _ | envs
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp [hbad, hfc, hnm, hce]
  let O := Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ st.compileOracle
  let T : WordSemStateFiniteExact width C F :=
    { st with
      code := l
      compileOracle := O
      compile := cc }
  -- the continuation after the callee returns
  let K : Option (WordSemResult width) × WordSemStateFiniteExact width C F →
      Option (WordSemResult width) × WordSemStateFiniteExact width C F := fun p =>
    match p with
    | (some (.result x ys), s2) =>
        if x ≠ .loc xl1 xl2 ∨ ys.length ≠ xn.length then (some .error, s2)
        else
          match popEnv s2 with
          | none => (some .error, s2)
          | some s1 =>
              if sptDomainEqUnion s1.locals envs.1 envs.2 then
                evaluate xrh (WordSemStateFiniteExact.setVars xn ys s1)
              else (some .error, s1)
    | (some (.exception x y), s2) =>
        match handler with
        | none => (some (.exception x y), s2)
        | some (hn, hprog, hl1, hl2) =>
            if x ≠ .loc hl1 hl2 then (some .error, s2)
            else if sptDomainEqUnion s2.locals envs.1 envs.2 then
              evaluate hprog (setVar hn y s2)
            else (some .error, s2)
    | (none, s) => (some .error, s)
    | (some (.break _), s) => (some .error, s)
    | (some (.continue _), s) => (some .error, s)
    | res => res
  have srcRun : ∀ (P : Nat → Nat → Nat) (r : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate prog (WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs handler (decClock { st with permute := P }))) = (r, s') →
      st.clock ≠ 0 →
      evaluate (.call (some (xn, names, xrh, xl1, xl2)) dest args handler) { st with permute := P } =
        K (r, s') := by
    intro P r s' h hz
    rw [evaluate_call_eq, show WordSemStateFiniteExact.getVars args { st with permute := P } = some xs
      from (getVars_congr st { st with permute := P } rfl args).trans hxs]
    dsimp only
    rw [if_neg hbad, show wordSemFindCode dest (wordSemAddRetLoc (some (xn, names, xrh, xl1, xl2)) xs)
      st.code st.stackSize = some (args1, prog, ss) from hfc]
    dsimp only
    rw [if_neg hnm, show wordSemCutEnvs names st.locals = some envs from hce]
    dsimp only
    rw [if_neg hz, h]
  have tgtRun : ∀ (r : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate prog' (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock T))) =
        (r, s') →
      st.clock ≠ 0 →
      evaluate (.call (some (xn, names, xrh, xl1, xl2)) dest args handler) T = K (r, s') := by
    intro r s' h hz
    rw [evaluate_call_eq, show WordSemStateFiniteExact.getVars args T = some xs
      from (getVars_congr st T rfl args).trans hxs]
    dsimp only
    rw [if_neg hbad, show wordSemFindCode dest (wordSemAddRetLoc (some (xn, names, xrh, xl1, xl2)) xs)
      l st.stackSize = some (args1, prog', ss) from hfcT]
    dsimp only
    rw [if_neg hnm, show wordSemCutEnvs names T.locals = some envs from hce]
    dsimp only
    rw [if_neg hz, h]
  by_cases hz : st.clock = 0
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs, evaluate_call_eq, show WordSemStateFiniteExact.getVars args T = some xs
      from (getVars_congr st T rfl args).trans hxs]
    simp only [hbad, Bool.false_eq_true, if_false, hfc, hfcT, hnm, hce, hz, if_true]
    rw [if_neg (show some WordSemResult.timeOut ≠ some WordSemResult.error by simp)]
    refine ⟨trivial, hrel, hdom, ?_⟩
    cases handler <;> rfl
  have hpf := pushEnv_fields envs handler (decClock st)
  let stt : WordSemStateFiniteExact width C F :=
    WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock st))
  have sttCode : stt.code = st.code := hpf.1
  have sttComp : stt.compile = st.compile := hpf.2.1
  have sttOr : stt.compileOracle = st.compileOracle := hpf.2.2.1
  have sttGc : stt.gcFun = st.gcFun := hpf.2.2.2.1
  have sttClock : stt.clock = st.clock - 1 := hpf.2.2.2.2.1
  have sttTd : stt.termdep = st.termdep := hpf.2.2.2.2.2
  obtain ⟨perm1, H1⟩ := ih prog' stt (Or.inr ⟨sttTd, by rw [sttClock]; omega⟩) l O cc
    ⟨by rw [sttCode]; exact hrel, by rw [sttCode]; exact hdom, by rw [sttComp]; exact hcomp,
      by rw [sttOr], by rw [sttGc]; exact hgc⟩
  rcases hA : evaluate prog' { stt with permute := perm1 } with ⟨resA, rA⟩
  rw [hA] at H1
  dsimp only at H1
  have hcs' : compileSingle t k a c ((n, args1.length, prog), col) = (n, args1.length, prog') :=
    Prod.ext rfl hcs
  obtain ⟨perm2, H2⟩ := compile_single_lem t k a c n col prog args1.length { stt with permute := perm1 }
    ⟨sptDomainFromList2 args1, by show WordSimp.gcFunConstOk stt.gcFun; rw [sttGc]; exact hgc⟩
  rw [hcs'] at H2
  rcases hR : evaluate prog { { stt with permute := perm1 } with permute := perm2 } with ⟨res, rst⟩
  rw [hR] at H2
  dsimp only at H2
  have hR' : evaluate prog { stt with permute := perm2 } = (res, rst) := hR
  -- the source callee, ending in any chosen permutation
  have hswap : ∀ q : Nat → Nat → Nat, res ≠ some .error → ∃ P : Nat → Nat → Nat,
      evaluate prog (WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs handler (decClock { st with permute := P }))) = (res, { rst with permute := q }) := by
    intro q hne
    have hsw := permute_swap_lemma prog { stt with permute := perm2 } q
    rw [hR'] at hsw
    obtain ⟨perm4, hP⟩ := hsw hne
    refine ⟨fun n => if n = 0 then st.permute 0 else perm4 (n - 1), ?_⟩
    have hpush := pushEnv_shift envs handler (decClock st) perm4
    rw [show decClock { st with permute := fun n => if n = 0 then st.permute 0 else perm4 (n - 1) } =
      { decClock st with permute := fun n => if n = 0 then (decClock st).permute 0 else perm4 (n - 1) }
      from rfl, hpush]
    exact hP
  by_cases herr : res = some .error
  · obtain ⟨P, hP⟩ : ∃ P : Nat → Nat → Nat, evaluate prog (WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs handler (decClock { st with permute := P }))) = (res, rst) := by
      refine ⟨fun n => if n = 0 then st.permute 0 else perm2 (n - 1), ?_⟩
      have hpush := pushEnv_shift envs handler (decClock st) perm2
      rw [show decClock { st with permute := fun n => if n = 0 then st.permute 0 else perm2 (n - 1) } =
        { decClock st with permute := fun n => if n = 0 then (decClock st).permute 0 else perm2 (n - 1) }
        from rfl, hpush]
      exact hR'
    refine ⟨P, ?_⟩
    rw [srcRun P res rst hP hz]
    subst herr
    simp [K]
  rw [if_neg herr, hA] at H2
  dsimp only at H2
  obtain ⟨hres, heq, hloc⟩ := H2
  subst resA
  rw [if_neg herr] at H1
  rcases hB : evaluate prog' { stt with code := l, compileOracle := O, compile := cc } with ⟨resB, rB⟩
  rw [hB] at H1
  dsimp only at H1
  obtain ⟨hresB, hcB, hdB, hsB⟩ := H1
  subst resB
  have hB' : evaluate prog' (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock T))) =
      (res, rB) := by
    rw [show decClock T = { decClock st with code := l, compileOracle := O, compile := cc } from rfl,
      pushEnv_tgt]
    exact hB
  have hclkR := evaluate_clock prog _ _ _ hR'
  have hconR := evaluate_consts prog _ _ _ hR'
  by_cases hbr : wordSemBadFunReturn res = true
  · obtain ⟨P, hP⟩ := hswap rst.permute herr
    refine ⟨P, ?_⟩
    rw [srcRun P _ _ hP hz]
    rcases res with _ | r
    · simp [K]
    cases r <;> first | (simp [wordSemBadFunReturn] at hbr; done) | (simp only [K]; simp)
  have hlocal : rst.locals = rA.locals := by
    rcases res with _ | r
    · exact absurd rfl hbr
    cases r <;> first | exact absurd rfl hbr | exact hloc
  have hst := eqRel_permute heq hlocal
  obtain ⟨pA, hpA⟩ : ∃ pA, rA.permute = pA := ⟨_, rfl⟩
  rw [hpA] at hst
  subst hst
  obtain ⟨cB, hcBe⟩ : ∃ cB, rB.code = cB := ⟨_, rfl⟩
  rw [hcBe] at hsB
  subst hsB
  rcases res with _ | r
  · exact absurd rfl hbr
  cases r with
  | «break» _ => exact absurd rfl hbr
  | «continue» _ => exact absurd rfl hbr
  | error => exact absurd rfl herr
  | timeOut | notEnoughSpace | finalFfi _ =>
    obtain ⟨P, hP⟩ := hswap pA herr
    refine ⟨P, ?_⟩
    rw [srcRun P _ _ hP hz, tgtRun _ _ hB' hz]
    simp only [K]
    rw [if_neg herr]
    exact ⟨by trivial, hcB, hdB, by trivial⟩
  | result x ys =>
    by_cases hx : x ≠ .loc xl1 xl2 ∨ ys.length ≠ xn.length
    · obtain ⟨P, hP⟩ := hswap pA herr
      refine ⟨P, ?_⟩
      rw [srcRun P _ _ hP hz]
      simp [K, hx]
    rcases hpop : popEnv rst with _ | x''
    · obtain ⟨P, hP⟩ := hswap pA herr
      refine ⟨P, ?_⟩
      rw [srcRun P _ _ hP hz]
      simp only [K, hx, if_false]
      rw [popEnv_permute, hpop]
      simp
    have hpf2 := popEnv_fields hpop
    by_cases hdu : sptDomainEqUnion x''.locals envs.1 envs.2
    swap
    · obtain ⟨P, hP⟩ := hswap pA herr
      refine ⟨P, ?_⟩
      rw [srcRun P _ _ hP hz]
      simp only [K, hx, if_false]
      rw [popEnv_permute, hpop]
      simp [hdu]
    let Y : WordSemStateFiniteExact width C F :=
      WordSemStateFiniteExact.setVars xn ys { x'' with permute := pA }
    have hYc : Y.clock < st.clock := by
      show x''.clock < st.clock
      rw [hpf2.2.2.2.2.1]
      have := hclkR.1
      change rst.clock ≤ stt.clock at this
      rw [sttClock] at this
      omega
    have hYt : Y.termdep = st.termdep := by
      show x''.termdep = st.termdep
      rw [hpf2.2.2.2.2.2, hclkR.2]; exact sttTd
    obtain ⟨perm3, H3⟩ := ih xrh Y (Or.inr ⟨hYt, hYc⟩) cB
      (Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ Y.compileOracle) cc
      ⟨by show codeRel x''.code cB; rw [hpf2.1]; exact hcB,
       by show sptDomain x''.code = sptDomain cB; rw [hpf2.1]; exact hdB,
       by show x''.compile = _; rw [hpf2.2.1, ← hconR.2.2.2.2.1]; show stt.compile = _;
          rw [sttComp]; exact hcomp,
       rfl,
       by show WordSimp.gcFunConstOk x''.gcFun; rw [hpf2.2.2.2.1, ← hconR.1]; show WordSimp.gcFunConstOk stt.gcFun;
          rw [sttGc]; exact hgc⟩
    obtain ⟨P, hP⟩ := hswap perm3 herr
    refine ⟨P, ?_⟩
    have hnx : ¬(x ≠ .loc xl1 xl2 ∨ ys.length ≠ xn.length) := hx
    have srcRes : evaluate (.call (some (xn, names, xrh, xl1, xl2)) dest args handler)
        { st with permute := P } = evaluate xrh { Y with permute := perm3 } := by
      rw [srcRun P _ _ hP hz]
      simp only [K]
      rw [if_neg hnx, popEnv_permute, hpop]
      dsimp only [Option.map]
      rw [if_pos hdu]
      rfl
    let M := Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ x''.compileOracle
    have tgtRes : evaluate (.call (some (xn, names, xrh, xl1, xl2)) dest args handler) T =
        evaluate xrh { Y with code := cB, compileOracle := M, compile := cc } := by
      rw [tgtRun _ _ hB' hz]
      let Mr := Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ rst.compileOracle
      show K (some (.result x ys), { rst with permute := pA, code := cB, compileOracle := Mr, compile := cc }) = _
      simp only [K]
      rw [if_neg hnx, popEnv_with, hpop]
      dsimp only [Option.map]
      rw [if_pos hdu]
      have hMM : M = Mr := by simp only [M, Mr, hpf2.2.2.1]
      rw [hMM]
      rfl
    rw [srcRes, tgtRes]
    exact H3
  | exception x y =>
    cases handler with
    | none =>
      obtain ⟨P, hP⟩ := hswap pA herr
      refine ⟨P, ?_⟩
      rw [srcRun P _ _ hP hz, tgtRun _ _ hB' hz]
      simp only [K]
      rw [if_neg herr]
      exact ⟨by trivial, hcB, hdB, by trivial⟩
    | some hh =>
      obtain ⟨hn, hprog, hl1, hl2⟩ := hh
      by_cases hxl : x ≠ .loc hl1 hl2
      · obtain ⟨P, hP⟩ := hswap pA herr
        refine ⟨P, ?_⟩
        rw [srcRun P _ _ hP hz]
        simp [K, hxl]
      by_cases hdu : sptDomainEqUnion rst.locals envs.1 envs.2
      swap
      · obtain ⟨P, hP⟩ := hswap pA herr
        refine ⟨P, ?_⟩
        rw [srcRun P _ _ hP hz]
        simp only [K, hxl, if_false]
        rw [if_neg (show ¬sptDomainEqUnion ({ rst with permute := pA } :
          WordSemStateFiniteExact width C F).locals envs.1 envs.2 from hdu)]
        simp
      let Y : WordSemStateFiniteExact width C F := setVar hn y { rst with permute := pA }
      have hYc : Y.clock < st.clock := by
        show rst.clock < st.clock
        have := hclkR.1
        change rst.clock ≤ stt.clock at this
        rw [sttClock] at this
        omega
      have hYt : Y.termdep = st.termdep := by
        show rst.termdep = st.termdep
        rw [hclkR.2]; exact sttTd
      obtain ⟨perm3, H3⟩ := ih hprog Y (Or.inr ⟨hYt, hYc⟩) cB
        (Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ Y.compileOracle) cc
        ⟨hcB, hdB,
         by show rst.compile = _; rw [← hconR.2.2.2.2.1]; show stt.compile = _; rw [sttComp]; exact hcomp,
         rfl,
         by show WordSimp.gcFunConstOk rst.gcFun; rw [← hconR.1]; show WordSimp.gcFunConstOk stt.gcFun;
            rw [sttGc]; exact hgc⟩
      obtain ⟨P, hP⟩ := hswap perm3 herr
      refine ⟨P, ?_⟩
      have srcRes : evaluate (.call (some (xn, names, xrh, xl1, xl2)) dest args
          (some (hn, hprog, hl1, hl2))) { st with permute := P } = evaluate hprog { Y with permute := perm3 } := by
        rw [srcRun P _ _ hP hz]
        simp only [K]
        rw [if_neg hxl, if_pos (show sptDomainEqUnion ({ rst with permute := perm3 } :
          WordSemStateFiniteExact width C F).locals envs.1 envs.2 from hdu)]
        rfl
      let Mr := Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ rst.compileOracle
      have tgtRes : evaluate (.call (some (xn, names, xrh, xl1, xl2)) dest args
          (some (hn, hprog, hl1, hl2))) T = evaluate hprog { Y with code := cB, compileOracle := Mr, compile := cc } := by
        rw [tgtRun _ _ hB' hz]
        show K (some (.exception x y), { rst with permute := pA, code := cB, compileOracle := Mr, compile := cc }) = _
        simp only [K]
        let Tst : WordSemStateFiniteExact width C F :=
          { rst with permute := pA, code := cB, compileOracle := Mr, compile := cc }
        rw [if_neg hxl, if_pos (show sptDomainEqUnion Tst.locals envs.1 envs.2 from hdu)]
        rfl
      rw [srcRes, tgtRes]
      exact H3

open Classical in
/-- HOL `compile_single_correct`, `Call` case (`word_to_wordProofScript.sml:347-589`), with HOL's
    outer `termdep`/`clock` induction hypothesis (used for the callee body and for the return
    and exception handlers, all run at a smaller clock). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Call {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (st : WordSemStateFiniteExact width C F) (ih : CompileSingleCorrectLowerIH tt kk aa co st) :
    CompileSingleCorrectAt tt kk aa co (.call ret dest args handler) st := by
  cases ret with
  | some r =>
    obtain ⟨xn, names, xrh, xl1, xl2⟩ := r
    exact compileSingleCorrect_callRet tt kk aa co xn names xrh xl1 xl2 dest args handler st ih
  | none =>
    cases handler with
    | none => exact compileSingleCorrect_callTail tt kk aa co dest args st ih
    | some h =>
      intro l coracle cc _
      refine ⟨st.permute, ?_⟩
      have herr : (evaluate (.call none dest args (some h)) st).1 = some .error := by
        rw [evaluate_call_eq]
        split
        · rfl
        · split
          · rfl
          · split <;> rfl
      rcases e : evaluate (.call none dest args (some h)) st with ⟨r, s⟩
      rw [e] at herr
      dsimp only at herr ⊢
      rw [if_pos herr]
      trivial

end Flapjack.Compiler.Backend.WordToWord
