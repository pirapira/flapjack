import Flapjack.Pancake.Proofs.PanToTarget.ConstMemory
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateConsts
import Flapjack.Compiler.Backend.Semantics.WordSem.Semantics
import Flapjack.HolArb

/-! pan_to_targetProofScript.sml 606-778: evaluating a no_alloc/no_install
WordSem program from a state whose memory is replaced by a graph-equal memory
gives the same result and a final state that again differs only by a
graph-equal memory. The recursive core follows the WordSem evaluate recursion
(as HOL's recInduct evaluate_ind). -/
namespace Flapjack.Pancake.Proofs.PanToTarget.MemorySwap
open Flapjack Flapjack.SetSep Flapjack.Pancake.Proofs.PanToTarget.ConstMemory
open Flapjack.WordSemStateFiniteExact Flapjack.WordProps

/-- Canonical WordSem codec for the owning source carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

section Swap
variable {width : Nat} [NeZero width] {C F : Type}

/-- Pointwise agreement of a state's memory with `m` on its domain (Flapjack
form of the graph equality `fun2set (s.memory, s.mdomain) = fun2set (m, s.mdomain)`). -/
def MemEq (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) : Prop :=
  ∀ a, s.mdomain a = true → s.memory a = m a

theorem memEq_iff (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    MemEq s m ↔ fun2Set (s.memory, fun a => s.mdomain a = true) =
      fun2Set (m, fun a => s.mdomain a = true) :=
  (fun2Set_eq_iff _ _ _).symm

/-- Two evaluation results agree up to a graph-equal final memory. -/
def Swap (o o' : Option (WordSemResult width) × WordSemStateFiniteExact width C F) : Prop :=
  ∃ m', o' = (o.1, { o.2 with memory := m' }) ∧ MemEq o.2 m'

theorem swap_map (r : Option (WordSemResult width)) (t : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) (hm : MemEq t m) :
    Swap (r, t) (r, { t with memory := m }) := ⟨m, rfl, hm⟩

private theorem getStoreMem (n : WordStoreHOL) (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) : getStore n { s with memory := m } = getStore n s := rfl

private theorem jumpExcMem (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) :
    jumpExc { s with memory := m } =
      (jumpExc s).map fun x => ({ x.1 with memory := m }, x.2) := by
  unfold jumpExc
  split
  · simp only
    split <;> rfl
  · rfl

set_option linter.unusedSimpArgs false in
/-- Non-recursive statements (Flapjack factoring of memory_swap_lemma1's
non-inductive cases). -/
theorem swap_const (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width)
    (hm : MemEq s m) (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true)
    (hna : noAllocSubprogsHOL p = true) (hni : noInstallSubprogsHOL p = true) :
    Swap (evaluate p s) (evaluate p { s with memory := m }) := by
  have h := (memEq_iff s m).mp hm
  have expEq := wordExpConstMemory s m h
  cases p <;> simp only [wordProgClockConst, Bool.false_eq_true] at hp
  case skip => rw [evaluate, evaluate]; exact swap_map _ _ m hm
  case alloc => simp [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp] at hna
  case install => simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni
  case «break» => rw [evaluate, evaluate]; exact swap_map _ _ m hm
  case «continue» => rw [evaluate, evaluate]; exact swap_map _ _ m hm
  case move =>
    rw [evaluate, evaluate]
    simp only [getVarsConstMemory]
    split <;> (try split) <;> exact swap_map _ _ m hm
  case assign =>
    rw [evaluate, evaluate]
    simp only [expEq]
    split <;> exact swap_map _ _ m hm
  case get =>
    rw [evaluate, evaluate]
    simp only [getStoreMem]
    split <;> exact swap_map _ _ m hm
  case set =>
    rw [evaluate, evaluate]
    simp only [expEq]
    split <;> (try split) <;> exact swap_map _ _ m hm
  case opCurrHeap =>
    rw [evaluate, evaluate]
    simp only [expEq]
    split <;> exact swap_map _ _ m hm
  case «return» =>
    rw [evaluate, evaluate]
    simp only [getVarConstMemory, getVarsConstMemory]
    split <;> exact swap_map _ _ m hm
  case raise =>
    rw [evaluate, evaluate]
    simp only [getVarConstMemory, jumpExcMem]
    split
    · exact swap_map _ _ m hm
    · rename_i w _
      rcases hj : jumpExc s with _ | ⟨s', l1, l2⟩
      · exact swap_map _ _ m hm
      · simp only [Option.map]
        have frame : MemEq s' m := by
          unfold jumpExc at hj
          split at hj
          · split at hj
            · simp only [Option.some.injEq, Prod.mk.injEq] at hj
              obtain ⟨rfl, -, -⟩ := hj
              exact hm
            · cases hj
          · cases hj
        exact swap_map _ _ m frame
  case locValue =>
    rw [evaluate, evaluate]
    split <;> exact swap_map _ _ m hm
  case codeBufferWrite =>
    rw [evaluate, evaluate]
    simp only [getVarConstMemory]
    split <;> (try split) <;> exact swap_map _ _ m hm
  case dataBufferWrite =>
    rw [evaluate, evaluate]
    simp only [getVarConstMemory]
    split <;> (try split) <;> exact swap_map _ _ m hm
  case storeConsts t1 t2 addr offset words =>
    rw [evaluate, evaluate]
    simp only [getVarConstMemory]
    split
    · rename_i a off _ _
      split
      · exact swap_map _ _ m hm
      · refine ⟨wordSemConstWrites a off words m, rfl, ?_⟩
        exact (fun2Set_eq_iff _ _ _).mp
          (constWritesConstMemory a off words s.memory m (fun x => s.mdomain x = true) h)
    · exact swap_map _ _ m hm
  case inst i =>
    rw [evaluate, evaluate]
    have ic := instConstMemory i s m h
    rcases hi : inst i s with _ | x
    · rw [ic.1.mp hi]
      exact swap_map _ _ m hm
    · have hne : inst i s ≠ none := by rw [hi]; simp
      obtain ⟨m', hm', graph⟩ := ic.2 hne
      rcases hi' : inst i { s with memory := m } with _ | y
      · exact absurd (ic.1.mpr hi') hne
      · rw [hi, hi'] at hm'
        rw [hi] at graph
        simp only [holThe] at hm' graph
        subst hm'
        exact ⟨m', rfl, (fun2Set_eq_iff _ _ _).mp graph⟩
  case store exp v =>
    rw [evaluate, evaluate]
    simp only [expEq, getVarConstMemory]
    split
    · rename_i a w _ _
      unfold memStore
      by_cases hd : s.mdomain a = true
      · simp only [hd, if_true]
        refine ⟨fun x => if x = a then w else m x, rfl, ?_⟩
        exact (fun2Set_eq_iff _ _ _).mp (fun2SetUpdateEq s.memory m _ a w h)
      · simp only [hd, Bool.false_eq_true, if_false]
        exact swap_map _ _ m hm
    · exact swap_map _ _ m hm
  case ffi index ptr1 len1 ptr2 len2 names =>
    rw [evaluate, evaluate]
    have rb := fun ptr len => readBytearrayConstMemory s.memory m s.mdomain s.be ptr len h
    simp only [getVarConstMemory, ← rb]
    generalize getVar len1 s = g1
    generalize getVar ptr1 s = g2
    generalize getVar len2 s = g3
    generalize getVar ptr2 s = g4
    rcases g1 with _ | ⟨w | _⟩ <;> try exact swap_map _ _ m hm
    all_goals rcases g2 with _ | ⟨w2 | _⟩ <;> try exact swap_map _ _ m hm
    all_goals rcases g3 with _ | ⟨w3 | _⟩ <;> try exact swap_map _ _ m hm
    all_goals rcases g4 with _ | ⟨w4 | _⟩ <;> try exact swap_map _ _ m hm
    all_goals simp only
    generalize wordSemCutEnv names s.locals = ce
    rcases ce with _ | env
    · exact swap_map _ _ m hm
    simp only
    generalize readBytearrayWordHOL _ _ (memLoadByteAuxExact s.memory s.mdomain s.be) = r1
    generalize readBytearrayWordHOL _ _ (memLoadByteAuxExact s.memory s.mdomain s.be) = r2
    rcases r1 with _ | bytes <;> rcases r2 with _ | bytes2 <;> try exact swap_map _ _ m hm
    simp only
    generalize callFFIHOL s.ffi (.extCall index) bytes bytes2 = cf
    cases cf with
    | final outcome => exact swap_map _ _ m hm
    | ret newFfi newBytes =>
      refine ⟨writeBytearrayExact w4 newBytes m s.mdomain s.be, rfl, ?_⟩
      exact (fun2Set_eq_iff _ _ _).mp
        (writeBytearrayConstMemory m s.mdomain s.be newBytes w4 s.memory h)
  case shareInst op v exp =>
    rw [evaluate, evaluate]
    simp only [expEq]
    split
    · rename_i ad _
      rcases hsh : shareInst (rw := width) op v ad s with ⟨res, t⟩
      have sc := shareInstConstMemory res s op v ad m t ⟨h, hsh⟩
      rw [sc.2.2]
      refine swap_map res t m ?_
      intro a ha
      rw [sc.1]
      exact hm a (sc.2.1 ▸ ha)
    · exact swap_map _ _ m hm

private theorem popEnvMem (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) :
    popEnv { s with memory := m } = (popEnv s).map fun x => { x with memory := m } := by
  unfold popEnv
  dsimp only
  generalize s.stack = st
  rcases st with _ | ⟨⟨m0, e0, e, hd⟩, xs⟩
  · rfl
  · rcases hd with _ | ⟨n, _, _⟩ <;> rfl

private theorem popEnvFrame (s s1 : WordSemStateFiniteExact width C F) (h : popEnv s = some s1) :
    s1.memory = s.memory ∧ s1.mdomain = s.mdomain ∧ s1.code = s.code := by
  unfold popEnv at h
  split at h <;> (try cases h) <;> exact ⟨rfl, rfl, rfl⟩

omit [NeZero width] in
private theorem callRetSub (pred : WordLangProgHOL (BitVec width) → Bool)
    {n : List Nat} {names : WordLangCutsetsHOL} {r : WordLangProgHOL (BitVec width)} {l1 l2 : Nat}
    {dest : Option Nat} {args : List Nat}
    {hd : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)}
    (h : notCreatedSubprogsWithMemOp .load pred (.call (some (n, names, r, l1, l2)) dest args hd) = true) :
    notCreatedSubprogsWithMemOp .load pred r = true := by
  unfold notCreatedSubprogsWithMemOp at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

omit [NeZero width] in
private theorem callHandlerSub (pred : WordLangProgHOL (BitVec width) → Bool)
    {ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)}
    {dest : Option Nat} {args : List Nat} {n : Nat} {hp : WordLangProgHOL (BitVec width)} {l1 l2 : Nat}
    (h : notCreatedSubprogsWithMemOp .load pred (.call ret dest args (some (n, hp, l1, l2))) = true) :
    notCreatedSubprogsWithMemOp .load pred hp = true := by
  unfold notCreatedSubprogsWithMemOp at h
  simp only [Bool.and_eq_true] at h
  exact h.2.2

set_option linter.unusedSimpArgs false in
/-- Recursive core of memory_swap_lemma1, by recursion on HOL's evaluate
termination measure (as HOL's recInduct evaluate_ind). -/
theorem swap_evaluate :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (m : BitVec width → WordLocW width),
      noAllocSubprogsHOL p = true → noInstallSubprogsHOL p = true →
      noAllocCode s.code → noInstallCode s.code → MemEq s m →
      Swap (evaluate p s) (evaluate p { s with memory := m })
  | .tick, s, m, _, _, _, _, hm => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      split <;> exact swap_map _ _ m hm
  | .mustTerminate q, s, m, hna, hni, hac, hic, hm => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.true_and] at hna hni
      by_cases hz : s.termdep = 0
      · rw [if_pos hz, if_pos hz]
        exact swap_map _ _ m hm
      · rw [if_neg hz, if_neg hz]
        have ih := swap_evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } m hna hni hac hic hm
        obtain ⟨m', eq, mem⟩ := ih
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at eq mem
        have eq' : evaluate q { { s with memory := m } with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } = (r, { s1 with memory := m' }) := eq
        rw [eq']
        cases r with
        | none => exact ⟨m', rfl, mem⟩
        | some x => cases x <;> first | exact swap_map _ _ m hm | exact ⟨m', rfl, mem⟩
  | .seq c1 c2, s, m, hna, hni, hac, hic, hm => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      have hna' := hna
      have hni' := hni
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.and_eq_true] at hna' hni'
      obtain ⟨m1, eq1, mem1⟩ := swap_evaluate c1 s m hna'.1 hni'.1 hac hic hm
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at eq1 mem1
      rw [eq1]
      have hc1 := evaluate_clock c1 s r1 s1 h1
      have code1 : s.code = s1.code :=
        noInstallEvaluateConstCode c1 s r1 s1 ⟨h1, hni'.1, hic⟩
      cases r1 with
      | none =>
        exact swap_evaluate c2 s1 m1 hna'.2 hni'.2 (code1 ▸ hac) (code1 ▸ hic) mem1
      | some x => exact ⟨m1, rfl, mem1⟩
  | .ite cmp r1 ri c1 c2, s, m, hna, hni, hac, hic, hm => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      simp only [getVarConstMemory, getVarImmConstMemory]
      have hna' := hna
      have hni' := hni
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.and_eq_true] at hna' hni'
      rcases WordSemStateFiniteExact.getVar r1 s with _ | x <;>
        rcases WordSemStateFiniteExact.getVarImm ri s with _ | y <;> simp only <;>
        try exact swap_map _ _ m hm
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only
      · exact swap_map _ _ m hm
      · exact swap_evaluate c2 s m hna'.2 hni'.2 hac hic hm
      · exact swap_evaluate c1 s m hna'.1 hni'.1 hac hic hm
  | .loop names c exitNames, s, m, hna, hni, hac, hic, hm => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      have hna' := hna
      have hni' := hni
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hna' hni'
      rw [cutStateWithMemConst (names, .ln) s m]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · exact swap_map _ _ m hm
      simp only [Option.map]
      obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      obtain ⟨m1, eq1, mem1⟩ := swap_evaluate c { s with locals := l } m hna' hni' hac hic hm
      rcases hb : evaluate c { s with locals := l } with ⟨rb, s1⟩
      rw [hb] at eq1 mem1
      dsimp only at eq1 mem1
      rw [eq1]
      dsimp only
      have hcl := evaluate_clock c _ rb s1 hb
      have code1 : s.code = s1.code :=
        noInstallEvaluateConstCode c { s with locals := l } rb s1 ⟨hb, hni', hic⟩
      by_cases hcont : wordSemContLoop rb = true
      · rw [if_pos hcont, if_pos hcont]
        by_cases hz : s1.clock = 0
        · rw [if_pos hz]
          split
          · exact ⟨m1, rfl, mem1⟩
          · rename_i hz'; exact absurd hz hz'
        · rw [if_neg hz]
          split
          · rename_i hz'; exact absurd hz' hz
          simp only [wordSemSTOP]
          exact swap_evaluate (.loop names c exitNames) (decClock s1) m1 hna hni
            (code1 ▸ hac) (code1 ▸ hic) mem1
      · rw [if_neg hcont, if_neg hcont]
        split
        · rw [cutStateWithMemConst (exitNames, .ln) s1 m1]
          rcases hce : cutState (exitNames, .ln) s1 with _ | s2
          · exact ⟨m1, rfl, mem1⟩
          · simp only [Option.map]
            obtain ⟨l2, rfl⟩ := cutStateConst _ _ _ hce
            exact ⟨m1, rfl, mem1⟩
        · exact ⟨m1, rfl, mem1⟩
  | .call ret dest args handler, s, m, hna, hni, hac, hic, hm => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht, ht]
      simp only [getVarsConstMemory]
      rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
      · exact swap_map _ _ m hm
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · rw [if_pos hbad, if_pos hbad]
        exact swap_map _ _ m hm
      rw [if_neg hbad, if_neg hbad]
      try dsimp only
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · exact swap_map _ _ m hm
      simp only
      have hprogA := noAllocFindCode s.code dest _ _ _ prog _ ⟨hf, hac⟩
      have hprogI := noInstallFindCode s.code dest _ _ _ prog _ ⟨hic, hf⟩
      cases ret with
      | none =>
        cases handler with
        | some _ => exact swap_map _ _ m hm
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · rw [if_pos hz, if_pos hz]
            exact swap_map _ _ m hm
          rw [if_neg hz, if_neg hz]
          have e : WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock { s with memory := m }) =
              { WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock s) with memory := m } := rfl
          rw [e]
          obtain ⟨m2, eq2, mem2⟩ :=
            swap_evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock s)) m hprogA hprogI hac hic hm
          rcases hcv : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock s)) with ⟨rc, sc⟩
          rw [hcv] at eq2 mem2
          dsimp only at eq2 mem2
          rw [eq2]
          dsimp only
          split <;> exact ⟨m2, rfl, mem2⟩
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · rw [if_pos hdc, if_pos hdc]
          exact swap_map _ _ m hm
        rw [if_neg hdc, if_neg hdc]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · exact swap_map _ _ m hm
        simp only
        have epush : ∀ t : WordSemStateFiniteExact width C F,
            WordSemStateFiniteExact.pushEnv envs handler { t with memory := m } = { WordSemStateFiniteExact.pushEnv envs handler t with memory := m } :=
          fun t => pushEnvMemUpd m envs handler t
        by_cases hz : s.clock = 0
        · rw [if_pos hz, if_pos hz, epush s]
          exact swap_map _ _ m hm
        rw [if_neg hz, if_neg hz]
        have e : WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock { s with memory := m })) =
            { WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock s)) with memory := m } := by
          rw [show WordSemStateFiniteExact.decClock { s with memory := m } = { WordSemStateFiniteExact.decClock s with memory := m } from rfl,
            epush]
          rfl
        rw [e]
        have pushConst := pushEnvMemConst envs handler (WordSemStateFiniteExact.decClock s)
        have hpre : (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock s))).code = s.code :=
          code_pushEnv envs handler _
        have hm0 : MemEq (WordSemStateFiniteExact.callEnv args1 ss
            (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock s))) m := by
          intro a ha
          have hd : (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs
              handler (WordSemStateFiniteExact.decClock s))).mdomain = s.mdomain := pushConst.2
          have hme : (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs
              handler (WordSemStateFiniteExact.decClock s))).memory = s.memory := pushConst.1
          rw [hme]
          exact hm a (hd ▸ ha)
        obtain ⟨m2, eq2, mem2⟩ :=
          swap_evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock s))) m hprogA hprogI
            (hpre ▸ hac) (hpre ▸ hic) hm0
        rcases hcv : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at eq2 mem2
        dsimp only at eq2 mem2
        rw [eq2]
        try dsimp only
        have hcl := evaluate_clock prog _ rc s2 hcv
        have code2 : s2.code = s.code :=
          (noInstallEvaluateConstCode prog _ rc s2 ⟨hcv, hprogI, hpre ▸ hic⟩).symm.trans hpre
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        all_goals try dsimp only
        · exact ⟨m2, rfl, mem2⟩
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · rw [if_pos hx, if_pos hx]
            exact ⟨m2, rfl, mem2⟩
          rw [if_neg hx, if_neg hx]
          rw [popEnvMem s2 m2]
          rcases hp : WordSemStateFiniteExact.popEnv s2 with _ | s1
          · exact ⟨m2, rfl, mem2⟩
          simp only [Option.map]
          obtain ⟨fm, fd, fc⟩ := popEnvFrame s2 s1 hp
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          have mem1 : MemEq s1 m2 := by
            intro a ha; rw [fm]; exact mem2 a (fd ▸ ha)
          by_cases hdu : sptDomainEqUnion s1.locals envs.1 envs.2
          · simp only [hdu, ↓reduceIte]
            · have e2 : WordSemStateFiniteExact.setVars n ys { s1 with memory := m2 } = { WordSemStateFiniteExact.setVars n ys s1 with memory := m2 } := rfl
              rw [e2]
              have code1 : s1.code = s.code := fc.trans code2
              unfold noAllocSubprogsHOL at hna
              unfold noInstallSubprogsHOL at hni
              exact swap_evaluate retHandler (WordSemStateFiniteExact.setVars n ys s1) m2 (callRetSub _ hna) (callRetSub _ hni)
                (code1 ▸ hac) (code1 ▸ hic) mem1
          · simp only [hdu, ↓reduceIte]
            exact ⟨m2, rfl, mem1⟩
        · cases handler with
          | none => exact ⟨m2, rfl, mem2⟩
          | some hv =>
            obtain ⟨n', hprog', l1', l2'⟩ := hv
            simp only
            by_cases hx : x ≠ WordLocW.loc l1' l2'
            · rw [if_pos hx, if_pos hx]
              exact ⟨m2, rfl, mem2⟩
            rw [if_neg hx, if_neg hx]
            by_cases hdu : sptDomainEqUnion s2.locals envs.1 envs.2
            · simp only [hdu, ↓reduceIte]
              · have e2 : WordSemStateFiniteExact.setVar n' y { s2 with memory := m2 } = { WordSemStateFiniteExact.setVar n' y s2 with memory := m2 } := rfl
                rw [e2]
                unfold noAllocSubprogsHOL at hna
                unfold noInstallSubprogsHOL at hni
                exact swap_evaluate hprog' (WordSemStateFiniteExact.setVar n' y s2) m2 (callHandlerSub _ hna)
                  (callHandlerSub _ hni) (code2 ▸ hac) (code2 ▸ hic) mem2
            · simp only [hdu, ↓reduceIte]
              exact ⟨m2, rfl, mem2⟩
        all_goals exact ⟨m2, rfl, mem2⟩
  | .skip, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .move a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .inst a, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .assign a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .get a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .set a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .store a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .alloc a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .storeConsts a b c d f, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .raise a, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | WordLangProgHOL.return a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | WordLangProgHOL.break a, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | WordLangProgHOL.continue a, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .opCurrHeap a b c, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .locValue a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .install a b c d f, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .codeBufferWrite a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .dataBufferWrite a b, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .ffi a b c d f g, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
  | .shareInst a b c, s, m, hna, hni, _, _, hm => swap_const s m hm _ rfl hna hni
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc1 with ⟨_, _⟩)
    try (rcases hcl with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.pushEnv_clock, WordSemStateFiniteExact.pushEnv_termdep, true_and] at *
    omega

end Swap

/-- Original local memory_swap_lemma1 (607-736): for a no_alloc/no_install
program run from a state with no_alloc/no_install code, replacing the memory by
a graph-equal one gives the same result and a final state equal up to memory
(compared by overwriting memory with HOL's ARB, holArb) whose memory is again
graph-equal. Proof by the WordSem evaluate recursion (swap_evaluate). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "memory_swap_lemma1"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memorySwapLemma1 {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F)
      (m : BitVec width → WordLocW width),
      evaluate prog st = (res, rst) ∧
        fun2Set (st.memory, fun a => st.mdomain a = true) =
          fun2Set (m, fun a => st.mdomain a = true) ∧
        noAllocCode st.code ∧ noInstallCode st.code ∧
        noAllocSubprogsHOL prog = true ∧ noInstallSubprogsHOL prog = true →
      ∃ st' : WordSemStateFiniteExact width C F,
        evaluate prog { st with memory := m } = (res, st') ∧
        { st' with memory := @holArb (BitVec width → WordLocW width) ⟨fun _ => .word 0⟩ } =
          { rst with memory := @holArb (BitVec width → WordLocW width) ⟨fun _ => .word 0⟩ } ∧
        fun2Set (rst.memory, fun a => rst.mdomain a = true) =
          fun2Set (st'.memory, fun a => rst.mdomain a = true) := by
  intro prog st res rst m ⟨run, graph, hac, hic, hna, hni⟩
  obtain ⟨m', eq, mem⟩ := swap_evaluate prog st m hna hni hac hic ((memEq_iff st m).mpr graph)
  rw [run] at eq mem
  exact ⟨_, eq, rfl, (memEq_iff rst m').mp mem⟩

/-- Original local memory_swap_lemma (743-760), the rephrased form with an
explicit final memory. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "memory_swap_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memorySwapLemma {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F)
      (m : BitVec width → WordLocW width),
      evaluate prog st = (res, rst) ∧
        fun2Set (st.memory, fun a => st.mdomain a = true) =
          fun2Set (m, fun a => st.mdomain a = true) ∧
        noAllocCode st.code ∧ noInstallCode st.code ∧
        noAllocSubprogsHOL prog = true ∧ noInstallSubprogsHOL prog = true →
      ∃ m' : BitVec width → WordLocW width,
        evaluate prog { st with memory := m } = (res, { rst with memory := m' }) ∧
        fun2Set (rst.memory, fun a => rst.mdomain a = true) =
          fun2Set (m', fun a => rst.mdomain a = true) := by
  intro prog st res rst m ⟨run, graph, hac, hic, hna, hni⟩
  obtain ⟨m', eq, mem⟩ := swap_evaluate prog st m hna hni hac hic ((memEq_iff st m).mpr graph)
  rw [run] at eq mem
  exact ⟨m', eq, (memEq_iff rst m').mp mem⟩

/-- Full original word_semantics_memory_update (772-907): with graph-equal
memory and no_alloc/no_install code, a non-Fail semantics of the memory-updated
state equals the semantics of the original state. At every clock the entry
call runs to the same result and an FFI-equal final state (memory_swap), so
the fail guard, the termination choice and the divergence trace coincide; the
non-Fail premise is kept as in HOL. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_semantics_memory_update"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordSemanticsMemoryUpdate {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) (start : Nat)
    (h : fun2Set (s.memory, fun a => s.mdomain a = true) =
        fun2Set (m, fun a => s.mdomain a = true) ∧
      noAllocCode s.code ∧ noInstallCode s.code) :
    semantics { s with memory := m } start ≠ .fail →
      semantics s start = semantics { s with memory := m } start := by
  intro _
  obtain ⟨graph, hac, hic⟩ := h
  have hm := (memEq_iff s m).mpr graph
  have key : ∀ k, ∃ m', evaluate (.call none (some start) [0] none) { { s with memory := m } with clock := k } =
      ((evaluate (.call none (some start) [0] none) { s with clock := k }).1,
        { (evaluate (.call none (some start) [0] none) { s with clock := k }).2 with memory := m' }) := by
    intro k
    obtain ⟨m', eq, _⟩ := swap_evaluate (.call none (some start) [0] none) { s with clock := k } m
      rfl rfl hac hic hm
    exact ⟨m', eq⟩
  choose f hf using key
  dsimp only at hf
  unfold semantics
  dsimp only
  simp only [hf]
  try dsimp only
  congr 1
  case e_c =>
    apply propext
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hf k]; exact hk⟩
    · rintro ⟨k, hk⟩
      rw [hf k] at hk
      exact ⟨k, hk⟩
  case e_e =>
    congr 1
    congr 1
    funext b
    apply propext
    constructor
    · rintro ⟨k, t, r, o, he, hmatch, rfl⟩
      refine ⟨k, { t with memory := f k }, r, o, ?_, hmatch, rfl⟩
      rw [he]
    · rintro ⟨k, t, r, o, he, hmatch, rfl⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨k, _, _, o, rfl, hmatch, rfl⟩

end Flapjack.Pancake.Proofs.PanToTarget.MemorySwap
