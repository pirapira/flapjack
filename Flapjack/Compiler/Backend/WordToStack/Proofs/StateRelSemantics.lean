import Flapjack.Compiler.Backend.Semantics.WordSem.Semantics
import Flapjack.Compiler.Backend.Semantics.StackSem.Semantics
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClockIoEventsMono
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClockIoEventsMono
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Results
import Flapjack.Compiler.Backend.WordToStack.Proofs.SemanticsHelpers
import Flapjack.SemanticsProps.Implements
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCall

/-! Observational layer of the original Word-to-Stack proof
(word_to_stackProofScript.sml 10154-10372, state_rel_IMP_semantics). The
helpers below reason about the clock-indexed entry-call families of the
native WordSem and StackSem semantics. Every untagged declaration here is
Flapjack-local factoring of the original state_rel_IMP_semantics /
state_rel_IMP_semantics' proofs (HOL proves these steps inline) and has no
separate HOL declaration; the per-clock EntrySimulation is derived from the
original comp_Call by entrySimulationOfStateRel, never assumed by a tagged
theorem. -/
namespace Flapjack.WordToStackProofs.StateRelSemantics
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.WordToStackProofs.CompCorrect

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

variable {width : Nat} [NeZero width] {C F : Type}

/-- The source entry call at a fixed clock (local naming). -/
noncomputable abbrev wordEntry (s : WordSemStateFiniteExact width (Nat × C) F) (start k : Nat) :=
  WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) {s with clock := k}

/-- The target entry call at a fixed clock (local naming). -/
noncomputable abbrev stackEntry (t : StackSemStateFiniteExact width C F) (start k : Nat) :=
  StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := k})

/-- Per-clock entry simulation, the shape of the original comp_Call
conclusion at every source clock. Local factoring; the tagged theorem derives
it from comp_Call. -/
def EntrySimulation (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (start : Nat) : Prop :=
  ∀ k res s1, wordEntry s start k = (res, s1) → res ≠ some .error →
    ∃ ck res1 t1, stackEntry t start (k + ck) = (res1, t1) ∧
      (res.map compileResult = res1 ∧ s1.ffi = t1.ffi ∨
        res.map compileResult ≠ res1 ∧ res1 = some (.halt (.word 2)) ∧
          t1.ffi.ioEvents <+: s1.ffi.ioEvents ∧
          s1.stackMax.getD (s1.stackLimit + 1) > s1.stackLimit)

/-- Source results excluded by the WordSem fail guard. -/
def wordBad (r : Option (WordSemResult width)) : Prop :=
  match r with
  | some (.exception _ _) => True
  | some (.result ret _) => ret ≠ WordLocW.loc 1 0
  | some .error => True
  | none => True
  | _ => False

/-- Target results excluded by the StackSem fail guard. -/
def stackBad (r : Option (StackSemResult width)) : Prop :=
  r ≠ some .timeOut ∧ r ≠ some (.result (.loc 1 0)) ∧
    (∀ w, r ≠ some (.halt (.word w))) ∧ ∀ e, r ≠ some (.finalFFI e)

theorem sourceNotBad (s : WordSemStateFiniteExact width (Nat × C) F) (start : Nat)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail) (k : Nat) :
    ¬ wordBad (wordEntry s start k).1 := by
  intro bad
  apply notFail
  unfold WordSemStateFiniteExact.semantics
  rw [if_pos ⟨k, bad⟩]

theorem wordEntryAddClock (s : WordSemStateFiniteExact width (Nat × C) F) (start k extra : Nat)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (run : wordEntry s start k = (res, s1)) (notTimeOut : res ≠ some .timeOut) :
    wordEntry s start (k + extra) = (res, {s1 with clock := s1.clock + extra}) := by
  have h := WordSemStateFiniteExact.evaluate_add_clock extra _ _ res s1 ⟨run, notTimeOut⟩
  simpa only [wordEntry] using h

theorem stackEntryAddClock (t : StackSemStateFiniteExact width C F) (start k extra : Nat)
    (res : Option (StackSemResult width)) (t1 : StackSemStateFiniteExact width C F)
    (run : stackEntry t start k = (res, t1)) (notTimeOut : res ≠ some .timeOut) :
    stackEntry t start (k + extra) = (res, {t1 with clock := t1.clock + extra}) := by
  have h := Compiler.Backend.StackProps.evaluateAddClock extra _ _ res t1 ⟨run, notTimeOut⟩
  simpa only [stackEntry] using h

theorem wordEntryEventsMono (s : WordSemStateFiniteExact width (Nat × C) F) (start k1 k2 : Nat)
    (le : k1 ≤ k2) :
    (wordEntry s start k1).2.ffi.ioEvents <+: (wordEntry s start k2).2.ffi.ioEvents := by
  have h := WordSemStateFiniteExact.evaluate_add_clock_io_events_mono
    (.call none (some start) [0] none) {s with clock := k1} (k2 - k1)
  simpa only [wordEntry, Nat.add_sub_of_le le] using h

theorem stackEntryEventsMono (t : StackSemStateFiniteExact width C F) (start k1 k2 : Nat)
    (le : k1 ≤ k2) :
    (stackEntry t start k1).2.ffi.ioEvents <+: (stackEntry t start k2).2.ffi.ioEvents := by
  have h := Compiler.Backend.StackProps.EvaluateAddClockIoEventsMono.evaluateAddClockIoEventsMono
    (k2 - k1) (.call none (.inl start) none) {t with clock := k1}
  simpa only [stackEntry, Nat.add_sub_of_le le] using h

/-- A source entry result allowed by the WordSem fail guard (and by the
actual tail-call evaluator, which never returns Break/Continue). -/
theorem sourceResultCases (s : WordSemStateFiniteExact width (Nat × C) F) (start k : Nat)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail) :
    (wordEntry s start k).1 = some .timeOut ∨
      (∃ ys, (wordEntry s start k).1 = some (.result (.loc 1 0) ys)) ∨
      (wordEntry s start k).1 = some .notEnoughSpace ∨
      ∃ e, (wordEntry s start k).1 = some (.finalFfi e) := by
  have good := sourceNotBad s start notFail k
  rcases run : wordEntry s start k with ⟨res, s1⟩
  have noLoop := SemanticsHelpers.wordCallNoneNotBreakContinue (some start) [0] none
    {s with clock := k} s1 res run
  rw [run] at good
  simp only
  rcases res with _ | r
  · exact absurd trivial good
  · cases r with
    | result ret ys =>
      by_cases h : ret = .loc 1 0
      · exact Or.inr (Or.inl ⟨ys, by rw [h]⟩)
      · exact absurd h good
    | exception _ _ => exact absurd trivial good
    | «break» n => exact absurd rfl (noLoop.1 n)
    | «continue» n => exact absurd rfl (noLoop.2 n)
    | timeOut => exact Or.inl rfl
    | notEnoughSpace => exact Or.inr (Or.inr (Or.inl rfl))
    | finalFfi e => exact Or.inr (Or.inr (Or.inr ⟨e, rfl⟩))
    | error => exact absurd trivial good

theorem sourceNotError (s : WordSemStateFiniteExact width (Nat × C) F) (start k : Nat)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail) :
    (wordEntry s start k).1 ≠ some .error := by
  rcases sourceResultCases s start k notFail with h | ⟨ys, h⟩ | h | ⟨e, h⟩ <;> rw [h] <;> simp

/-- Target entry runs that are not time-outs coincide with the simulated run
of the same source clock. -/
theorem targetAgreesWithSimulation (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (start k : Nat)
    (sim : EntrySimulation s t start)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail)
    (r : Option (StackSemResult width)) (t' : StackSemStateFiniteExact width C F)
    (targetRun : stackEntry t start k = (r, t')) (notTimeOut : r ≠ some .timeOut) :
    ∃ res s1, wordEntry s start k = (res, s1) ∧
      (res.map compileResult = r ∧ s1.ffi = t'.ffi ∨
        res.map compileResult ≠ r ∧ r = some (.halt (.word 2)) ∧
          t'.ffi.ioEvents <+: s1.ffi.ioEvents ∧
          s1.stackMax.getD (s1.stackLimit + 1) > s1.stackLimit) := by
  rcases sourceRun : wordEntry s start k with ⟨res, s1⟩
  have notError := sourceNotError s start k notFail
  rw [sourceRun] at notError
  obtain ⟨ck, res1, t1, simRun, outcome⟩ := sim k res s1 sourceRun notError
  have boosted := stackEntryAddClock t start k ck r t' targetRun notTimeOut
  rw [simRun] at boosted
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj boosted
  exact ⟨res, s1, rfl, by simpa only using outcome⟩

theorem targetNotBad (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (start : Nat)
    (sim : EntrySimulation s t start)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail) (k : Nat) :
    ¬ stackBad (stackEntry t start k).1 := by
  intro bad
  rcases targetRun : stackEntry t start k with ⟨r, t'⟩
  rw [targetRun] at bad
  obtain ⟨res, s1, sourceRun, outcome⟩ :=
    targetAgreesWithSimulation s t start k sim notFail r t' targetRun bad.1
  rcases outcome with ⟨same, _⟩ | ⟨_, halt, _⟩
  · have cases := sourceResultCases s start k notFail
    rw [sourceRun] at cases
    rcases cases with h | ⟨ys, h⟩ | h | ⟨e, h⟩ <;> subst h <;> subst same
    · exact bad.1 rfl
    · exact bad.2.1 rfl
    · exact bad.2.2.1 1 rfl
    · exact bad.2.2.2 e rfl
  · exact bad.2.2.1 2 halt

/-- The exact source termination-choice predicate of WordSem semantics. -/
def sourceTermination (s : WordSemStateFiniteExact width (Nat × C) F) (start : Nat)
    (b : HolBehaviour) : Prop :=
  ∃ k t r outcome,
    WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) {s with clock := k} =
      (r, t) ∧
    (match r with
     | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
     | some (.result _ _) => outcome = HolOutcome.success
     | some .notEnoughSpace => outcome = HolOutcome.resourceLimitHit
     | _ => False) ∧
    b = HolBehaviour.terminate outcome t.ffi.ioEvents

/-- The exact target termination-choice predicate of StackSem semantics. -/
def targetTermination (t : StackSemStateFiniteExact width C F) (start : Nat)
    (b : HolBehaviour) : Prop :=
  ∃ k t' r outcome,
    StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := k}) = (some r, t') ∧
    (match r with
     | .finalFFI e => outcome = HolOutcome.ffiOutcome e
     | .halt w => outcome =
         if w = .word 0 then HolOutcome.success else HolOutcome.resourceLimitHit
     | .result _ => outcome = HolOutcome.success
     | _ => False) ∧
    b = HolBehaviour.terminate outcome t'.ffi.ioEvents

/-- The source clock family of divergent semantics. -/
def sourceFamily (s : WordSemStateFiniteExact width (Nat × C) F) (start : Nat)
    (l : HolLList HolIoEvent) : Prop :=
  ∃ k, l = HolLList.fromList (wordEntry s start k).2.ffi.ioEvents

/-- The target clock family of divergent semantics. -/
def targetFamily (t : StackSemStateFiniteExact width C F) (start : Nat)
    (l : HolLList HolIoEvent) : Prop :=
  ∃ k, l = HolLList.fromList (stackEntry t start k).2.ffi.ioEvents

theorem sourceSemanticsEq (s : WordSemStateFiniteExact width (Nat × C) F) (start : Nat)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail) :
    WordSemStateFiniteExact.semantics s start =
      match holOptionSome (sourceTermination s start) with
      | some res => res
      | none => .diverge (HolLList.buildLprefixLub (sourceFamily s start)) := by
  have notBad : ¬ ∃ k, wordBad (wordEntry s start k).1 := fun ⟨k, h⟩ =>
    sourceNotBad s start notFail k h
  unfold WordSemStateFiniteExact.semantics
  dsimp only
  split
  · rename_i bad
    exact absurd bad notBad
  · rfl

theorem targetSemanticsEq (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (start : Nat)
    (sim : EntrySimulation s t start)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail) :
    StackSemEvaluate.semantics start t =
      match holOptionSome (targetTermination t start) with
      | some res => res
      | none => .diverge (HolLList.buildLprefixLub (targetFamily t start)) := by
  have notBad : ¬ ∃ k, stackBad (stackEntry t start k).1 := fun ⟨k, h⟩ =>
    targetNotBad s t start sim notFail k h
  unfold StackSemEvaluate.semantics
  dsimp only
  split
  · rename_i bad
    exact absurd bad notBad
  · rfl

theorem sourceTerminationUnique (s : WordSemStateFiniteExact width (Nat × C) F) (start : Nat)
    (b1 b2 : HolBehaviour) (h1 : sourceTermination s start b1)
    (h2 : sourceTermination s start b2) : b2 = b1 := by
  obtain ⟨k1, t1, r1, o1, run1, m1, rfl⟩ := h1
  obtain ⟨k2, t2, r2, o2, run2, m2, rfl⟩ := h2
  wlog le : k1 ≤ k2 generalizing k1 t1 r1 o1 k2 t2 r2 o2
  · exact (this k2 t2 r2 o2 run2 m2 k1 t1 r1 o1 run1 m1 (by omega)).symm
  have notTimeOut : r1 ≠ some .timeOut := by
    rintro rfl
    exact m1
  have boosted := wordEntryAddClock s start k1 (k2 - k1) r1 t1 run1 notTimeOut
  rw [Nat.add_sub_of_le le] at boosted
  rw [wordEntry, run2] at boosted
  obtain ⟨sameResult, samePost⟩ := Prod.mk.inj boosted
  subst sameResult samePost
  rcases r2 with _ | x
  · exact m2.elim
  · cases x <;> simp_all

theorem sourceFamilyChain (s : WordSemStateFiniteExact width (Nat × C) F) (start : Nat) :
    HolLList.lprefixChain (sourceFamily s start) := by
  rintro first second ⟨k1, rfl⟩ ⟨k2, rfl⟩
  rcases Nat.le_total k1 k2 with le | le
  · exact Or.inl ((HolLList.lprefix_fromList _ _).mpr (wordEntryEventsMono s start k1 k2 le))
  · exact Or.inr ((HolLList.lprefix_fromList _ _).mpr (wordEntryEventsMono s start k2 k1 le))

theorem targetFamilyChain (t : StackSemStateFiniteExact width C F) (start : Nat) :
    HolLList.lprefixChain (targetFamily t start) := by
  rintro first second ⟨k1, rfl⟩ ⟨k2, rfl⟩
  rcases Nat.le_total k1 k2 with le | le
  · exact Or.inl ((HolLList.lprefix_fromList _ _).mpr (stackEntryEventsMono t start k1 k2 le))
  · exact Or.inr ((HolLList.lprefix_fromList _ _).mpr (stackEntryEventsMono t start k2 k1 le))

/-- A terminating target entry result yields a target termination witness. -/
private theorem targetWitness (t : StackSemStateFiniteExact width C F) (start k : Nat)
    (r : StackSemResult width) (t1 : StackSemStateFiniteExact width C F)
    (run : stackEntry t start k = (some r, t1))
    (terminating : (∃ e, r = .finalFFI e) ∨ (∃ w, r = .halt w) ∨ ∃ v, r = .result v) :
    ∃ b, targetTermination t start b := by
  rcases terminating with ⟨e, rfl⟩ | ⟨w, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨_, k, t1, _, _, run, rfl, rfl⟩
  · exact ⟨_, k, t1, _, _, run, rfl, rfl⟩
  · exact ⟨_, k, t1, _, _, run, rfl, rfl⟩

/-- Every terminating source run gives a terminating target run. -/
private theorem targetTerminatesOfSource (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (start : Nat)
    (sim : EntrySimulation s t start)
    (_notFail : WordSemStateFiniteExact.semantics s start ≠ .fail)
    (b : HolBehaviour) (h : sourceTermination s start b) :
    ∃ b', targetTermination t start b' := by
  obtain ⟨k, s1, r, o, run, m, -⟩ := h
  have notError : r ≠ some .error := by
    rintro rfl
    exact m
  obtain ⟨ck, res1, t1, simRun, outcome⟩ := sim k r s1 run notError
  rcases outcome with ⟨same, _⟩ | ⟨_, halt, _⟩
  · subst same
    rcases r with _ | x
    · exact m.elim
    · cases x with
      | result v _ => exact targetWitness t start (k + ck) _ t1 simRun (Or.inr (Or.inr ⟨v, rfl⟩))
      | notEnoughSpace => exact targetWitness t start (k + ck) _ t1 simRun (Or.inr (Or.inl ⟨_, rfl⟩))
      | finalFfi e => exact targetWitness t start (k + ck) _ t1 simRun (Or.inl ⟨e, rfl⟩)
      | _ => exact m.elim
  · subst halt
    exact targetWitness t start (k + ck) _ t1 simRun (Or.inr (Or.inl ⟨_, rfl⟩))

private theorem holOptionSome_eq_none {α : Type} {P : α → Prop} (h : ∀ x, ¬ P x) :
    holOptionSome P = none := by
  unfold holOptionSome
  rw [dif_neg (fun ⟨x, hx⟩ => h x hx)]

/-- When the target has no termination witness, the source diverges with the
same trace limit. -/
theorem divergentEq (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (start : Nat)
    (sim : EntrySimulation s t start)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail)
    (noTarget : ∀ b, ¬ targetTermination t start b) :
    HolBehaviour.diverge (HolLList.buildLprefixLub (targetFamily t start)) =
      WordSemStateFiniteExact.semantics s start := by
  have noSource : ∀ b, ¬ sourceTermination s start b := fun b h => by
    obtain ⟨b', h'⟩ := targetTerminatesOfSource s t start sim notFail b h
    exact noTarget b' h'
  rw [sourceSemanticsEq s start notFail, holOptionSome_eq_none noSource]
  dsimp only
  congr 1
  -- every source run is matched by an event-equal simulated target run
  have matched : ∀ k, ∃ ck, (wordEntry s start k).2.ffi.ioEvents =
      (stackEntry t start (k + ck)).2.ffi.ioEvents := by
    intro k
    rcases run : wordEntry s start k with ⟨res, s1⟩
    have notError := sourceNotError s start k notFail
    rw [run] at notError
    obtain ⟨ck, res1, t1, simRun, outcome⟩ := sim k res s1 run notError
    refine ⟨ck, ?_⟩
    rw [simRun]
    rcases outcome with ⟨_, ffi⟩ | ⟨_, halt, _⟩
    · exact congrArg (fun f => HolFfiState.ioEvents f) ffi
    · subst halt
      exact (noTarget _ (Classical.choose_spec
        (targetWitness t start (k + ck) _ t1 simRun (Or.inr (Or.inl ⟨_, rfl⟩))))).elim
  apply HolLList.IMP_build_lprefix_lub_EQ (targetFamilyChain t start) (sourceFamilyChain s start)
  · rintro l ⟨k, rfl⟩
    obtain ⟨ck, eq⟩ := matched k
    refine ⟨_, ⟨k, rfl⟩, (HolLList.lprefix_fromList _ _).mpr ?_⟩
    rw [eq]
    exact stackEntryEventsMono t start k (k + ck) (Nat.le_add_right k ck)
  · rintro l ⟨k, rfl⟩
    obtain ⟨ck, eq⟩ := matched k
    refine ⟨_, ⟨k + ck, rfl⟩, (HolLList.lprefix_fromList _ _).mpr ?_⟩
    rw [eq]

/-- A target termination that agrees with the source run at the same clock
is the source semantics. -/
theorem sameTermination (s : WordSemStateFiniteExact width (Nat × C) F)
    (start k : Nat)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail)
    (r : StackSemResult width) (t' : StackSemStateFiniteExact width C F) (o : HolOutcome)
    (m : match r, o with
      | .finalFFI e, outcome => outcome = HolOutcome.ffiOutcome e
      | .halt w, outcome =>
          outcome = if w = .word 0 then HolOutcome.success else HolOutcome.resourceLimitHit
      | .result _, outcome => outcome = HolOutcome.success
      | _, _ => False)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (sourceRun : wordEntry s start k = (res, s1))
    (same : res.map compileResult = some r) (ffi : s1.ffi = t'.ffi) :
    HolBehaviour.terminate o t'.ffi.ioEvents = WordSemStateFiniteExact.semantics s start := by
  have witness : sourceTermination s start (.terminate o t'.ffi.ioEvents) := by
    refine ⟨k, s1, res, o, sourceRun, ?_, by rw [ffi]⟩
    rcases res with _ | x
    · cases same
    · cases x with
      | result v ys =>
        cases same
        exact m
      | notEnoughSpace =>
        cases same
        simpa [compileResult, NeZero.ne width] using m
      | finalFfi e =>
        cases same
        exact m
      | exception v p =>
        cases same
        exact m.elim
      | «break» n =>
        cases same
        exact m.elim
      | «continue» n =>
        cases same
        exact m.elim
      | timeOut =>
        cases same
        exact m.elim
      | error =>
        cases same
        exact m.elim
  rw [sourceSemanticsEq s start notFail,
    HolLList.holOptionSome_eq_some witness (sourceTerminationUnique s start _ · witness)]

/-- Membership of the target semantics in the resource-limit extension of
the source semantics, from the per-clock entry simulation. Local factoring of
the original state_rel_IMP_semantics proof. -/
theorem semanticsOfEntrySimulation (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (start : Nat)
    (sim : EntrySimulation s t start)
    (two : (2 : BitVec width) ≠ 0)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail) :
    SemanticsPropsHOL.extendWithResourceLimitHOL
      (fun b => b = WordSemStateFiniteExact.semantics s start)
      (StackSemEvaluate.semantics start t) := by
  rw [targetSemanticsEq s t start sim notFail]
  rcases ht : holOptionSome (targetTermination t start) with _ | b
  · exact Or.inl (divergentEq s t start sim notFail (holOptionSome_none ht))
  · obtain ⟨k, t', r, o, targetRun, m, rfl⟩ := holOptionSome_some ht
    have notTimeOut : some r ≠ some (.timeOut : StackSemResult width) := by
      rintro ⟨⟩
      exact m
    obtain ⟨res, s1, sourceRun, outcome⟩ :=
      targetAgreesWithSimulation s t start k sim notFail (some r) t' targetRun notTimeOut
    rcases outcome with ⟨same, ffi⟩ | ⟨_, halt, prefix', -⟩
    · exact Or.inl (sameTermination s start k notFail r t' o m res s1 sourceRun same ffi)
    · -- the target stopped at the resource limit
      cases halt
      have limit : o = HolOutcome.resourceLimitHit := by
        dsimp only at m
        split at m
        · rename_i zero
          exact absurd (WordLocW.word.inj zero) two
        · exact m
      subst limit
      right
      rw [sourceSemanticsEq s start notFail]
      rcases hs : holOptionSome (sourceTermination s start) with _ | b
      · right
        refine ⟨_, _, rfl, rfl, ?_⟩
        apply HolLList.lprefix_trans ((HolLList.lprefix_fromList _ _).mpr prefix')
        apply HolLList.buildLprefixLub_upper (sourceFamilyChain s start)
        exact ⟨k, by rw [sourceRun]⟩
      · left
        obtain ⟨k2, s2, r2, o2, run2, m2, rfl⟩ := holOptionSome_some hs
        refine ⟨_, o2, s2.ffi.ioEvents, rfl, rfl, prefix'.trans ?_⟩
        rcases Nat.le_total k k2 with le | le
        · have mono := wordEntryEventsMono s start k k2 le
          rw [sourceRun] at mono
          simpa only [wordEntry, run2] using mono
        · have notTimeOut2 : r2 ≠ some .timeOut := by
            rintro rfl
            exact m2
          have boosted := wordEntryAddClock s start k2 (k - k2) r2 s2 run2 notTimeOut2
          rw [Nat.add_sub_of_le le, sourceRun] at boosted
          obtain ⟨-, rfl⟩ := Prod.mk.inj boosted
          exact List.prefix_refl _

/-- Under word_lang_safe_for_space the simulated source run never exceeds the
stack limit, so the resource-limit branch of the entry simulation is empty and
the two semantics coincide. Local factoring of state_rel_IMP_semantics'. -/
theorem semanticsEqOfEntrySimulation (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (start : Nat)
    (sim : EntrySimulation s t start)
    (notFail : WordSemStateFiniteExact.semantics s start ≠ .fail)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace s start) :
    StackSemEvaluate.semantics start t = WordSemStateFiniteExact.semantics s start := by
  rw [targetSemanticsEq s t start sim notFail]
  rcases ht : holOptionSome (targetTermination t start) with _ | b
  · exact divergentEq s t start sim notFail (holOptionSome_none ht)
  · obtain ⟨k, t', r, o, targetRun, m, rfl⟩ := holOptionSome_some ht
    have notTimeOut : some r ≠ some (.timeOut : StackSemResult width) := by
      rintro ⟨⟩
      exact m
    obtain ⟨res, s1, sourceRun, outcome⟩ :=
      targetAgreesWithSimulation s t start k sim notFail (some r) t' targetRun notTimeOut
    rcases outcome with ⟨same, ffi⟩ | ⟨_, _, _, over⟩
    · exact sameTermination s start k notFail r t' o m res s1 sourceRun same ffi
    · obtain ⟨max, maxEq, maxLe⟩ := safe k res s1 sourceRun
      rw [maxEq] at over
      simp only [Option.getD_some] at over
      omega

/-- The original comp_Call at every source clock gives the per-clock entry
simulation (state_rel_with_clock moves the relation to each clock), together
with the original 2w ≠ 0w fact. Local factoring. -/
theorem entrySimulationOfStateRel (ac : AsmConfigExact width) (k : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (t : StackSemStateFiniteExact width C F)
    (lens : List Nat) (start : Nat) (related : stateRel ac k 0 0 s t lens 0) :
    EntrySimulation s t start := by
  intro clock res s1 run notError
  have moved := SemanticsHelpers.stateRelWithClock ac k clock s t lens 0 related
  obtain ⟨ck, t1, res1, targetRun, _, _, outcome⟩ :=
    CompCall.compCall ac start {s with clock := clock} k res s1 {t with clock := clock} lens
      ⟨run, notError, moved⟩
  refine ⟨ck, res1, t1, by simpa only [stackEntry] using targetRun, ?_⟩
  by_cases same : res.map compileResult = res1
  · rw [if_pos same] at outcome
    exact Or.inl ⟨same, outcome.1⟩
  · rw [if_neg same] at outcome
    exact Or.inr ⟨same, outcome⟩

private theorem twoNeZero (ac : AsmConfigExact width) (k : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (t : StackSemStateFiniteExact width C F)
    (lens : List Nat) (related : stateRel ac k 0 0 s t lens 0) : (2 : BitVec width) ≠ 0 := by
  have wide : 8 ≤ width := by
    unfold stateRel at related
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,h,_⟩ := related
    exact h
  have twoLt : 2 < 2 ^ width :=
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by norm_num) wide
  intro h
  have := congrArg BitVec.toNat h
  simp [Nat.mod_eq_of_lt twoLt] at this

/-- Full original state_rel_IMP_semantics (10154-10372): from the whole state
relation at frame 0/0 and a non-Fail source semantics, the native StackSem
semantics of the entry call is in extend_with_resource_limit of the singleton
source semantics. Both premises and the resource-limit set membership are
exactly the original ones; target failure is excluded, target terminations are
either the source termination or a resource-limit prefix of the source trace,
and target divergence yields source divergence with the same trace limit, all
from comp_Call at every clock (with evaluate_add_clock, the io-event
monotonicity laws and word_Call_NONE_not_Break_Continue). HOL's singleton set
is the predicate fun b => b = semantics s start. Canonical maps and word
widths are qualified; evaluators inherit reals_as_rational_cuts (SOUNDNESS
item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_IMP_semantics"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemantics (ac : AsmConfigExact width) (k : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (t : StackSemStateFiniteExact width C F)
    (lens : List Nat) (start : Nat)
    (h : stateRel ac k 0 0 s t lens 0 ∧ WordSemStateFiniteExact.semantics s start ≠ .fail) :
    SemanticsPropsHOL.extendWithResourceLimitHOL
      (fun b => b = WordSemStateFiniteExact.semantics s start)
      (StackSemEvaluate.semantics start t) :=
  semanticsOfEntrySimulation s t start (entrySimulationOfStateRel ac k s t lens start h.1)
    (twoNeZero ac k s t lens h.1) h.2

/-- Full original state_rel_IMP_semantics' (10473-10708): with additionally
word_lang_safe_for_space, the target semantics equals the source semantics.
The comp_Call resource-limit branch would give a source stack_max above the
stack limit, which safe-for-space excludes at every clock. Premises and the
exact equality conclusion are the original ones. Canonical maps and word widths
are qualified; evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_IMP_semantics'"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemantics' (ac : AsmConfigExact width) (k : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (t : StackSemStateFiniteExact width C F)
    (lens : List Nat) (start : Nat)
    (h : stateRel ac k 0 0 s t lens 0 ∧ WordSemStateFiniteExact.semantics s start ≠ .fail ∧
      WordSemStateFiniteExact.wordLangSafeForSpace s start) :
    StackSemEvaluate.semantics start t = WordSemStateFiniteExact.semantics s start :=
  semanticsEqOfEntrySimulation s t start (entrySimulationOfStateRel ac k s t lens start h.1)
    h.2.1 h.2.2

end Flapjack.WordToStackProofs.StateRelSemantics
