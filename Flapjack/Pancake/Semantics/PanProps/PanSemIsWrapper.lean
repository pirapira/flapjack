import Flapjack.Pancake.Semantics.PanProps.SemanticsWrapper
import Flapjack.Pancake.Semantics.PanSem.Semantics

namespace Flapjack

/-- Flapjack proof infrastructure: the original source result classification. -/
private def panSemWrapperClass {width : Nat} [NeZero width] :
    Option (PanSemResultExact width) → SemanticsRunResHOL HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.returned _) => .CompleteResult HolOutcome.success
  | _ => .RunError

open Classical in
/-- Flapjack proof infrastructure: classification of any exact clock-indexed
evaluation family, used to prove the original concrete semantics equality. -/
private theorem panSemIsWrapper_aux {width : Nat} [NeZero width] {σ : Type}
    (E : Nat → Option (PanSemResultExact width) ×
      PanSemStateFiniteExact width σ) :
    (if ∃ k, (match (E k).1 with
        | some .timeOut => False
        | some (.finalFfi _) => False
        | some (.returned _) => False
        | _ => True)
      then HolBehaviour.fail
      else
        match holOptionSome (fun res => ∃ k t r outcome,
            E k = (r, t) ∧
            (match r with
             | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
             | some (.returned _) => outcome = HolOutcome.success
             | _ => False) ∧
            res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
        | some res => res
        | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
            l = HolLList.fromList (E k).2.ffi.ioEvents))) =
      panPropsSemanticsWrapper
        (Prod.map panSemWrapperClass
          (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘ E) := by
  have hk : ∀ k, (match (E k).1 with
      | some .timeOut => False
      | some (.finalFfi _) => False
      | some (.returned _) => False
      | _ => True) ↔
      ∃ v, (Prod.map panSemWrapperClass
        (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘ E) k = (.RunError, v) := by
    intro k
    simp only [Function.comp_apply]
    generalize E k = e
    rcases e with ⟨r, t⟩
    rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp [panSemWrapperClass]
  have hP : (fun res => ∃ k t r outcome,
      E k = (r, t) ∧
      (match r with
       | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
       | some (.returned _) => outcome = HolOutcome.success
       | _ => False) ∧
      res = HolBehaviour.terminate outcome t.ffi.ioEvents) =
      (fun res => ∃ k r ev,
        (Prod.map panSemWrapperClass
          (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘ E) k =
          (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) := by
    funext res
    apply propext
    constructor
    · rintro ⟨k, t, r, outcome, he, hm, rfl⟩
      refine ⟨k, outcome, t.ffi.ioEvents, ?_, rfl⟩
      simp only [Function.comp_apply, he, Prod.map]
      rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp at hm <;>
        simp [panSemWrapperClass, hm]
    · rintro ⟨k, r', ev, hf, rfl⟩
      simp only [Function.comp_apply] at hf
      rcases he : E k with ⟨r, t⟩
      rw [he] at hf
      simp only [Prod.map, Prod.mk.injEq] at hf
      obtain ⟨hg, rfl⟩ := hf
      refine ⟨k, t, r, r', he, ?_, rfl⟩
      rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp [panSemWrapperClass] at hg ⊢ <;>
        exact hg.symm
  unfold panPropsSemanticsWrapper
  rw [exists_congr hk, hP]
  rfl


namespace PanSemIsWrapperFiniteSupport
/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness


end PanSemIsWrapperFiniteSupport

/-- Original no-premise equality for the faithful PanSem evaluator and
observational semantics. TailCall is Call NONE, the clock is overwritten at
every natural number, all original result cases and FFI event projection remain.
No evaluator hook, chain, LUB, successful-run or target observation premise is added. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "pan_sem_is_wrapper"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem panPropsPanSemIsWrapper {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (start : Pancake.PanLang.MlS) :
    PanSemStateFiniteExact.semantics source start =
      let prog : Pancake.PanLang.ProgHOL width := .call none start []
      panPropsSemanticsWrapper
        ((Prod.map (fun res : Option (PanSemResultExact width) => match res with
            | some .timeOut => SemanticsRunResHOL.Incomplete
            | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
            | some (.returned _) => .CompleteResult HolOutcome.success
            | _ => .RunError)
          (fun state : PanSemStateFiniteExact width σ => state.ffi.ioEvents)) ∘
          (fun k => PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k } prog)) := by
  unfold PanSemStateFiniteExact.semantics
  exact panSemIsWrapper_aux _

end Flapjack
