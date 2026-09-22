import Flapjack.Compile

/-! Genuine context invariants ported from Pancake's `pan_commonPropsScript.sml`.

This file is temporary pending the HOL-shaped source-tree move.  It deliberately
contains no evaluator boundary or compiler-correctness wrapper.
-/

namespace Flapjack

/-- Cake `ctxt_max_def` (`pan_commonPropsScript.sml:11`) port: the slot bound
recorded by `mk_ctxt`/`ctxt_fc` holds for every variable slot. -/
def panValueCtxtMax [BEq String] (bound : Nat)
    (vars : InfoMap (Shape × List Nat)) : Prop :=
  0 ≤ bound ∧
    ∀ name shape slots, lookupInfo name vars = some (shape, slots) →
      ∀ slot ∈ slots, slot ≤ bound

/-- Cake `no_overlap_def` (`pan_commonPropsScript.sml:18`) port: within each
variable the slots are duplicate-free, and slots of two distinct variables
cannot share a slot number. -/
def panValueNoOverlap [BEq String] (vars : InfoMap (Shape × List Nat)) : Prop :=
  (∀ name shape slots, lookupInfo name vars = some (shape, slots) → slots.Nodup) ∧
    ∀ name name' shape shape' slots slots',
      lookupInfo name vars = some (shape, slots) →
      lookupInfo name' vars = some (shape', slots') →
      (∃ slot, slot ∈ slots ∧ slot ∈ slots') → name = name'

/-- The empty variable map satisfies Cake's `ctxt_max`. -/
theorem panValueCtxtMax_empty [BEq String] (bound : Nat) (hbound : 0 ≤ bound) :
    panValueCtxtMax bound ([] : InfoMap (Shape × List Nat)) := by
  refine ⟨hbound, ?_⟩
  intro name shape slots hlookup
  simp [lookupInfo] at hlookup

/-- Extending a `ctxt_max` context with an entry whose slots are all bounded
    preserves `ctxt_max`.  This is the context-extension step for the `dec` and
    `decCall` cases of Cake's `not_mem_context_assigned_mem_gt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1252`). -/
theorem panValueCtxtMax_cons_of [BEq String] (bound : Nat)
    (vars : InfoMap (Shape × List Nat)) (name : String) (shape : Shape)
    (slots : List Nat) (hmax : panValueCtxtMax bound vars)
    (hslots : ∀ slot ∈ slots, slot ≤ bound) :
    panValueCtxtMax bound ((name, (shape, slots)) :: vars) := by
  refine ⟨hmax.1, ?_⟩
  intro name' shape' slots' hlookup
  cases hb : (name == name') with
  | false =>
      simp only [lookupInfo, hb] at hlookup
      exact hmax.2 name' shape' slots' hlookup
  | true =>
      simp only [lookupInfo, hb] at hlookup
      have hpair : (shape, slots) = (shape', slots') := by simpa using hlookup
      have hslotsEq : slots = slots' := congrArg Prod.snd hpair
      rw [← hslotsEq]
      exact hslots

/-- Weakening a `ctxt_max` context bound preserves `ctxt_max`.  This is the
    context-bound step for the `dec`/`decCall` extension used by Cake's
    `locals_rel_extend_new_var` (`pan_to_crepProofScript.sml:4179`). -/
theorem panValueCtxtMax_mono [BEq String] (bound bound' : Nat) (hle : bound ≤ bound')
    (vars : InfoMap (Shape × List Nat)) (hmax : panValueCtxtMax bound vars) :
    panValueCtxtMax bound' vars := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro name shape slots hlookup slot hmem
  exact Nat.le_trans (hmax.2 name shape slots hlookup slot hmem) hle

/-- Cake `ctxt_max_el_leq` (`pan_to_crepProofScript.sml:1493`): in a
`ctxt_max` context, every recorded slot number of a variable is bounded by the
context bound. -/theorem panValueCtxtMax_getElem_le [BEq String] (bound : Nat)
    (vars : InfoMap (Shape × List Nat)) (name : String) (shape : Shape)
    (slots : List Nat) (n : Nat)
    (hmax : panValueCtxtMax bound vars)
    (hlookup : lookupInfo name vars = some (shape, slots))
    (hn : n < slots.length) :
    slots[n] ≤ bound :=
  hmax.2 name shape slots hlookup slots[n] (List.getElem_mem hn)

/-- Counterpart of the context hypothesis of Cake's
    `not_mem_context_assigned_mem_gt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1252`): any value
    strictly above a `ctxt_max` bound is absent from the slot list of every
    variable in the context. -/
theorem panValueCtxtMax_not_mem_of_lt [BEq String] (bound x : Nat)
    (vars : InfoMap (Shape × List Nat)) (name : String) (shape : Shape)
    (slots : List Nat)
    (hmax : panValueCtxtMax bound vars)
    (hx : bound < x)
    (hlookup : lookupInfo name vars = some (shape, slots)) :
    x ∉ slots := by
  intro hmem
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hmem
  have hle := panValueCtxtMax_getElem_le bound vars name shape slots n hmax hlookup hn
  rw [hget] at hle
  omega

/-- The empty variable map satisfies Cake's `no_overlap`. -/
theorem panValueNoOverlap_empty [BEq String] :
    panValueNoOverlap ([] : InfoMap (Shape × List Nat)) := by
  refine ⟨?_, ?_⟩
  · intro name shape slots hlookup
    simp [lookupInfo] at hlookup
  · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
    simp [lookupInfo] at hlookup

/-- Extending a `no_overlap` context with a fresh entry whose slots are
    duplicate-free and disjoint from every existing entry preserves
    `no_overlap`.  This is the context-extension step for Cake's
    `locals_rel_extend_new_var` (`pan_to_crepProofScript.sml:4179`). -/
theorem panValueNoOverlap_cons_of [BEq String] [LawfulBEq String]
    (vars : InfoMap (Shape × List Nat)) (name : String) (shape : Shape)
    (slots : List Nat)
    (hoverlap : panValueNoOverlap vars)
    (hnodup : slots.Nodup)
    (hdisj : ∀ name' shape' slots',
      lookupInfo name' vars = some (shape', slots') → ListDisjoint slots slots') :
    panValueNoOverlap ((name, (shape, slots)) :: vars) := by
  refine ⟨?_, ?_⟩
  · intro name' shape' slots' hlookup
    cases hb : (name == name') with
    | false =>
        have hlookup' : lookupInfo name' vars = some (shape', slots') := by
          simpa [lookupInfo, hb] using hlookup
        exact hoverlap.1 name' shape' slots' hlookup'
    | true =>
        have hpair : (shape, slots) = (shape', slots') := by
          simpa [lookupInfo, hb] using hlookup
        have hslotsEq : slots = slots' := congrArg Prod.snd hpair
        rw [← hslotsEq]
        exact hnodup
  · intro name1 name2 shape1 shape2 slots1 slots2 hl1 hl2 hcommon
    cases hb1 : (name == name1) with
    | false =>
        have hl1' : lookupInfo name1 vars = some (shape1, slots1) := by
          simpa [lookupInfo, hb1] using hl1
        cases hb2 : (name == name2) with
        | false =>
            have hl2' : lookupInfo name2 vars = some (shape2, slots2) := by
              simpa [lookupInfo, hb2] using hl2
            exact hoverlap.2 name1 name2 shape1 shape2 slots1 slots2 hl1' hl2' hcommon
        | true =>
            have hl2' : (shape, slots) = (shape2, slots2) := by
              simpa [lookupInfo, hb2] using hl2
            have hslots2 : slots = slots2 := congrArg Prod.snd hl2'
            obtain ⟨slot, hs1, hs2⟩ := hcommon
            rw [← hslots2] at hs2
            exfalso
            exact hdisj name1 shape1 slots1 hl1' slot hs2 hs1
    | true =>
        have hl1' : (shape, slots) = (shape1, slots1) := by
          simpa [lookupInfo, hb1] using hl1
        cases hb2 : (name == name2) with
        | false =>
            have hl2' : lookupInfo name2 vars = some (shape2, slots2) := by
              simpa [lookupInfo, hb2] using hl2
            have hslots1 : slots = slots1 := congrArg Prod.snd hl1'
            obtain ⟨slot, hs1, hs2⟩ := hcommon
            rw [← hslots1] at hs1
            exfalso
            exact hdisj name2 shape2 slots2 hl2' slot hs1 hs2
        | true =>
            have hname1 : name1 = name := (beq_iff_eq.mp hb1).symm
            have hname2 : name2 = name := (beq_iff_eq.mp hb2).symm
            rw [hname1, hname2]

/-- Counterpart of Cake `no_overlap_flookup_distinct`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml`): two distinct
    variables of a `no_overlap` context have disjoint slot lists. -/
theorem panValueNoOverlap_lookup_disjoint [BEq String] [LawfulBEq String]
    (vars : InfoMap (Shape × List Nat)) (name name' : String)
    (shape shape' : Shape) (slots slots' : List Nat)
    (hoverlap : panValueNoOverlap vars) (hne : name ≠ name')
    (hlookup : lookupInfo name vars = some (shape, slots))
    (hlookup' : lookupInfo name' vars = some (shape', slots')) :
    ListDisjoint slots slots' := by
  intro value hin hin'
  exact hne (hoverlap.2 name name' shape shape' slots slots'
    hlookup hlookup' ⟨value, hin, hin'⟩)

end Flapjack
