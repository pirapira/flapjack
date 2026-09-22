import Flapjack.CompileCalleeParameterFreshness
import Flapjack.PanToCrepMaxList

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

/-- Counterpart of Cake `all_distinct_alist_no_overlap`
    (`cakeml/pancake/semantics/panPropsScript.sml`): the `(variable, shape,
    slot-list)` alist built by splitting a nodup flat slot list with
    `withShape` satisfies `panValueNoOverlap`. -/
theorem panValueNoOverlap_zip_withShape [LawfulBEq String]
    (ns : List Nat) (vs : List VarName) (sh : List Shape)
    (hns : ns.Nodup)
    (hlen : ns.length = Shape.shapeSize (.comb sh))
    (hlenv : vs.length = sh.length) :
    panValueNoOverlap (vs.zip (sh.zip (withShape sh ns))) := by
  constructor
  · intro name shape slots hlookup
    have hmem := lookupInfo_some_mem name
      (vs.zip (sh.zip (withShape sh ns))) (shape, slots) hlookup
    obtain ⟨i, hi, _hj, _hfirst, hsecond⟩ :=
      mem_zip_getElem vs (sh.zip (withShape sh ns)) (name, (shape, slots)) hmem
    rw [List.getElem_zip] at hsecond
    have hiShapes : i < sh.length := by rw [hlenv] at hi; exact hi
    have hiValues : i < (withShape sh ns).length := by
      rw [withShape_length]; exact hiShapes
    have hcomponent : slots = (withShape sh ns)[i]'hiValues := by
      simpa using (congrArg Prod.snd hsecond).symm
    rw [hcomponent]
    exact all_distinct_withShape sh ns i hns hiShapes hlen
  · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
    by_cases hneName : name = name'
    · exact hneName
    · exfalso
      obtain ⟨slot, hslot, hslot'⟩ := hcommon
      have hmem := lookupInfo_some_mem name
        (vs.zip (sh.zip (withShape sh ns))) (shape, slots) hlookup
      have hmem' := lookupInfo_some_mem name'
        (vs.zip (sh.zip (withShape sh ns))) (shape', slots') hlookup'
      have hdisj := listDisjoint_of_mem_zip_withShape vs sh ns
        (name, (shape, slots)) (name', (shape', slots'))
        hlenv (by rw [withShape_length]) hns hlen hmem hmem' hneName
      exact hdisj slot hslot hslot'

/-! Counterpart of Cake's `all_distinct_alist_ctxt_max`
    (`cakeml/pancake/semantics/panPropsScript.sml`): the `(variable, shape,
    slot-list)` alist built by splitting a flat slot list with `withShape`
    satisfies `panValueCtxtMax` at `maxList ns`. -/
theorem panValueCtxtMax_zip_withShape [LawfulBEq String]
    (ns : List Nat) (vs : List VarName) (sh : List Shape)
    (_hns : ns.Nodup)
    (hlen : ns.length = Shape.shapeSize (.comb sh))
    (hlenv : vs.length = sh.length) :
    panValueCtxtMax (maxList ns) (vs.zip (sh.zip (withShape sh ns))) := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro name shape slots hlookup slot hslot
  have hmem := lookupInfo_some_mem name
    (vs.zip (sh.zip (withShape sh ns))) (shape, slots) hlookup
  obtain ⟨i, hi, _hj, _hfirst, hsecond⟩ :=
    mem_zip_getElem vs (sh.zip (withShape sh ns)) (name, (shape, slots)) hmem
  rw [List.getElem_zip] at hsecond
  have hiShapes : i < sh.length := by rw [hlenv] at hi; exact hi
  have hiValues : i < (withShape sh ns).length := by
    rw [withShape_length]; exact hiShapes
  have hcomponent : slots = (withShape sh ns)[i]'hiValues := by
    simpa using (congrArg Prod.snd hsecond).symm
  rw [hcomponent] at hslot
  exact maxList_ge_of_mem ns slot
    (mem_of_withShape_mem sh ns i slot hiValues hlen hslot)

/-! The compiler-generated formal-parameter map satisfies the Cake `no_overlap`
    invariant.  The proof reuses the source-shaped parameter-list allocation
    theorem, then transports it through the metadata equation and the
    list-backed finite-map lookup. -/
theorem panValueNoOverlap_compileParamVars
    [LawfulBEq String]
    (params : List (VarName × Shape)) (offset : Nat) :
    panValueNoOverlap ((compileParamVars params offset).1.reverse) := by
  let values : List (PanValue Unit) := params.map (fun _ => PanValue.word ())
  have hlength : params.length = values.length := by
    simp [values]
  have hpair := compileCalleeParameterList_slots_pairwise_disjoint
    params values offset hlength
  have hrel := pairwise_symmetric_relation_of_mem
    (fun left right : CalleeParameter Unit =>
      ∀ slot ∈ left.slots, slot ∉ right.slots)
    (compileCalleeParameterList params values offset) hpair
  have hmetadata := compileCalleeParameterList_metadata params values offset hlength
  have hdistinct : ∀ names : List Nat, CrepDistinctNames names → names.Nodup := by
    intro names
    induction names with
    | nil => simp
    | cons name names ih =>
        intro h
        rcases h with ⟨hnot, htail⟩
        exact List.pairwise_cons.mpr ⟨
          (fun other hmem heq => hnot (heq ▸ hmem)),
          ih htail⟩
  have rawMem : ∀ name shape slots,
      lookupInfo name (compileParamVars params offset).1.reverse =
        some (shape, slots) →
      (name, (shape, slots)) ∈ (compileParamVars params offset).1 := by
    intro name shape slots hlookup
    have hmem := lookupInfo_some_mem name
      (compileParamVars params offset).1.reverse (shape, slots) hlookup
    exact List.mem_reverse.mp hmem
  constructor
  · intro name shape slots hlookup
    have hmemRaw := rawMem name shape slots hlookup
    rw [← hmetadata] at hmemRaw
    obtain ⟨parameter, hparameter, hentry⟩ := List.mem_map.mp hmemRaw
    have hslots := compileCalleeParameterList_distinct_slots
      params values offset hlength parameter hparameter
    have hslots' : slots = parameter.slots :=
      congrArg Prod.snd (congrArg Prod.snd hentry).symm
    rw [hslots']
    exact hdistinct parameter.slots hslots
  · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
    have hmemRaw := rawMem name shape slots hlookup
    have hmemRaw' := rawMem name' shape' slots' hlookup'
    rw [← hmetadata] at hmemRaw hmemRaw'
    obtain ⟨left, hleft, hleftEq⟩ := List.mem_map.mp hmemRaw
    obtain ⟨right, hright, hrightEq⟩ := List.mem_map.mp hmemRaw'
    by_cases heq : left = right
    · have hleftName : left.name = name := congrArg Prod.fst hleftEq
      have hrightName : right.name = name' := congrArg Prod.fst hrightEq
      exact hleftName.symm.trans ((congrArg CalleeParameter.name heq).trans hrightName)
    · have hleftDisj := hrel left hleft right hright heq
      obtain ⟨slot, hslot, hslot'⟩ := hcommon
      have hslotLeft : left.slots = slots :=
        congrArg Prod.snd (congrArg Prod.snd hleftEq)
      have hslotRight : right.slots = slots' :=
        congrArg Prod.snd (congrArg Prod.snd hrightEq)
      exfalso
      apply hleftDisj slot
      · rw [hslotLeft]
        exact hslot
      · rw [hslotRight]
        exact hslot'

/-! The corresponding `ctxt_max` fact uses Cake's inclusive maximum: the
    compiler's next-free slot minus one bounds every parameter slot. -/
theorem panValueCtxtMax_compileParamVars
    [LawfulBEq String]
    (params : List (VarName × Shape)) (offset : Nat)
    (hnames : (params.map Prod.fst).Nodup) :
    panValueCtxtMax
      ((compileParamVars params offset).2.2 - 1)
      ((compileParamVars params offset).1.reverse) := by
  have hnamesCompiled :
      ((compileParamVars params offset).1.map Prod.fst).Nodup := by
    have hshapes := compileParamVars_preserves_parameter_shapes params offset
    have hnames' := congrArg (List.map Prod.fst) hshapes
    have heq :
        (compileParamVars params offset).1.map Prod.fst = params.map Prod.fst := by
      simpa [Function.comp_def] using hnames'
    rw [heq]
    exact hnames
  refine ⟨by omega, ?_⟩
  intro name shape slots hlookup slot hslot
  have hlookupRaw : lookupInfo name (compileParamVars params offset).1 =
      some (shape, slots) := by
    rw [← lookupInfo_reverse_of_nodup name
      (compileParamVars params offset).1 hnamesCompiled] at hlookup
    exact hlookup
  have hlt := compileParamVars_slot_lt params offset name shape slots
    hlookupRaw slot hslot
  omega
/-! Package the two Cake context invariants for the compiler-generated
    parameter map.  This is the concrete `mk_ctxt` fragment used when a
    source callee is entered with its flattened parameters. -/
theorem panToCrepMakeVmap_context_invariants
    [LawfulBEq String]
    (params : List (VarName × Shape))
    (hnames : (params.map Prod.fst).Nodup) :
    panValueNoOverlap (panToCrepMakeVmap params) ∧
      panValueCtxtMax
        ((compileParamVars params 0).2.2 - 1)
        (panToCrepMakeVmap params) := by
  constructor
  · simpa [panToCrepMakeVmap] using
      panValueNoOverlap_compileParamVars params 0
  · simpa [panToCrepMakeVmap] using
      panValueCtxtMax_compileParamVars params 0 hnames

/-! Cake's `state_rel` packages `locals_rel`, whose defining premises are
    `no_overlap` and `ctxt_max`, together with the source-global and memory
    components.  The existing `panValueCrepStateRel` is intentionally kept
    as the compatibility relation used by the lower-level correctness files;
    this strengthened wrapper exposes the original invariant shape for the
    top-level `state_rel_imp_semantics_to_crep` port. -/
end Flapjack
