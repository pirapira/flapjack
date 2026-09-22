import Flapjack.PanProgramSimp
import Flapjack.PanValueFlatten
import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.Language

/-!
Faithful port of the HOL4/CakeML finite-map interface used by the original
`pan_to_crepProofScript.sml` correctness chain.

CakeML's `('a,'b) fmap` (`finite_mapTheory`) is a total function with finite
support; `FLOOKUP`, `FUPDATE` (`|+`), `FUPDATE_LIST` (`|++`) and `FEMPTY` are
its observable interface.  We represent it here as `α → Option β`, which is
extensionally the same object and makes the HOL equations definitional:

* `FLOOKUP (FUPDATE f (k,v)) k' = if k = k' then SOME v else FLOOKUP f k'`
  (`finite_mapTheory.FLOOKUP_UPDATE`);
* `f |++ [] = f`, `f |++ (h::t) = FUPDATE f h |++ t`
  (`finite_mapTheory.FUPDATE_LIST_THM`);
* `~MEM k (MAP FST kvl) => FUPDATE (f |++ kvl) (k,v) = (FUPDATE f (k,v)) |++ kvl`
  (`finite_mapTheory.FUPDATE_FUPDATE_LIST_COMMUTES`).

The list-valued helpers `opt_mmap_some_eq_zip_flookup` and
`opt_mmap_disj_zip_flookup` (`pan_commonPropsScript.sml:170`, `:188`) are the
ones consumed by `local_rel_le_zip_update_preserved`
(`pan_to_crepProofScript.sml:2263`).
-/

namespace Flapjack

/-- CakeML/HOL `('a,'b) fmap`, represented as a total function. -/
abbrev FiniteMap (α β : Type) := α → Option β

/-- Cake `FLOOKUP` (`finite_mapTheory.FLOOKUP_DEF`). -/
def FLOOKUP (f : FiniteMap α β) (key : α) : Option β := f key

/-- Cake `FEMPTY`. -/
def FEMPTY : FiniteMap α β := fun _ => none

/-- Cake `FUPDATE` (`|+`, `finite_mapTheory.FUPDATE_DEF`). -/
def FUPDATE [BEq α] (f : FiniteMap α β) (entry : α × β) : FiniteMap α β :=
  fun key => if entry.1 == key then some entry.2 else f key

/-- Cake `FUPDATE_LIST` (`|++`, `finite_mapTheory.FUPDATE_LIST`), i.e.
`FOLDL FUPDATE`. -/
def FUPDATE_LIST [BEq α] (f : FiniteMap α β) (entries : List (α × β)) : FiniteMap α β :=
  entries.foldl (fun g entry => FUPDATE g entry) f

/-- Cake `FDOM`: the keys whose lookup is defined. -/
def FDOM (f : FiniteMap α β) : α → Prop := fun key => f key ≠ none

@[simp] theorem FLOOKUP_empty (key : α) :
    FLOOKUP (FEMPTY : FiniteMap α β) key = none := rfl

/-- Cake `FLOOKUP_UPDATE` (`finite_mapTheory.FLOOKUP_UPDATE`). -/
theorem FLOOKUP_update [BEq α] [LawfulBEq α] (f : FiniteMap α β)
    (k1 : α) (v : β) (k2 : α) :
    FLOOKUP (FUPDATE f (k1, v)) k2 = if k1 == k2 then some v else FLOOKUP f k2 :=
  rfl

/-- Cake `FUPDATE_LIST_THM`, nil case. -/
theorem FUPDATE_LIST_nil [BEq α] (f : FiniteMap α β) :
    FUPDATE_LIST f [] = f := rfl

/-- Cake `FUPDATE_LIST_THM`, cons case. -/
theorem FUPDATE_LIST_cons [BEq α] (f : FiniteMap α β) (entry : α × β)
    (entries : List (α × β)) :
    FUPDATE_LIST f (entry :: entries) = FUPDATE_LIST (FUPDATE f entry) entries := rfl

/-- Cake `FUPDATE_LIST_APPLY_NOT_MEM`: updating keys other than `k` does not
change the lookup at `k`. -/
theorem FLOOKUP_FUPDATE_LIST_not_mem [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (entries : List (α × β)) (k : α)
    (h : k ∉ entries.map Prod.fst) :
    FLOOKUP (FUPDATE_LIST f entries) k = FLOOKUP f k := by
  induction entries generalizing f with
  | nil => rfl
  | cons entry entries ih =>
    have hk : entry.1 ≠ k := by
      intro he
      exact h (by simp [he])
    have htail : k ∉ entries.map Prod.fst := by
      intro hmem
      exact h (by simp [hmem])
    rw [FUPDATE_LIST_cons, ih (FUPDATE f entry) htail, FLOOKUP_update]
    have hbf : (entry.1 == k) = false := beq_eq_false_iff_ne.mpr hk
    simp [hbf]

/-- Two single updates at distinct keys commute. -/
theorem FUPDATE_comm [BEq α] [LawfulBEq α] (f : FiniteMap α β)
    (k1 : α) (v1 : β) (k2 : α) (v2 : β) (h : k1 ≠ k2) :
    FUPDATE (FUPDATE f (k1, v1)) (k2, v2) =
      FUPDATE (FUPDATE f (k2, v2)) (k1, v1) := by
  funext key
  unfold FUPDATE
  by_cases h2 : k2 == key
  · have hk2 : k2 = key := beq_iff_eq.mp h2
    have h1 : (k1 == key) = false := by
      have hne : k1 ≠ key := fun he => h (he.trans hk2.symm)
      exact beq_eq_false_iff_ne.mpr hne
    simp [h2, h1]
  · have hk2 : key ≠ k2 := fun he => h2 (beq_iff_eq.mpr he.symm)
    have h2f : (k2 == key) = false := beq_eq_false_iff_ne.mpr (fun he => hk2 he.symm)
    by_cases h1 : k1 == key <;> simp [h2f, h1]

/-- Cake `FUPDATE_FUPDATE_LIST_COMMUTES`: a single update at a key absent from
the update list commutes with the whole list update. -/
theorem FUPDATE_FUPDATE_LIST_commutes [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (k : α) (v : β) (entries : List (α × β))
    (h : k ∉ entries.map Prod.fst) :
    FUPDATE (FUPDATE_LIST f entries) (k, v) =
      FUPDATE_LIST (FUPDATE f (k, v)) entries := by
  induction entries generalizing f with
  | nil => rfl
  | cons entry entries ih =>
    have hk : entry.1 ≠ k := by
      intro he
      exact h (by simp [he])
    have htail : k ∉ entries.map Prod.fst := by
      intro hmem
      exact h (by simp [hmem])
    rw [FUPDATE_LIST_cons (f := FUPDATE f (k, v)) (entry := entry) (entries := entries)]
    rw [FUPDATE_LIST_cons (f := f) (entry := entry) (entries := entries)]
    rw [ih (FUPDATE f entry) htail]
    rw [FUPDATE_comm f entry.1 entry.2 k v hk]

/-- `mapM` congruence: pointwise-equal maps on the elements of a list give the
same `OPT_MMAP` result. -/
theorem list_mapM_congr {α β : Type} (g h : α → Option β) (xs : List α)
    (hgh : ∀ x, x ∈ xs → g x = h x) : xs.mapM g = xs.mapM h := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, hgh x (by simp), ih (fun y hy => hgh y (by simp [hy]))]

/-- Cake `opt_mmap_some_eq_zip_flookup` (`pan_commonPropsScript.sml:170`):
folding the `(key,value)` list over a finite map makes every key look up its
paired value, provided the key list is duplicate-free and lengths agree. -/
theorem opt_mmap_some_eq_zip_flookup [BEq α] [LawfulBEq α]
    (xs : List α) (f : FiniteMap α β) (ys : List β)
    (hdistinct : xs.Nodup) (hlen : xs.length = ys.length) :
    xs.mapM (fun key => FLOOKUP (FUPDATE_LIST f (xs.zip ys)) key) = some ys := by
  induction xs generalizing ys f with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      obtain ⟨hxnot, hdistinct'⟩ := List.nodup_cons.mp hdistinct
      have hlen' : xs.length = ys.length := by
        simp only [List.length_cons] at hlen
        omega
      have hxzip : x ∉ (xs.zip ys).map Prod.fst := by
        intro hmem
        obtain ⟨p, hp, hfst⟩ := List.mem_map.mp hmem
        obtain ⟨hpin, _hpy⟩ := List.of_mem_zip hp
        rw [hfst] at hpin
        exact hxnot hpin
      rw [List.zip_cons_cons, FUPDATE_LIST_cons, List.mapM_cons]
      have hhead : FLOOKUP (FUPDATE_LIST (FUPDATE f (x, y)) (xs.zip ys)) x = some y := by
        rw [FLOOKUP_FUPDATE_LIST_not_mem (FUPDATE f (x, y)) (xs.zip ys) x hxzip,
          FLOOKUP_update]
        simp
      have htail :
          xs.mapM (fun key => FLOOKUP (FUPDATE_LIST (FUPDATE f (x, y)) (xs.zip ys)) key)
            = some ys :=
        ih (ys := ys) (f := FUPDATE f (x, y)) hdistinct' hlen'
      rw [hhead, htail]
      rfl

/-- Cake `opt_mmap_disj_zip_flookup` (`pan_commonPropsScript.sml:188`): if the
updated keys are disjoint from the queried keys, the list update is invisible
to the query. -/
theorem opt_mmap_disj_zip_flookup [BEq α] [LawfulBEq α]
    (xs : List α) (f : FiniteMap α β) (ys : List α) (zs : List β)
    (hdisj : ListDisjoint xs ys) (hlen : xs.length = zs.length) :
    ys.mapM (fun key => FLOOKUP (FUPDATE_LIST f (xs.zip zs)) key) =
      ys.mapM (fun key => FLOOKUP f key) := by
  induction xs generalizing zs f with
  | nil => rfl
  | cons x xs ih =>
    cases zs with
    | nil => simp at hlen
    | cons z zs =>
      have hlen' : xs.length = zs.length := by
        simp only [List.length_cons] at hlen
        omega
      have hxnot : x ∉ ys := by
        intro hmem
        exact hdisj x (by simp) hmem
      have hdisj' : ListDisjoint xs ys := by
        intro value hin hin'
        exact hdisj value (by simp [hin]) hin'
      rw [List.zip_cons_cons, FUPDATE_LIST_cons]
      rw [ih (zs := zs) (f := FUPDATE f (x, z)) hdisj' hlen']
      apply list_mapM_congr
      intro key hkey
      rw [FLOOKUP_update]
      have hkx : (x == key) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro he
        exact hxnot (he ▸ hkey)
      simp [hkx]

/-- Cake `locals_rel_def` (`pan_to_crepProofScript.sml:71`) port.  The source
locals are keyed by variable name and the target locals by word address; the
relation records that every live variable's flattened word list is recoverable
from the target map through its slot list.  `vars` is the alist representation
of `ctxt.vars` (looked up with `lookupInfo`, the Flapjack `FLOOKUP` on the
context). -/
def localsRel [BEq String] (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (sLocals : FiniteMap String (PanValue α))
    (tLocals : FiniteMap Nat α) : Prop :=
  panValueNoOverlap vars ∧ panValueCtxtMax vmax vars ∧
    ∀ vname v, FLOOKUP sLocals vname = some v →
      ∃ ns vs, lookupInfo vname vars = some (panValueShape [] v, ns) ∧
        ns.mapM (FLOOKUP tLocals) = some vs ∧ panValueFlatten v = vs ∧
        isWfShape [] (panValueShape [] v) = true

/-- Cake `locals_rel_lookup_ctxt` (`pan_to_crepProofScript.sml:527`). -/
theorem localsRel_lookup_ctxt [BEq String]
    (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (sLocals : FiniteMap String (PanValue α)) (tLocals : FiniteMap Nat α)
    (vr : String) (v : PanValue α)
    (hrel : localsRel vars vmax sLocals tLocals)
    (hlookup : FLOOKUP sLocals vr = some v) :
    ∃ ns, lookupInfo vr vars = some (panValueShape [] v, ns) ∧
      ns.length = (panValueFlatten v).length ∧
      ns.mapM (FLOOKUP tLocals) = some (panValueFlatten v) ∧
      isWfShape [] (panValueShape [] v) = true := by
  obtain ⟨ns, vs, hctxt, hmap, hflat, hwf⟩ := hrel.2.2 vr v hlookup
  refine ⟨ns, hctxt, ?_, ?_, hwf⟩
  · rw [hflat]
    exact list_mapM_length (FLOOKUP tLocals) ns vs hmap
  · rw [hflat]
    exact hmap

/-- Cake `mk_ctxt_imp_locals_rel` (`pan_to_crepProofScript.sml:4677`),
source-map-empty generalization: any context map that satisfies `no_overlap`
and `ctxt_max` is related to an arbitrary target locals map when the source
locals map is `FEMPTY` (the third conjunct is vacuous). -/
theorem localsRel_of_empty_source [BEq String]
    (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (tLocals : FiniteMap Nat α)
    (hnooverlap : panValueNoOverlap vars)
    (hmax : panValueCtxtMax vmax vars) :
    localsRel vars vmax (FEMPTY : FiniteMap String (PanValue α)) tLocals := by
  refine ⟨hnooverlap, hmax, ?_⟩
  intro vname v hlookup
  simp [FLOOKUP_empty] at hlookup

/-- Cake `mk_ctxt_imp_locals_rel` (`pan_to_crepProofScript.sml:4677`) at the
empty context `mk_ctxt FEMPTY (make_funcs pc) 0 es`: the empty variable map
satisfies `no_overlap` and `ctxt_max`, and the source locals map is empty. -/
theorem localsRel_empty [BEq String] (vmax : Nat) (tLocals : FiniteMap Nat α) :
    localsRel ([] : InfoMap (Shape × List Nat)) vmax
      (FEMPTY : FiniteMap String (PanValue α)) tLocals :=
  localsRel_of_empty_source [] vmax tLocals panValueNoOverlap_empty
    (panValueCtxtMax_empty vmax (Nat.zero_le vmax))

/-- Cake `local_rel_le_zip_update_preserved`
(`pan_to_crepProofScript.sml:2263`): overwriting a variable with a
shape-compatible value and refreshing the target map through the variable's
slot list preserves the locals relation. -/
theorem localRel_le_zip_update_preserved [BEq String] [LawfulBEq String]
    (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (l : FiniteMap String (PanValue α)) (l' : FiniteMap Nat α)
    (x : String) (v v' : PanValue α) (sh : Shape) (ns : List Nat)
    (hrel : localsRel vars vmax l l')
    (hlookup : FLOOKUP l x = some v)
    (hctxt : lookupInfo x vars = some (sh, ns))
    (hshape : panValueShape [] v = panValueShape [] v')
    (hdistinct : ns.Nodup) :
    localsRel vars vmax (FUPDATE l (x, v'))
      (FUPDATE_LIST l' (ns.zip (panValueFlatten v'))) := by
  obtain ⟨hns, hnsctxt0, hnslen0, _hnsmap, hnswf⟩ := localsRel_lookup_ctxt vars vmax l l' x v hrel hlookup
  have heq : (panValueShape [] v, hns) = (sh, ns) := by
    apply Option.some.inj
    rw [← hnsctxt0, hctxt]
  have hhns : hns = ns := congrArg Prod.snd heq
  have hnsctxt : lookupInfo x vars = some (panValueShape [] v, ns) := by
    rw [← hhns]
    exact hnsctxt0
  have hnslen : ns.length = (panValueFlatten v).length := by
    rw [← hhns]
    exact hnslen0
  have hwf' : isWfShape [] (panValueShape [] v') = true := by
    rw [← hshape]
    exact hnswf
  have hflatlen : (panValueFlatten v).length = (panValueFlatten v').length := by
    rw [panValueFlatten_length_eq_shapeSize v hnswf,
      panValueFlatten_length_eq_shapeSize v' hwf', hshape]
  have hlen' : ns.length = (panValueFlatten v').length := by
    rw [hnslen, hflatlen]
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  intro vname v'' hlookup''
  rw [FLOOKUP_update] at hlookup''
  cases hx : x == vname with
  | true =>
    have hxv : vname = x := (beq_iff_eq.mp hx).symm
    simp [hx] at hlookup''
    cases hlookup''
    refine ⟨ns, panValueFlatten v', ?_, ?_, rfl, hwf'⟩
    · rw [hxv, ← hshape]
      exact hnsctxt
    · exact opt_mmap_some_eq_zip_flookup ns l' (panValueFlatten v') hdistinct hlen'
  | false =>
    have hne : x ≠ vname := beq_eq_false_iff_ne.mp hx
    simp [hx] at hlookup''
    obtain ⟨ns'', vs'', hctxt'', hmap'', hflat'', hwf''⟩ :=
      hrel.2.2 vname v'' hlookup''
    refine ⟨ns'', vs'', hctxt'', ?_, hflat'', hwf''⟩
    have hdisj : ListDisjoint ns ns'' :=
      panValueNoOverlap_lookup_disjoint vars x vname (panValueShape [] v)
        (panValueShape [] v'') ns ns'' hrel.1 hne hnsctxt hctxt''
    rw [opt_mmap_disj_zip_flookup ns l' ns'' (panValueFlatten v') hdisj hlen']
    exact hmap''

/-- Cake `locals_rel_extend_new_var` (`pan_to_crepProofScript.sml:4179`):
extending the source and target locals with a fresh variable whose slot list is
duplicate-free, bounded above the old context and below the new context bound,
and length-matched to the flattened value, preserves the locals relation. -/
theorem localsRel_extend_new_var [BEq String] [LawfulBEq String]
    (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (l : FiniteMap String (PanValue α)) (l' : FiniteMap Nat α)
    (x : String) (v : PanValue α) (ns : List Nat)
    (hrel : localsRel vars vmax l l')
    (hwf : isWfShape [] (panValueShape [] v) = true)
    (hdistinct : ns.Nodup)
    (hbounds : ∀ slot ∈ ns,
      vmax < slot ∧ slot ≤ vmax + Shape.shapeSize (panValueShape [] v))
    (hlen : ns.length = Shape.shapeSize (panValueShape [] v)) :
    localsRel ((x, (panValueShape [] v, ns)) :: vars)
      (vmax + Shape.shapeSize (panValueShape [] v))
      (FUPDATE l (x, v)) (FUPDATE_LIST l' (ns.zip (panValueFlatten v))) := by
  have hlenFlat : ns.length = (panValueFlatten v).length := by
    rw [hlen, panValueFlatten_length_eq_shapeSize v hwf]
  have hdisjAll : ∀ name' shape' slots',
      lookupInfo name' vars = some (shape', slots') → ListDisjoint ns slots' := by
    intro name' shape' slots' hlookup' slot hmem hmem'
    exact panValueCtxtMax_not_mem_of_lt vmax slot vars name' shape' slots'
      hrel.2.1 (hbounds slot hmem).1 hlookup' hmem'
  refine ⟨?_, ?_, ?_⟩
  · exact panValueNoOverlap_cons_of vars x (panValueShape [] v) ns
      hrel.1 hdistinct hdisjAll
  · exact panValueCtxtMax_cons_of (vmax + Shape.shapeSize (panValueShape [] v))
      vars x (panValueShape [] v) ns
      (panValueCtxtMax_mono vmax (vmax + Shape.shapeSize (panValueShape [] v))
        (Nat.le_add_right _ _) vars hrel.2.1)
      (fun slot hmem => (hbounds slot hmem).2)
  · intro vname v'' hlookup''
    rw [FLOOKUP_update] at hlookup''
    cases hx : (x == vname) with
    | true =>
        have hxv : vname = x := (beq_iff_eq.mp hx).symm
        simp [hx] at hlookup''
        cases hlookup''
        refine ⟨ns, panValueFlatten v, ?_, ?_, rfl, hwf⟩
        · rw [hxv]
          simp [lookupInfo]
        · exact opt_mmap_some_eq_zip_flookup ns l' (panValueFlatten v)
            hdistinct hlenFlat
    | false =>
        have hne : x ≠ vname := beq_eq_false_iff_ne.mp hx
        simp [hx] at hlookup''
        obtain ⟨ns'', vs'', hctxt'', hmap'', hflat'', hwf''⟩ :=
          hrel.2.2 vname v'' hlookup''
        have hbf : (x == vname) = false := beq_eq_false_iff_ne.mpr hne
        refine ⟨ns'', vs'', ?_, ?_, hflat'', hwf''⟩
        · simpa [lookupInfo, hbf] using hctxt''
        · have hdisj'' : ListDisjoint ns ns'' := by
            intro slot hmem hmem'
            exact panValueCtxtMax_not_mem_of_lt vmax slot vars vname
              (panValueShape [] v'') ns'' hrel.2.1 (hbounds slot hmem).1 hctxt'' hmem'
          rw [opt_mmap_disj_zip_flookup ns l' ns'' (panValueFlatten v) hdisj'' hlenFlat]
          exact hmap''

/-! ### Domain subtraction and Cake's `res_var` -/

/-- Counterpart of HOL4's `\\` (domain subtraction) on finite maps:
    `FDOMSUB f key` removes `key` from the domain of `f`. -/
def FDOMSUB [BEq α] (f : FiniteMap α β) (key : α) : FiniteMap α β :=
  fun k => if key == k then none else f k

/-- Counterpart of Cake's `res_var_def` (cakeml/pancake/semantics/crepSemScript.sml:163):
    `res_var lc (n, NONE) = lc \\ n` and `res_var lc (n, SOME v) = lc |+ (n,v)`. -/
def resVar [BEq α] (f : FiniteMap α β) (entry : α × Option β) : FiniteMap α β :=
  match entry.2 with
  | none => FDOMSUB f entry.1
  | some v => FUPDATE f (entry.1, v)

theorem FLOOKUP_domsub [BEq α] [LawfulBEq α] (f : FiniteMap α β) (key k : α) :
    FLOOKUP (FDOMSUB f key) k = if key == k then none else FLOOKUP f k := rfl

theorem FDOMSUB_FUPDATE_neq [BEq α] [LawfulBEq α] (f : FiniteMap α β) (key m : α) (v : β)
    (h : key ≠ m) :
    FDOMSUB (FUPDATE f (m, v)) key = FUPDATE (FDOMSUB f key) (m, v) := by
  funext k
  simp only [FDOMSUB, FUPDATE]
  by_cases hkm : m == k
  · simp only [hkm, if_true]
    have hkm' : k = m := (beq_iff_eq.mp hkm).symm
    have hkeyk : (key == k) = false := by
      rw [beq_eq_false_iff_ne]
      intro hc
      exact h (hc.trans hkm')
    simp only [hkeyk, Bool.false_eq_true, if_false]
  · simp only [hkm, Bool.false_eq_true, if_false]

theorem FDOMSUB_commutes [BEq α] [LawfulBEq α] (f : FiniteMap α β) (n m : α)
    (h : n ≠ m) : FDOMSUB (FDOMSUB f n) m = FDOMSUB (FDOMSUB f m) n := by
  funext k
  simp only [FDOMSUB]
  by_cases hmn : m == k
  · have hmn' : k = m := (beq_iff_eq.mp hmn).symm
    have hnk : (n == k) = false := by
      rw [beq_eq_false_iff_ne]
      intro hc
      exact h (hc.trans hmn')
    simp only [hmn, if_true, hnk, Bool.false_eq_true, if_false]
  · by_cases hnk : n == k
    · have hnk' : k = n := (beq_iff_eq.mp hnk).symm
      have hmk : (m == k) = false := by
        rw [beq_eq_false_iff_ne]
        intro hc
        exact h (hnk'.symm.trans hc.symm)
      simp only [hnk, if_true, hmk, Bool.false_eq_true, if_false]
    · simp only [hmn, hnk, Bool.false_eq_true, if_false]

/-- Counterpart of Cake's `flookup_res_var_thm` (crepPropsScript.sml:257),
    stated with the Boolean equality that `resVar` is implemented with. -/
theorem FLOOKUP_resVar [BEq α] [LawfulBEq α] (f : FiniteMap α β) (m n : α)
    (v : Option β) :
    FLOOKUP (resVar f (m, v)) n = if n == m then v else FLOOKUP f n := by
  cases v with
  | none =>
    simp only [resVar, FDOMSUB, FLOOKUP]
    by_cases h : n == m
    · have hm : (m == n) = true := by
        rw [beq_iff_eq]
        exact (beq_iff_eq.mp h).symm
      simp only [hm, if_true, h]
    · have hm : (m == n) = false := by
        rw [beq_eq_false_iff_ne]
        intro hc
        exact h (beq_iff_eq.mpr hc.symm)
      simp only [hm, Bool.false_eq_true, if_false, h]
  | some w =>
    simp only [resVar, FUPDATE, FLOOKUP]
    by_cases h : n == m
    · have hm : (m == n) = true := by
        rw [beq_iff_eq]
        exact (beq_iff_eq.mp h).symm
      simp only [hm, if_true, h]
    · have hm : (m == n) = false := by
        rw [beq_eq_false_iff_ne]
        intro hc
        exact h (beq_iff_eq.mpr hc.symm)
      simp only [hm, Bool.false_eq_true, if_false, h]

/-- Counterpart of Cake's `flookup_res_var_diff_eq` (crepPropsScript.sml:249). -/
theorem FLOOKUP_resVar_diff_eq [BEq α] [LawfulBEq α] (f : FiniteMap α β) (m n : α)
    (v : β) (h : n ≠ m) : FLOOKUP (resVar f (m, some v)) n = FLOOKUP f n := by
  rw [FLOOKUP_resVar]
  have hb : (n == m) = false := by
    rw [beq_eq_false_iff_ne]
    exact h
  simp only [hb, Bool.false_eq_true, if_false]

/-- Counterpart of Cake's `res_var_commutes` (crepPropsScript.sml:234). -/
theorem resVar_commutes [BEq α] [LawfulBEq α] (lc lc' : FiniteMap α β) (n h : α)
    (hne : n ≠ h) :
    resVar (resVar lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
    resVar (resVar lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h) := by
  cases hh : FLOOKUP lc' h with
  | none =>
    cases hn : FLOOKUP lc' n with
    | none =>
      simp only [resVar]
      rw [FDOMSUB_commutes lc n h hne]
    | some vn =>
      simp only [resVar]
      rw [FDOMSUB_FUPDATE_neq lc h n vn hne.symm]
  | some vh =>
    cases hn : FLOOKUP lc' n with
    | none =>
      simp only [resVar]
      rw [FDOMSUB_FUPDATE_neq lc n h vh hne]
    | some vn =>
      simp only [resVar]
      rw [FUPDATE_comm lc h vh n vn hne.symm]

/-- Counterpart of Cake's `flookup_res_var_distinct_eq` (crepPropsScript.sml:763):
folding `res_var` over a list whose keys do not contain `x` leaves `x` untouched. -/
theorem FLOOKUP_foldl_resVar_not_mem [BEq α] [LawfulBEq α]
    (xs : List (α × Option β)) (f : FiniteMap α β) (x : α)
    (h : x ∉ xs.map Prod.fst) :
    FLOOKUP (xs.foldl resVar f) x = FLOOKUP f x := by
  induction xs generalizing f with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, hrest⟩ := h
    rw [List.foldl_cons, ih (resVar f entry) hrest, FLOOKUP_resVar]
    have hfalse : (x == entry.1) = false := beq_eq_false_iff_ne.mpr hne
    simp [hfalse]

/-- Counterpart of Cake's `flookup_res_var_distinct_zip_eq` (crepPropsScript.sml:777):
the zipped form of `FLOOKUP_foldl_resVar_not_mem`. -/
theorem FLOOKUP_foldl_resVar_zip_not_mem [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List (Option β)) (f : FiniteMap α β) (x : α)
    (hlen : xs.length = ys.length) (h : x ∉ xs) :
    FLOOKUP ((xs.zip ys).foldl resVar f) x = FLOOKUP f x := by
  apply FLOOKUP_foldl_resVar_not_mem
  rw [List.map_fst_zip (by omega)]
  exact h

/-- Counterpart of Cake's `flookup_res_var_distinct` (crepPropsScript.sml:796):
looking up a key list disjoint from the updated key list is unaffected by the fold. -/
theorem map_FLOOKUP_foldl_resVar_zip [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List α) (zs : List (Option β)) (f : FiniteMap α β)
    (hdisj : ListDisjoint xs ys) (hlen : xs.length = zs.length) :
    ys.map (fun y => FLOOKUP ((xs.zip zs).foldl resVar f) y) =
      ys.map (fun y => FLOOKUP f y) := by
  revert hdisj
  induction ys with
  | nil => intro _; rfl
  | cons y rest ih =>
    intro hdisj
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · exact FLOOKUP_foldl_resVar_zip_not_mem xs zs f y hlen
        (fun hy => hdisj y hy (by simp))
    · exact ih (fun v hv hmem => hdisj v hv (by simp [hmem]))

end Flapjack
