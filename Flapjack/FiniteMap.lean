import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.Proofs.PanSimp
import Flapjack.PanValueFlatten
import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.Pancake.PanLang

/-!
Faithful port of the HOL4/CakeML finite-map interface used by the original
`pan_to_crepProofScript.sml` correctness chain.  The primitive interface and
its definitional equations live in `Flapjack.FiniteMap.Basic`, so that
compiler-level modules can cite `FLOOKUP` without depending on this proof
module; this file keeps the derived commutation and list-lookup lemmas.

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

Provenance convention: the lemmas below cite the CakeML/HOL declaration they are
modelled after, but they are Flapjack-specific analogues, not exact HOL ports,
and therefore carry no `@[hol]` tag.  They are stated over this repository's
extensional `α → Option β` finite-map representation with Boolean `BEq`,
whereas the HOL originals are stated over `finite_map`'s `FLOOKUP` object; where
an exact port exists it is tagged and placed in the corresponding proof module
(for example the tagged `locals_rel_def` over the finite-map context lives in
`Flapjack/Pancake/Proofs/PanToCrep.lean`).
-/

namespace Flapjack

/-- `mapM` congruence: pointwise-equal maps on the elements of a list give the
same `OPT_MMAP` result.  Flapjack-specific proof infrastructure; no exact HOL
counterpart. -/
theorem list_mapM_congr {α β : Type} (g h : α → Option β) (xs : List α)
    (hgh : ∀ x, x ∈ xs → g x = h x) : xs.mapM g = xs.mapM h := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, hgh x (by simp), ih (fun y hy => hgh y (by simp [hy]))]

/-- Flapjack-specific analogue of Cake `opt_mmap_some_eq_zip_flookup`
(`pan_commonPropsScript.sml:170`), not an exact HOL port: it uses this file's
extensional map with Boolean `BEq`.  Folding the `(key,value)` list over a finite
map makes every key look up its paired value, provided the key list is
duplicate-free and lengths agree. -/
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

/-- Flapjack-specific analogue of Cake `opt_mmap_disj_zip_flookup`
(`pan_commonPropsScript.sml:188`), not an exact HOL port: if the updated keys are
disjoint from the queried keys, the list update is invisible to the query. -/
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

/-- Flapjack-specific executable surrogate for Cake `locals_rel_def`
(`pan_to_crepProofScript.sml:71`).  The source locals are keyed by variable name
and the target locals by word address; the relation records that every live
variable's flattened word list is recoverable from the target map through its
slot list.  `vars` is the alist representation of `ctxt.vars` (looked up with
`lookupInfo`, the Flapjack `FLOOKUP` on the context).

This list-backed variant is not the reviewed finite-map HOL port; the exact
`@[hol]`-tagged `locals_rel_def` over `PanToCrepProofContext` lives in
`Flapjack/Pancake/Proofs/PanToCrep.lean`. -/
def executableLocalsRel [BEq String] (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (sLocals : FiniteMap String (PanValue α))
    (tLocals : FiniteMap Nat α) : Prop :=
  panValueNoOverlap vars ∧ panValueCtxtMax vmax vars ∧
    ∀ vname v, FLOOKUP sLocals vname = some v →
      ∃ ns vs, lookupInfo vname vars = some (panValueShape [] v, ns) ∧
        ns.mapM (FLOOKUP tLocals) = some vs ∧ panValueFlatten v = vs ∧
        isWfShape [] (panValueShape [] v) = true

/-- Flapjack-specific alist analogue of Cake `locals_rel_lookup_ctxt`
(`pan_to_crepProofScript.sml:527`); not the HOL port.  The exact `@[hol]`-tagged
`locals_rel_def`/`ctxt_max`/`no_overlap` ports are stated over the finite-map
context in `Flapjack/Pancake/Proofs/PanToCrep.lean` and
`Flapjack/Pancake/Semantics/PanCommonProps.lean`; this lemma works with the
list-backed `executableLocalsRel`. -/
theorem executableLocalsRel_lookup_ctxt [BEq String]
    (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (sLocals : FiniteMap String (PanValue α)) (tLocals : FiniteMap Nat α)
    (vr : String) (v : PanValue α)
    (hrel : executableLocalsRel vars vmax sLocals tLocals)
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

/-- Flapjack-specific alist analogue of Cake `mk_ctxt_imp_locals_rel`
(`pan_to_crepProofScript.sml:4677`); not an exact HOL port, because the context
and relation here are the list-backed surrogates.  Source-map-empty
generalization: any context map that satisfies `no_overlap` and `ctxt_max` is
related to an arbitrary target locals map when the source locals map is
`FEMPTY` (the third conjunct is vacuous). -/
theorem executableLocalsRel_of_empty_source [BEq String]
    (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (tLocals : FiniteMap Nat α)
    (hnooverlap : panValueNoOverlap vars)
    (hmax : panValueCtxtMax vmax vars) :
    executableLocalsRel vars vmax (FEMPTY : FiniteMap String (PanValue α)) tLocals := by
  refine ⟨hnooverlap, hmax, ?_⟩
  intro vname v hlookup
  simp [FLOOKUP_empty] at hlookup

/-- Flapjack-specific alist analogue of Cake `mk_ctxt_imp_locals_rel`
(`pan_to_crepProofScript.sml:4677`); not an exact HOL port.  At the empty
context `mk_ctxt FEMPTY (make_funcs pc) 0 es`: the empty variable map satisfies
`no_overlap` and `ctxt_max`, and the source locals map is empty. -/
theorem executableLocalsRel_empty [BEq String] (vmax : Nat) (tLocals : FiniteMap Nat α) :
    executableLocalsRel ([] : InfoMap (Shape × List Nat)) vmax
      (FEMPTY : FiniteMap String (PanValue α)) tLocals :=
  executableLocalsRel_of_empty_source [] vmax tLocals panValueNoOverlap_empty
    (panValueCtxtMax_empty vmax (Nat.zero_le vmax))

/-- Flapjack-specific alist analogue of Cake `local_rel_le_zip_update_preserved`
(`pan_to_crepProofScript.sml:2263`); not an exact HOL port, since it is stated
over `executableLocalsRel` and the list-backed context.  Overwriting a variable
with a shape-compatible value and refreshing the target map through the
variable's slot list preserves the locals relation. -/
theorem localRel_le_zip_update_preserved [BEq String] [LawfulBEq String]
    (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (l : FiniteMap String (PanValue α)) (l' : FiniteMap Nat α)
    (x : String) (v v' : PanValue α) (sh : Shape) (ns : List Nat)
    (hrel : executableLocalsRel vars vmax l l')
    (hlookup : FLOOKUP l x = some v)
    (hctxt : lookupInfo x vars = some (sh, ns))
    (hshape : panValueShape [] v = panValueShape [] v')
    (hdistinct : ns.Nodup) :
    executableLocalsRel vars vmax (FUPDATE l (x, v'))
      (FUPDATE_LIST l' (ns.zip (panValueFlatten v'))) := by
  obtain ⟨hns, hnsctxt0, hnslen0, _hnsmap, hnswf⟩ := executableLocalsRel_lookup_ctxt vars vmax l l' x v hrel hlookup
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

/-- Flapjack-specific alist analogue of Cake `locals_rel_extend_new_var`
(`pan_to_crepProofScript.sml:4179`); not an exact HOL port, since it is stated
over `executableLocalsRel` and the list-backed context.  Extending the source and
target locals with a fresh variable whose slot list is duplicate-free, bounded
above the old context and below the new context bound, and length-matched to the
flattened value, preserves the locals relation. -/
theorem executableLocalsRel_extend_new_var [BEq String] [LawfulBEq String]
    (vars : InfoMap (Shape × List Nat)) (vmax : Nat)
    (l : FiniteMap String (PanValue α)) (l' : FiniteMap Nat α)
    (x : String) (v : PanValue α) (ns : List Nat)
    (hrel : executableLocalsRel vars vmax l l')
    (hwf : isWfShape [] (panValueShape [] v) = true)
    (hdistinct : ns.Nodup)
    (hbounds : ∀ slot ∈ ns,
      vmax < slot ∧ slot ≤ vmax + Shape.shapeSize (panValueShape [] v))
    (hlen : ns.length = Shape.shapeSize (panValueShape [] v)) :
    executableLocalsRel ((x, (panValueShape [] v, ns)) :: vars)
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

/-- Flapjack-specific analogue of Cake's `flookup_res_var_thm`
(crepPropsScript.sml:257), not an exact HOL port: it is stated with the Boolean
equality that `resVar` is implemented with. -/
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

/-- Flapjack-specific analogue of Cake's `flookup_res_var_diff_eq`
(crepPropsScript.sml:249); not an exact HOL port, since it is stated over the
Boolean-`BEq` `resVar`. -/
theorem FLOOKUP_resVar_diff_eq [BEq α] [LawfulBEq α] (f : FiniteMap α β) (m n : α)
    (v : β) (h : n ≠ m) : FLOOKUP (resVar f (m, some v)) n = FLOOKUP f n := by
  rw [FLOOKUP_resVar]
  have hb : (n == m) = false := by
    rw [beq_eq_false_iff_ne]
    exact h
  simp only [hb, Bool.false_eq_true, if_false]

/-- Flapjack-specific analogue of Cake's `res_var_commutes`
(crepPropsScript.sml:234); not an exact HOL port, since it is stated over the
Boolean-`BEq` `resVar`. -/
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

/-- Flapjack-specific analogue of Cake's `flookup_res_var_distinct_eq`
(crepPropsScript.sml:763); not an exact HOL port, since it is stated over this
file's `resVar`: folding `res_var` over a list whose keys do not contain `x`
leaves `x` untouched. -/
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

/-- Flapjack-specific analogue of Cake's `flookup_res_var_distinct_zip_eq`
(crepPropsScript.sml:777); not an exact HOL port: the zipped form of
`FLOOKUP_foldl_resVar_not_mem`. -/
theorem FLOOKUP_foldl_resVar_zip_not_mem [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List (Option β)) (f : FiniteMap α β) (x : α)
    (hlen : xs.length = ys.length) (h : x ∉ xs) :
    FLOOKUP ((xs.zip ys).foldl resVar f) x = FLOOKUP f x := by
  apply FLOOKUP_foldl_resVar_not_mem
  rw [List.map_fst_zip (by omega)]
  exact h

/-- Flapjack-specific analogue of Cake's `flookup_res_var_distinct`
(crepPropsScript.sml:796); not an exact HOL port: looking up a key list disjoint
from the updated key list is unaffected by the fold. -/
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

theorem FLOOKUP_FUPDATE_LIST_zip_not_mem [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List β) (f : FiniteMap α β) (n : α)
    (hlen : xs.length = ys.length) (h : n ∉ xs) :
    FLOOKUP (FUPDATE_LIST f (xs.zip ys)) n = FLOOKUP f n := by
  apply FLOOKUP_FUPDATE_LIST_not_mem
  rw [List.map_fst_zip (by omega)]
  exact h

theorem map_FLOOKUP_FUPDATE_LIST_zip_not_mem [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List α) (zs : List β) (f : FiniteMap α β)
    (hdisj : ListDisjoint xs ys) (hlen : xs.length = zs.length) :
    ys.map (fun y => FLOOKUP (FUPDATE_LIST f (xs.zip zs)) y) =
      ys.map (fun y => FLOOKUP f y) := by
  revert hdisj
  induction ys with
  | nil => intro _; rfl
  | cons y rest ih =>
    intro hdisj
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · exact FLOOKUP_FUPDATE_LIST_zip_not_mem xs zs f y hlen
        (fun hy => hdisj y hy (by simp))
    · exact ih (fun v hv hmem => hdisj v hv (by simp [hmem]))

theorem map_FLOOKUP_foldl_resVar_zip_fupdate [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List α) (as : List β) (cs : List (Option β))
    (fm : FiniteMap α β) (hdisj : ListDisjoint xs ys)
    (hlenAs : xs.length = as.length) (hlenCs : xs.length = cs.length) :
    ys.map (fun y => FLOOKUP ((xs.zip cs).foldl resVar (FUPDATE_LIST fm (xs.zip as))) y) =
      ys.map (fun y => FLOOKUP fm y) := by
  rw [map_FLOOKUP_foldl_resVar_zip xs ys cs (FUPDATE_LIST fm (xs.zip as)) hdisj hlenCs]
  exact map_FLOOKUP_FUPDATE_LIST_zip_not_mem xs ys as fm hdisj hlenAs

/-- Flapjack-specific analogue of Cake `domsub_commutes_fupdate`
(pan_commonPropsScript.sml:319); not an exact HOL port, since it is stated over
the Boolean-`BEq` `FDOMSUB`: domain subtraction at a key absent from the update
list commutes with the list update. -/
theorem FDOMSUB_FUPDATE_LIST_commutes [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List β) (fm : FiniteMap α β) (x : α)
    (h : x ∉ xs) (hlen : xs.length = ys.length) :
    FDOMSUB (FUPDATE_LIST fm (xs.zip ys)) x =
      FUPDATE_LIST (FDOMSUB fm x) (xs.zip ys) := by
  induction xs generalizing fm ys with
  | nil =>
    cases ys with
    | nil => simp [FUPDATE_LIST_nil]
    | cons y ys => simp at hlen
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hne : x ≠ a := by
        intro he
        exact h (by simp [he])
      have htail : x ∉ xs := by
        intro hmem
        exact h (by simp [hmem])
      have hlenTail : xs.length = ys.length := by simpa using hlen
      rw [List.zip_cons_cons, FUPDATE_LIST_cons]
      rw [ih ys (FUPDATE fm (a, y)) htail hlenTail]
      rw [FDOMSUB_FUPDATE_neq fm x a y hne]
      rw [FUPDATE_LIST_cons]

/-- Flapjack-specific analogue of Cake `update_eq_zip_flookup`
(pan_commonPropsScript.sml:244); not an exact HOL port: a key occurring in a
distinct key list looks up its paired value in the updated map. -/
theorem FLOOKUP_FUPDATE_LIST_zip_getElem [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List β) (f : FiniteMap α β) (n : Nat)
    (hdistinct : xs.Nodup) (hlen : xs.length = ys.length) (hn : n < xs.length) :
    FLOOKUP (FUPDATE_LIST f (xs.zip ys)) (xs[n]'hn) =
      some (ys[n]'(by rw [← hlen]; exact hn)) := by
  induction xs generalizing f ys n with
  | nil => simp at hn
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [List.nodup_cons] at hdistinct
      obtain ⟨ha, hdistinctTail⟩ := hdistinct
      have hlenTail : xs.length = ys.length := by simpa using hlen
      cases n with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [List.zip_cons_cons, FUPDATE_LIST_cons]
        rw [FLOOKUP_FUPDATE_LIST_not_mem (FUPDATE f (a, y)) (xs.zip ys) a
          (by rw [List.map_fst_zip (by omega)]; exact ha)]
        rw [FLOOKUP_update]
        simp
      | succ k =>
        have hk : k < xs.length := by
          simp only [List.length_cons] at hn
          omega
        simp only [List.getElem_cons_succ]
        rw [List.zip_cons_cons, FUPDATE_LIST_cons]
        exact ih ys (FUPDATE f (a, y)) k hdistinctTail hlenTail hk

/-- Domain subtraction at a key that is not bound leaves the map unchanged. -/
theorem FDOMSUB_eq_self_of_lookup_none [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (x : α) (h : FLOOKUP f x = none) :
    FDOMSUB f x = f := by
  funext k
  by_cases hk : (x == k) = true
  · simp only [FDOMSUB, hk, if_true]
    rw [← beq_iff_eq.mp hk]
    exact h.symm
  · simp only [FDOMSUB, hk, Bool.false_eq_true, if_false]

/-- Updating a key with the value it already binds leaves the map unchanged. -/
theorem FUPDATE_eq_self_of_lookup_some [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (x : α) (v : β) (h : FLOOKUP f x = some v) :
    FUPDATE f (x, v) = f := by
  funext k
  by_cases hk : (x == k) = true
  · simp only [FUPDATE, hk, if_true]
    rw [← beq_iff_eq.mp hk]
    exact h.symm
  · simp only [FUPDATE, hk, Bool.false_eq_true, if_false]

/-- Domain subtraction at a key immediately after updating that same key. -/
theorem FDOMSUB_FUPDATE_same [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (x : α) (v : β) :
    FDOMSUB (FUPDATE f (x, v)) x = FDOMSUB f x := by
  funext k
  by_cases hk : (x == k) = true
  · simp only [FDOMSUB, FUPDATE, hk, if_true]
  · simp only [FDOMSUB, FUPDATE, hk, Bool.false_eq_true, if_false]

/-- Two consecutive updates of the same key collapse to the later one. -/
theorem FUPDATE_FUPDATE_same [BEq α] [LawfulBEq α]
    (f : FiniteMap α β) (x : α) (v1 v2 : β) :
    FUPDATE (FUPDATE f (x, v1)) (x, v2) = FUPDATE f (x, v2) := by
  funext k
  by_cases hk : (x == k) = true
  · simp only [FUPDATE, hk, if_true]
  · simp only [FUPDATE, hk, Bool.false_eq_true, if_false]

/-- Flapjack-specific analogue of Cake `res_var_lookup_original_eq`
(crepPropsScript.sml:612); not an exact HOL port, since it is stated over this
file's `resVar`: folding `res_var` over the `ZIP` of a distinct key list with its
values, restoring each key's original binding, reproduces the original map. -/
theorem foldl_resVar_zip_lookup_original [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List β) (lc : FiniteMap α β)
    (hdistinct : xs.Nodup) (hlen : xs.length = ys.length) :
    ((xs.zip (xs.map (FLOOKUP lc))).foldl resVar
        (FUPDATE_LIST lc (xs.zip ys))) = lc := by
  induction xs generalizing ys lc with
  | nil =>
    cases ys with
    | nil => simp [FUPDATE_LIST_nil]
    | cons y ys => simp at hlen
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [List.nodup_cons] at hdistinct
      obtain ⟨ha, hdistinctTail⟩ := hdistinct
      have hlenTail : xs.length = ys.length := by simpa using hlen
      have hnotmem : a ∉ (xs.zip ys).map Prod.fst := by
        rw [List.map_fst_zip (by omega)]
        exact ha
      simp only [List.map_cons, List.zip_cons_cons, FUPDATE_LIST_cons, List.foldl_cons]
      rw [← FUPDATE_FUPDATE_LIST_commutes lc a y (xs.zip ys) hnotmem]
      cases hlookup : FLOOKUP lc a with
      | none =>
        simp only [resVar, FDOMSUB_FUPDATE_same]
        rw [FDOMSUB_FUPDATE_LIST_commutes xs ys lc a ha hlenTail,
            FDOMSUB_eq_self_of_lookup_none lc a hlookup]
        exact ih ys lc hdistinctTail hlenTail
      | some v =>
        simp only [resVar]
        rw [FUPDATE_FUPDATE_same]
        rw [FUPDATE_eq_self_of_lookup_some (FUPDATE_LIST lc (xs.zip ys)) a v
          (by rw [FLOOKUP_FUPDATE_LIST_zip_not_mem xs ys lc a hlenTail ha]; exact hlookup)]
        exact ih ys lc hdistinctTail hlenTail

end Flapjack
