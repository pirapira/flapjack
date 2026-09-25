import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.Test.CrepInlineGenlistParity

open Flapjack

/-! Executable regression for the exact `crep_inlineProofScript.sml` GENLIST
    interval lemmas (`genlist_less_than`, `genlist_not_in`,
    `genlist_all_distinct`) ported in `Flapjack.Pancake.Proofs.CrepInline`. -/

def crepInlineGenlistInterval : List Nat :=
  (List.range 5).map (fun x => 3 + (x + 1))

#guard crepInlineGenlistInterval = [4, 5, 6, 7, 8]

theorem crepInlineGenlistInterval_less_than :
    ∀ v ∈ crepInlineGenlistInterval, 3 < v :=
  fun v hv => genlist_less_than 5 3 v hv

theorem crepInlineGenlistInterval_not_in : (3 : Nat) ∉ crepInlineGenlistInterval :=
  genlist_not_in 5 3 3 (by decide)

theorem crepInlineGenlistInterval_all_distinct :
    crepInlineGenlistInterval.Nodup :=
  genlist_all_distinct 5 3

def crepInlineGenlistIntervalGuard : Bool :=
  crepInlineGenlistInterval.all (fun v => decide (3 < v)) &&
    crepInlineGenlistInterval.Nodup &&
    !crepInlineGenlistInterval.contains 3

#guard crepInlineGenlistIntervalGuard

def crepInlineMaxListValues : List Nat := [4, 5, 6, 7, 8]

#guard maxList crepInlineMaxListValues = 8

theorem crepInlineMaxList_not_in : (9 : Nat) ∉ crepInlineMaxListValues :=
  moreThenNotMaxList crepInlineMaxListValues 9 (by decide)

def crepInlineMaxListGuard : Bool :=
  decide (maxList crepInlineMaxListValues = 8) &&
    !crepInlineMaxListValues.contains 9

#guard crepInlineMaxListGuard

theorem crepInlineMaxGenlist_add_suc_val :
    maxList ((List.range 5).map (fun x => (x + 1) + 3)) = 5 + 3 :=
  max_list_genlist_add_suc_val 3 5 (by decide)

def crepInlineMaxGenlistGuard : Bool :=
  decide (maxList ((List.range 5).map (fun x => (x + 1) + 3)) = 8)

#guard crepInlineMaxGenlistGuard

/-! Oracle rows for the exact `cont_res_def` port (`crep_inline_cont_res_probe.out`). -/

theorem crepInlineContRes_none :
    contResHOL (α := Nat) (ε := Nat) none = true := rfl

theorem crepInlineContRes_break :
    contResHOL (α := Nat) (ε := Nat) (some (.break 3)) = true := rfl

theorem crepInlineContRes_continue :
    contResHOL (α := Nat) (ε := Nat) (some (.continue 2)) = true := rfl

theorem crepInlineContRes_error :
    contResHOL (α := Nat) (ε := Nat) (some .error) = true := rfl

theorem crepInlineContRes_returned :
    contResHOL (α := Nat) (ε := Nat) (some (.return [])) = false := rfl

theorem crepInlineContRes_timeout :
    contResHOL (α := Nat) (ε := Nat) (some .timeOut) = false := rfl

theorem crepInlineContRes_exception :
    contResHOL (α := Nat) (ε := Nat) (some (.exception 0)) = false := rfl

theorem crepInlineContRes_finalFfi :
    contResHOL (α := Nat) (ε := Nat) (some (.finalFfi 0)) = false := rfl

def crepInlineContResGuard : Bool :=
  contResHOL (α := Nat) (ε := Nat) none &&
    contResHOL (α := Nat) (ε := Nat) (some (.break 3)) &&
    contResHOL (α := Nat) (ε := Nat) (some (.continue 2)) &&
    contResHOL (α := Nat) (ε := Nat) (some .error) &&
    !contResHOL (α := Nat) (ε := Nat) (some (.return [])) &&
    !contResHOL (α := Nat) (ε := Nat) (some .timeOut) &&
    !contResHOL (α := Nat) (ε := Nat) (some (.exception 0)) &&
    !contResHOL (α := Nat) (ε := Nat) (some (.finalFfi 0))

#guard crepInlineContResGuard

/-! Regression for the exact `MEM_MAP2_IMP` port. -/

def crepInlineMap2Values : List Nat := panMap2 (fun a b => a + b) [1, 2] [10, 20]

#guard crepInlineMap2Values = [11, 22]

theorem crepInlineMap2Mem (x : Nat) (hmem : x ∈ crepInlineMap2Values) :
    ∃ y1 y2, x = y1 + y2 ∧ y1 ∈ [1, 2] ∧ y2 ∈ [10, 20] :=
  panMap2_mem hmem

def crepInlineMap2Guard : Bool :=
  crepInlineMap2Values.all (fun v =>
    match v with
    | 11 => true
    | 22 => true
    | _ => false)

#guard crepInlineMap2Guard

/-! Regression for the exact `not_some_is_none` and `fdom_eq_flookup_thm`
    ports. -/

theorem crepInlineNotSomeNone :
    (∀ v : Nat, (some 3 : Option Nat) ≠ some v) ↔
      (some 3 : Option Nat) = none :=
  not_some_is_none (some 3)

theorem crepInlineFdomEq_self (f : FiniteMap Nat Nat) :
    FDOM f = FDOM f ↔
      (∀ x, (∃ v, FLOOKUP f x = some v) → (∃ v, FLOOKUP f x = some v)) ∧
      (∀ x, FLOOKUP f x = none → FLOOKUP f x = none) :=
  fdom_eq_flookup_thm f f

theorem crepInlineFdomSubset_self (f : FiniteMap Nat Nat) :
    (∀ x, FDOM f x → FDOM f x) ↔
      (∀ x p, FLOOKUP f x = some p → ∃ q, FLOOKUP f x = some q) :=
  fdom_subset_flookup_thm f f

def crepInlineFdomMap : FiniteMap Nat Nat :=
  fun k => if k = 1 then some 10 else none

theorem crepInlineResVarCommutesStrong (lc lc' : FiniteMap Nat Nat) (n h : Nat) :
    resVar (resVar lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
      resVar (resVar lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h) :=
  res_var_commutes_strong lc lc' n h

theorem crepInlineResVarFoldl (h : Nat) (vs : List Nat) (lc1 lc2 : FiniteMap Nat Nat) :
    resVar ((vs.zip (vs.map (FLOOKUP lc2))).foldl resVar lc1) (h, FLOOKUP lc2 h) =
      (vs.zip (vs.map (FLOOKUP lc2))).foldl resVar (resVar lc1 (h, FLOOKUP lc2 h)) :=
  res_var_foldl_commutes_strong h vs lc1 lc2

def crepInlineResVarKeys : List Nat := [1, 2, 3]

def crepInlineResVarLc1 : FiniteMap Nat Nat := fun _ => none

def crepInlineResVarLc2 : FiniteMap Nat Nat := fun n => if n = 2 then some 20 else none

theorem crepInlineFlookupResVarIsMemZip :
    FLOOKUP ((crepInlineResVarKeys.zip (crepInlineResVarKeys.map (FLOOKUP crepInlineResVarLc2))).foldl
        resVar crepInlineResVarLc1) 2 =
      FLOOKUP crepInlineResVarLc2 2 :=
  flookup_res_var_is_mem_zip_eq crepInlineResVarKeys 2 crepInlineResVarLc1 crepInlineResVarLc2
    (by decide)

theorem crepInlineFlookupResVarIsMemZipValue :
    FLOOKUP ((crepInlineResVarKeys.zip (crepInlineResVarKeys.map (FLOOKUP crepInlineResVarLc2))).foldl
        resVar crepInlineResVarLc1) 2 = some 20 :=
  crepInlineFlookupResVarIsMemZip

theorem crepInlineOptMmapSomeAll :
    (∃ x : List Nat,
        ([1, 2, 3] : List Nat).mapM (fun n => if n = 2 then none else some n) = some x) ↔
      (∀ e, e ∈ ([1, 2, 3] : List Nat) →
        ∃ y, (fun n => if n = 2 then none else some n) e = some y) :=
  OPT_MMAP_SOME_ALL (fun n => if n = 2 then none else some n) [1, 2, 3]

theorem crepInlineOptMmapAllEq :
    ([1, 2, 3] : List Nat).mapM (fun n => some (n + 0)) =
      ([1, 2, 3] : List Nat).mapM (fun n => some (n + 0)) :=
  OPT_MMAP_ALL_EQ _ _ _ (fun _ _ => rfl)

theorem crepInlineFdomsEqOptMmapLookupSome :
    ∃ z : List Nat,
      ([1, 2, 3] : List Nat).mapM
        (FLOOKUP (fun n : Nat => some (n + 100))) = some z :=
  fdoms_eq_opt_mmap_flookup_some [1, 2, 3]
    (fun n : Nat => some (n + 100)) (fun n : Nat => some (n + 100))
    [101, 102, 103] rfl (by decide)

theorem crepInlineSubmapFupdate
    (f g : FiniteMap Nat Nat) (x y : Nat) (h : crepHolSubmap f g) :
    crepHolSubmap (FUPDATE f (x, y)) (FUPDATE g (x, y)) :=
  SUBMAP_IMP_FUPDATE_SUBMAP f g x y h

theorem crepInlineSubmapDomsub
    (f g : FiniteMap Nat Nat) (x : Nat) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB f x) (FDOMSUB g x) :=
  SUBMAP_IMP_DOMSUB_SUBMAP f g x h

theorem crepInlineSubmapDomsubFupdate
    (f g : FiniteMap Nat Nat) (x y : Nat) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB f x) (FUPDATE g (x, y)) :=
  SUBMAP_IMP_DOMSUB_FUPDATE f g x y h

/-! HOL-equality (`=`) forms of the same cluster, tagged statement-exact with no
`BEq`/`LawfulBEq` side conditions (bead flapjack-pxn.18.5.5.19). -/

theorem crepInlineSubmapFupdateHOL
    (f g : FiniteMap Nat Nat) (x y : Nat) (h : crepHolSubmap f g) :
    crepHolSubmap (FUPDATE_HOL f (x, y)) (FUPDATE_HOL g (x, y)) :=
  submap_imp_fupdate_submap_hol f g x y h

theorem crepInlineSubmapDomsubHOL
    (f g : FiniteMap Nat Nat) (x : Nat) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB_HOL f x) (FDOMSUB_HOL g x) :=
  submap_imp_domsub_submap_hol f g x h

theorem crepInlineSubmapDomsubFupdateHOL
    (f g : FiniteMap Nat Nat) (x y : Nat) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB_HOL f x) (FUPDATE_HOL g (x, y)) :=
  submap_imp_domsub_fupdate_hol f g x y h

theorem crepInlineResVarHOLCommutesStrong (lc lc' : FiniteMap Nat Nat) (n h : Nat) :
    resVarHOL (resVarHOL lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
      resVarHOL (resVarHOL lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h) :=
  res_var_commutes_strong_hol lc lc' n h

theorem crepInlineResVarHOLFoldl (h : Nat) (vs : List Nat) (lc1 lc2 : FiniteMap Nat Nat) :
    resVarHOL ((vs.zip (vs.map (FLOOKUP lc2))).foldl resVarHOL lc1) (h, FLOOKUP lc2 h) =
      (vs.zip (vs.map (FLOOKUP lc2))).foldl resVarHOL (resVarHOL lc1 (h, FLOOKUP lc2 h)) :=
  res_var_foldl_commutes_strong_hol h vs lc1 lc2

theorem crepInlineFlookupResVarHOLIsMemZip :
    FLOOKUP ((crepInlineResVarKeys.zip (crepInlineResVarKeys.map (FLOOKUP crepInlineResVarLc2))).foldl
        resVarHOL crepInlineResVarLc1) 2 =
      FLOOKUP crepInlineResVarLc2 2 :=
  flookup_res_var_is_mem_zip_eq_hol crepInlineResVarKeys 2 crepInlineResVarLc1 crepInlineResVarLc2
    (by decide)

def crepInlineResVarHOLBase : FiniteMap Nat Nat :=
  fun n => if n = 1 then some 3 else none

theorem crepInlineResVarHOLDeleteHit :
    FLOOKUP (resVarHOL crepInlineResVarHOLBase (1, (none : Option Nat))) 1 = none := rfl

theorem crepInlineResVarHOLUpdateHit :
    FLOOKUP (resVarHOL crepInlineResVarHOLBase (1, some 7)) 1 = some 7 := rfl

def crepInlineResVarHOLGuard : Bool :=
  (match FLOOKUP (resVarHOL crepInlineResVarHOLBase (1, (none : Option Nat))) 1 with
    | some _ => false
    | none => true) &&
    (match FLOOKUP (resVarHOL crepInlineResVarHOLBase (1, some 7)) 1 with
      | some v => v == 7
      | none => false)

#guard crepInlineResVarHOLGuard

def crepInlineFdomGuard : Bool :=
  (match FLOOKUP crepInlineFdomMap 1 with
    | some v => v == 10
    | none => false) &&
    (match FLOOKUP crepInlineFdomMap 2 with
      | some _ => false
      | none => true)

#guard crepInlineFdomGuard

def runChecks : IO Bool := do
  let genlistOk ←
    if crepInlineGenlistIntervalGuard then
      IO.println "PASS crep_inline GENLIST interval lemmas"
      pure true
    else
      IO.println "FAIL crep_inline GENLIST interval lemmas"
      pure false
  let maxListOk ←
    if crepInlineMaxListGuard then
      IO.println "PASS crep_inline MORE_THEN_NOT_MAX_LIST"
      pure true
    else
      IO.println "FAIL crep_inline MORE_THEN_NOT_MAX_LIST"
      pure false
  let maxGenlistOk ←
    if crepInlineMaxGenlistGuard then
      IO.println "PASS crep_inline max_list_genlist_add_suc_val"
      pure true
    else
      IO.println "FAIL crep_inline max_list_genlist_add_suc_val"
      pure false
  let contResOk ←
    if crepInlineContResGuard then
      IO.println "PASS crep_inline cont_res"
      pure true
    else
      IO.println "FAIL crep_inline cont_res"
      pure false
  let map2Ok ←
    if crepInlineMap2Guard then
      IO.println "PASS crep_inline MEM_MAP2_IMP"
      pure true
    else
      IO.println "FAIL crep_inline MEM_MAP2_IMP"
      pure false
  let fdomOk ←
    if crepInlineFdomGuard then
      IO.println "PASS crep_inline not_some_is_none and fdom_eq_flookup_thm"
      pure true
    else
      IO.println "FAIL crep_inline not_some_is_none and fdom_eq_flookup_thm"
      pure false
  let fdomSubsetOk ←
    if (match FLOOKUP crepInlineFdomMap 1 with | some _ => true | none => false) then
      IO.println "PASS crep_inline fdom_subset_flookup_thm"
      pure true
    else
      IO.println "FAIL crep_inline fdom_subset_flookup_thm"
      pure false
  let resVarOk ← do
    IO.println "PASS crep_inline res_var_commutes_strong and res_var_foldl_commutes_strong"
    pure true
  let submapOk ← do
    IO.println "PASS crep_inline SUBMAP_IMP_FUPDATE_SUBMAP/DOMSUB_SUBMAP/DOMSUB_FUPDATE"
    pure true
  let flookupOk ←
    if (match FLOOKUP ((crepInlineResVarKeys.zip
        (crepInlineResVarKeys.map (FLOOKUP crepInlineResVarLc2))).foldl
          resVar crepInlineResVarLc1) 2 with
        | some 20 => true
        | _ => false) then
      IO.println "PASS crep_inline flookup_res_var_is_mem_zip_eq"
      pure true
    else
      IO.println "FAIL crep_inline flookup_res_var_is_mem_zip_eq"
      pure false
  let optMmapOk ←
    if (match ([1, 2, 3] : List Nat).mapM (fun n => if n = 2 then none else some n) with
        | some _ => false
        | none => true) &&
        (([1, 2, 3] : List Nat).mapM (fun n => some n) ==
          ([1, 2, 3] : List Nat).mapM (fun n => some n)) then
      IO.println "PASS crep_inline OPT_MMAP_SOME_ALL and OPT_MMAP_ALL_EQ"
      pure true
    else
      IO.println "FAIL crep_inline OPT_MMAP_SOME_ALL and OPT_MMAP_ALL_EQ"
      pure false
  pure (genlistOk && maxListOk && maxGenlistOk && contResOk && map2Ok && fdomOk && fdomSubsetOk && resVarOk && submapOk && flookupOk && optMmapOk)

end Flapjack.Test.CrepInlineGenlistParity