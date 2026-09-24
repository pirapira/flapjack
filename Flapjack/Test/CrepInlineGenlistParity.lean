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
  pure (genlistOk && maxListOk && maxGenlistOk && contResOk && map2Ok && fdomOk && fdomSubsetOk)

end Flapjack.Test.CrepInlineGenlistParity