import Flapjack.HolRef
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.Semantics.CrepSem

/-!
Crepe language properties from `cakeml/pancake/semantics/crepPropsScript.sml`.

This module depends on the language definitions and helpers in `CrepLang`;
the language module does not depend on these semantic properties.
-/

namespace Flapjack

universe u

/-- Faithful port of Cake `crepProps$cexp_heads_simp_def`
    (`cakeml/pancake/semantics/crepPropsScript.sml:11`). HOL rejects the
    argument when any inner list is empty, then maps total `HD` over the lists.
    The Lean default `.var 0` gives `headD` a total empty-list value; the guard
    makes that value unreachable in the result. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "cexp_heads_simp_def"]
def cexpHeadsSimp : List (List (CrepExp α)) → Option (List (CrepExp α))
  | expressions =>
      if expressions.any List.isEmpty then none
      else some (expressions.map (fun expression => expression.headD (.var 0)))

mutual
/-- Faithful port of Cake `crepProps$every_exp` from
    `cakeml/pancake/semantics/crepPropsScript.sml:1300`: `every_exp P e`
    holds when `P` holds of `e` and of every subexpression of `e`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "every_exp_def"]
def crepEveryExp (predicate : CrepExp α → Bool) : CrepExp α → Bool
  | .const value => predicate (.const value)
  | .var name => predicate (.var name)
  | .load address => predicate (.load address) && crepEveryExp predicate address
  | .load32 address => predicate (.load32 address) && crepEveryExp predicate address
  | .loadByte address => predicate (.loadByte address) && crepEveryExp predicate address
  | .loadGlob address => predicate (.loadGlob address)
  | .op operator arguments =>
      predicate (.op operator arguments) && crepEveryExpList predicate arguments
  | .crepOp operator arguments =>
      predicate (.crepOp operator arguments) && crepEveryExpList predicate arguments
  | .cmp operator left right =>
      predicate (.cmp operator left right) && crepEveryExp predicate left &&
        crepEveryExp predicate right
  | .shift operator left right =>
      predicate (.shift operator left right) && crepEveryExp predicate left &&
        crepEveryExp predicate right
  | .baseAddr => predicate .baseAddr
  | .topAddr => predicate .topAddr
/-- Cake's `EVERY (every_exp P)` list traversal. -/
def crepEveryExpList (predicate : CrepExp α → Bool) : List (CrepExp α) → Bool
  | [] => true
  | expression :: expressions =>
      crepEveryExp predicate expression && crepEveryExpList predicate expressions
end

/-- HOL `map_var_cexp_eq_var`: mapping `Var` over a list and flattening each
    expression's variable list recovers the original list. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "map_var_cexp_eq_var"]
theorem map_var_crepExpVars_eq {α : Type} (names : List Nat) :
    (names.map (CrepExp.var (α := α))).flatMap crepExpVars = names := by
  induction names with
  | nil => rfl
  | cons name names ih => simp [crepExpVars_var, ih]

/-- Flapjack-specific infrastructure: the length result for the pipeline's
    general-stride `loadShape`.  This is not a HOL port, because it quantifies an
    explicit stride; the exact HOL counterpart is `length_loadShape_eq_shape`. -/
theorem loadShape_length [BEq α] [OfNat α 0] [Add α]
    (address stride : α) (count : Nat) (value : CrepExp α) :
    (loadShape address stride count value).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadShape, ih]

/-- Faithful port of Cake `crepProps$length_load_shape_eq_shape`
    (`cakeml/pancake/semantics/crepPropsScript.sml:30`), stated over the fixed
    `byte$bytes_in_word` stride.  The `CrepBytesInWord` instance supplies the
    fixed byte width, so the explicit quantified variables are HOL's `n a e`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "length_load_shape_eq_shape"]
theorem length_loadShape_eq_shape [BEq α] [OfNat α 0] [Add α] [CrepBytesInWord α]
    (count : Nat) (address : α) (value : CrepExp α) :
    (loadShapeBytes address count value).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadShapeBytes, ih]

/-! Faithful port of Cake `crepProps$length_load_globals_eq_read_size`
    (`cakeml/pancake/semantics/crepPropsScript.sml:467`). -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "length_load_globals_eq_read_size"]
theorem loadGlobals_length {α : Type u}
    (address : BitVec 5) (count : Nat) :
    (loadGlobals (α := α) address count).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadGlobals, ih]

/-! Faithful port of Cake
    `crepProps$el_load_globals_elem`
    (`cakeml/pancake/semantics/crepPropsScript.sml:474`). The Lean `BitVec`
    specializes HOL's polymorphic word, `BitVec.ofNat` represents `n2w`, and
    the bound lets Lean use total list indexing just as HOL's `EL` does. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "el_load_globals_elem"]
theorem loadGlobals_getElem
    (address : BitVec 5) (count n : Nat) (h : n < count) :
    (loadGlobals (α := α) address count)[n]'(by
      simpa only [loadGlobals_length] using h) =
        .loadGlob (address + BitVec.ofNat 5 n) := by
  induction count generalizing address n with
  | zero => omega
  | succ count ih =>
      cases n with
      | zero => simp [loadGlobals]
      | succ n =>
          have hlt : n < count := by omega
          simp only [loadGlobals, List.getElem_cons_succ]
          rw [ih (address := address + 1) (n := n) hlt]
          have haddr :
              (address + 1) + BitVec.ofNat 5 n =
                address + BitVec.ofNat 5 (n + 1) := by
            rw [BitVec.ofNat_add]
            simp
            ac_rfl
          rw [haddr]

/-- Faithful port of Cake `crepProps$var_cexp_load_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:698`): the loads generated by
    `load_globals` contain no local variables. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "var_cexp_load_globals_empty"]
theorem loadGlobals_crepExpVars_empty {α : Type u}
    (address : BitVec 5) (count : Nat) :
    (loadGlobals (α := α) address count).flatMap crepExpVars = [] := by
  induction count generalizing address with
  | zero => simp [loadGlobals]
  | succ count ih => simp [loadGlobals, ih, crepExpVars]

/-! Faithful port of Cake `crepProps$assigned_free_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:458`). -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_store_globals_empty"]
theorem crepAssignedFreeVars_nestedSeq_storeGlobals {α : Type u}
    (address : BitVec 5) (values : List (CrepExp α)) :
    crepAssignedFreeVars (crepNestedSeq (storeGlobals (α := α) address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobals, crepNestedSeq, crepAssignedFreeVars]
  | cons value values ih =>
      simp [storeGlobals, crepNestedSeq, crepAssignedFreeVars, ih]

/-! Faithful port of Cake `crepProps$assigned_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:449`). -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_store_globals_empty"]
theorem crepAssignedVars_nestedSeq_storeGlobals {α : Type u}
    (address : BitVec 5) (values : List (CrepExp α)) :
    crepAssignedVars (crepNestedSeq (storeGlobals (α := α) address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobals, crepNestedSeq, crepAssignedVars]
  | cons value values ih =>
      simp [storeGlobals, crepNestedSeq, crepAssignedVars, ih]

/-- Faithful port of Cake `crepProps$assigned_free_vars_IMP_assigned_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml:373`): every free variable of
    a program is an assigned variable of that program. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_IMP_assigned_vars"]
theorem mem_crepAssignedFreeVars_imp_mem_crepAssignedVars (program : CrepProg α) (name : Nat)
    (h : name ∈ crepAssignedFreeVars program) : name ∈ crepAssignedVars program := by
  revert h
  induction program using crepAssignedFreeVars.induct with
  | case1 => intro h; simp [crepAssignedFreeVars] at h
  | case2 => intro h; simp_all [crepAssignedFreeVars, crepAssignedVars]
  | case3 => intro h; simpa [crepAssignedFreeVars, crepAssignedVars] using h
  | case4 => intro h; simpa [crepAssignedFreeVars, crepAssignedVars] using h
  | case5 =>
      intro h
      simp only [crepAssignedFreeVars, crepAssignedVars, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case6 =>
      intro h
      simp only [crepAssignedFreeVars, crepAssignedVars, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case7 => intro h; simp_all [crepAssignedFreeVars, crepAssignedVars]
  | case8 =>
      intro h
      simp only [crepAssignedFreeVars, crepAssignedVars, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case9 => intro h; simpa [crepAssignedFreeVars, crepAssignedVars] using h
  | case10 => intro h; simpa [crepAssignedFreeVars, crepAssignedVars] using h
  | case11 => intro h; simp [crepAssignedFreeVars] at h

/-- Faithful port of Cake `crepProps$nested_seq_assigned_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:411`): the assignments
    generated by `nested_seq (MAP2 Assign ns vs)` assign exactly `ns`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "nested_seq_assigned_vars_eq"]
theorem crepAssignedVars_nestedSeq_assign_zipWith (names : List Nat)
    (values : List (CrepExp α)) (h : names.length = values.length) :
    crepAssignedVars
        (crepNestedSeq
          (names.zipWith (fun name value => CrepProg.assign name value) values)) =
      names := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => simp [crepNestedSeq, crepAssignedVars]
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.zipWith_cons_cons, List.length_cons] at h ⊢
          simp [crepNestedSeq, crepAssignedVars, ih values (by omega)]

/-- Faithful port of Cake `crepProps$nested_seq_assigned_free_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:420`): the assignments
    generated by `nested_seq (MAP2 Assign ns vs)` assign exactly `ns`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "nested_seq_assigned_free_vars_eq"]
theorem crepAssignedFreeVars_nestedSeq_assign_zipWith {α : Type u} (names : List Nat)
    (values : List (CrepExp α)) (h : names.length = values.length) :
    crepAssignedFreeVars
        (crepNestedSeq
          (names.zipWith (fun name value => CrepProg.assign name value) values)) =
      names := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => simp [crepNestedSeq, crepAssignedFreeVars]
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.zipWith_cons_cons, List.length_cons] at h ⊢
          simp [crepNestedSeq, crepAssignedFreeVars, ih values (by omega)]

/-- Untagged production adapter: writing a `word_lab` global cell on the
    14-field `CrepRuntimeState` leaves every local binding unchanged. HOL's
    exact `FLOOKUP_set_globals` (crepPropsScript.sml:297) is over the 11-field
    state and is ported as `flookup_setCrepHolGlobals_locals`. -/
theorem flookup_setCrepRuntimeGlobals_locals {α σ : Type}
    (gv : BitVec 5) (w : PanWordLab α) (s : CrepRuntimeState α σ) (n : Nat) :
    FLOOKUP (setCrepRuntimeGlobals gv w s).locals n = FLOOKUP s.locals n :=
  rfl

/-- Exact HOL-shaped port of Cake `crepProps$FLOOKUP_set_globals`
    (`cakeml/pancake/semantics/crepPropsScript.sml:297`) over the 11-field
    `CrepHolState`: `FLOOKUP (set_globals gv w s).locals n = FLOOKUP s.locals n`.
    The globals update is the tagged `setCrepHolGlobals` (`set_globals_def`). -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "FLOOKUP_set_globals"]
theorem flookup_setCrepHolGlobals_locals {α σ : Type}
    (gv : BitVec 5) (w : PanWordLab α) (s : CrepHolState α σ) (n : Nat) :
    FLOOKUP (setCrepHolGlobals gv w s).locals n = FLOOKUP s.locals n :=
  rfl

/-! Membership equations for `crepAssignedFreeVars`, exposing Cake's
`assigned_free_vars_def` (`cakeml/pancake/crepLangScript.sml:149`) clause by
clause.  These keep the `not_mem_context_assigned_mem_gt` induction from
unfolding the well-founded definition at every `compileProgHOL` branch. -/

theorem mem_crepAssignedFreeVars_assign {α : Type u} (name : Nat)
    (value : CrepExp α) (x : Nat) :
    x ∈ crepAssignedFreeVars (.assign name value : CrepProg α) ↔ x = name := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_primitive {α : Type u} (names : List Nat)
    (operator : PrimOp) (arguments : List Nat) (x : Nat) :
    x ∈ crepAssignedFreeVars (.primitive names operator arguments : CrepProg α) ↔
      x ∈ names := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_seq {α : Type u} (first second : CrepProg α)
    (x : Nat) :
    x ∈ crepAssignedFreeVars (.seq first second) ↔
      x ∈ crepAssignedFreeVars first ∨ x ∈ crepAssignedFreeVars second := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_ite {α : Type u} (condition : CrepExp α)
    (thenBranch elseBranch : CrepProg α) (x : Nat) :
    x ∈ crepAssignedFreeVars (.ite condition thenBranch elseBranch) ↔
      x ∈ crepAssignedFreeVars thenBranch ∨ x ∈ crepAssignedFreeVars elseBranch := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_while {α : Type u} (condition : CrepExp α)
    (body : CrepProg α) (x : Nat) :
    x ∈ crepAssignedFreeVars (.while condition body) ↔
      x ∈ crepAssignedFreeVars body := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_shMem {α : Type u} (operator : CrepMemOp)
    (name : Nat) (address : CrepExp α) (x : Nat) :
    x ∈ crepAssignedFreeVars (.shMem operator name address) ↔ x = name := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_call_some_some {α : Type u} (returns : List Nat)
    (code : α) (handler : CrepProg α) (name : FunName)
    (arguments : List (CrepExp α)) (x : Nat) :
    x ∈ crepAssignedFreeVars (.call (some (returns, some (code, handler))) name arguments) ↔
      x ∈ returns ∨ x ∈ crepAssignedFreeVars handler := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_call_some_none {α : Type u} (returns : List Nat)
    (name : FunName) (arguments : List (CrepExp α)) (x : Nat) :
    x ∈ crepAssignedFreeVars (.call (some (returns, none)) name arguments) ↔
      x ∈ returns := by
  simp [crepAssignedFreeVars]

end Flapjack
