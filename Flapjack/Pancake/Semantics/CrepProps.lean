import Flapjack.HolRef
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.Semantics.CrepSem.Eval

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

/-- Faithful Lean port of Cake `crepProps$lookup_locals_eq_map_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml:17`). The HOL statement
    applies `crepSem.eval` only to `Var` expressions. Its defining `Var`
    equation is implemented directly by `crepSemEvalExp_var`; HOL
    `OPT_MMAP` therefore translates to `List.mapM` over the same local
    lookup. The theorem does not use the compatibility evaluator
    `evalCrepFullExpState`, nor does it claim a whole-evaluator equivalence.

    The representation translation erases HOL's sole `word_lab` constructor
    `Word`: a HOL lookup of `SOME (Word w)` corresponds to Lean's `some w`,
    and absent entries correspond to `none`. Thus a HOL finite `locals` map
    translates to the Lean lookup function `state.locals`. The runtime type
    carries extra evaluator dictionaries, but this theorem's only semantic
    case is the direct HOL `Var` clause.

    Scope boundary: this tag is for the variable-only theorem, not a claim that
    `crepSemEvalExp` ports all of HOL `eval_def`. In particular, Lean stores
    memory as `α → Option α` with a Boolean domain and globals as
    `α → Option α`; HOL stores total word memory with a separate address set,
    and globals keyed by fixed-width 5-bit words with `word_lab` values. The
    Lean `loadGlob` AST index is also `α`, whereas HOL's is 5-bit. None of
    those fields or constructors is observed by this theorem. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "lookup_locals_eq_map_vars"]
theorem lookup_locals_eq_map_vars
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (names : List Nat) :
    names.mapM state.locals =
      (names.map (CrepExp.var (α := α))).mapM
        (crepSemEvalExp state) := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [List.mapM_cons, List.map_cons, crepSemEvalExp_var, ih]

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
theorem loadGlobals_length {α : Type u} [OfNat α 1] [Add α]
    (address : α) (count : Nat) :
    (loadGlobals address count).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadGlobals, ih]

/-! Faithful width-polymorphic port of Cake
    `crepProps$el_load_globals_elem`
    (`cakeml/pancake/semantics/crepPropsScript.sml:474`). The Lean `BitVec`
    specializes HOL's polymorphic word, `BitVec.ofNat` represents `n2w`, and
    the bound lets Lean use total list indexing just as HOL's `EL` does. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "el_load_globals_elem"]
theorem loadGlobals_getElem {width : Nat}
    (address : BitVec width) (count n : Nat) (h : n < count) :
    (loadGlobals address count)[n]'(by
      simpa only [loadGlobals_length] using h) =
        .loadGlob (address + BitVec.ofNat width n) := by
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
              (address + 1) + BitVec.ofNat width n =
                address + BitVec.ofNat width (n + 1) := by
            rw [BitVec.ofNat_add]
            simp
            ac_rfl
          rw [haddr]

/-- Faithful port of Cake `crepProps$var_cexp_load_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:698`): the loads generated by
    `load_globals` contain no local variables. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "var_cexp_load_globals_empty"]
theorem loadGlobals_crepExpVars_empty {α : Type u} [OfNat α 1] [Add α]
    (address : α) (count : Nat) :
    (loadGlobals address count).flatMap crepExpVars = [] := by
  induction count generalizing address with
  | zero => simp [loadGlobals]
  | succ count ih => simp [loadGlobals, ih, crepExpVars]

/-! Faithful port of Cake `crepProps$assigned_free_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:458`). -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_store_globals_empty"]
theorem crepAssignedFreeVars_nestedSeq_storeGlobals {α : Type u}
    [OfNat α 1] [Add α]
    (address : α) (values : List (CrepExp α)) :
    crepAssignedFreeVars (crepNestedSeq (storeGlobals address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobals, crepNestedSeq, crepAssignedFreeVars]
  | cons value values ih =>
      simp [storeGlobals, crepNestedSeq, crepAssignedFreeVars, ih]

/-! Faithful port of Cake `crepProps$assigned_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:449`). -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_store_globals_empty"]
theorem crepAssignedVars_nestedSeq_storeGlobals {α : Type u}
    [OfNat α 1] [Add α]
    (address : α) (values : List (CrepExp α)) :
    crepAssignedVars (crepNestedSeq (storeGlobals address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobals, crepNestedSeq, crepAssignedVars]
  | cons value values ih =>
      simp [storeGlobals, crepNestedSeq, crepAssignedVars, ih]

end Flapjack
