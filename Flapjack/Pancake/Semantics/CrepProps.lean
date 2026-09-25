import Flapjack.HolRef
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.CrepLang.Prog
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
    makes that value unreachable in the result.

    FLAPJACK-SPECIFIC (not an exact HOL port): generic over `CrepExp α`, while
    HOL `crepLang$exp` is indexed by the word length. The exact width-indexed
    tag is on `cexpHeadsSimpW` below. -/
def cexpHeadsSimp : List (List (CrepExp α)) → Option (List (CrepExp α))
  | expressions =>
      if expressions.any List.isEmpty then none
      else some (expressions.map (fun expression => expression.headD (.var 0)))

/-- Exact width-indexed counterpart of HOL `cexp_heads_simp_def` over
    `CrepExp (BitVec width)`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "cexp_heads_simp_def"]
def cexpHeadsSimpW {width : Nat} [NeZero width]
    (expressions : List (List (CrepExp (BitVec width)))) :
    Option (List (CrepExp (BitVec width))) :=
  cexpHeadsSimp expressions

mutual
/-- Faithful port of Cake `crepProps$every_exp` from
    `cakeml/pancake/semantics/crepPropsScript.sml:1300`: `every_exp P e`
    holds when `P` holds of `e` and of every subexpression of `e`.

    FLAPJACK-SPECIFIC (not an exact HOL port): generic over `CrepExp α`, while
    HOL `crepLang$exp` is indexed by the word length. The exact width-indexed
    tag is on `crepEveryExpW` below. -/
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

/-- Exact width-indexed counterpart of HOL `every_exp_def` over
    `CrepExp (BitVec width)`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "every_exp_def"]
def crepEveryExpW {width : Nat} [NeZero width]
    (predicate : CrepExp (BitVec width) → Bool)
    (expression : CrepExp (BitVec width)) : Bool :=
  crepEveryExp predicate expression

/-- HOL `map_var_cexp_eq_var`: mapping `Var` over a list and flattening each
    expression's variable list recovers the original list. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type,
-- while HOL `prog`/`exp` are indexed by the word length.  The exact width-indexed
-- tag is on the corresponding `map_var_crepExpVars_eqW` declaration below.
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
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type.
-- HOL's exact expression-carrier theorem is `length_loadShapeHOLW` in
-- this module below; this production helper remains useful for generic code.
theorem length_loadShape_eq_shape [BEq α] [OfNat α 0] [Add α] [CrepBytesInWord α]
    (count : Nat) (address : α) (value : CrepExp α) :
    (loadShapeBytes address count value).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadShapeBytes, ih]

/-! Faithful port of Cake `crepProps$length_load_globals_eq_read_size`
    (`cakeml/pancake/semantics/crepPropsScript.sml:467`). -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type,
-- while HOL `prog`/`exp` are indexed by the word length.  The exact width-indexed
-- tag is on the corresponding `loadGlobals_lengthW` declaration below.
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
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type,
-- while HOL `prog`/`exp` are indexed by the word length.  The exact width-indexed
-- tag is on the corresponding `loadGlobals_getElemW` declaration below.
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
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type,
-- while HOL `prog`/`exp` are indexed by the word length.  The exact width-indexed
-- tag is on the corresponding `loadGlobals_crepExpVars_emptyW` declaration below.
theorem loadGlobals_crepExpVars_empty {α : Type u}
    (address : BitVec 5) (count : Nat) :
    (loadGlobals (α := α) address count).flatMap crepExpVars = [] := by
  induction count generalizing address with
  | zero => simp [loadGlobals]
  | succ count ih => simp [loadGlobals, ih, crepExpVars]

/-! Flapjack analogue of Cake
    `crepProps$assigned_free_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:458`). Its width-specialized
    counterpart below still uses String-backed function names in `CrepProg`,
    unlike HOL's `mlstring` identifiers, so neither declaration is tagged. -/
theorem crepAssignedFreeVars_nestedSeq_storeGlobals {α : Type u}
    (address : BitVec 5) (values : List (CrepExp α)) :
    crepAssignedFreeVars (crepNestedSeq (storeGlobals (α := α) address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobals, crepNestedSeq, crepAssignedFreeVars]
  | cons value values ih =>
      simp [storeGlobals, crepNestedSeq, crepAssignedFreeVars, ih]

/-! Flapjack analogue of Cake `crepProps$assigned_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:449`). Its width-specialized
    counterpart below still uses String-backed function names in `CrepProg`,
    unlike HOL's `mlstring` identifiers, so neither declaration is tagged. -/
theorem crepAssignedVars_nestedSeq_storeGlobals {α : Type u}
    (address : BitVec 5) (values : List (CrepExp α)) :
    crepAssignedVars (crepNestedSeq (storeGlobals (α := α) address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobals, crepNestedSeq, crepAssignedVars]
  | cons value values ih =>
      simp [storeGlobals, crepNestedSeq, crepAssignedVars, ih]

/-- Flapjack analogue of Cake
    `crepProps$assigned_free_vars_IMP_assigned_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml:373`): every free variable of
    a program is an assigned variable of that program. Its width-specialized
    counterpart below still uses String-backed function names in `CrepProg`,
    unlike HOL's `mlstring` identifiers, so neither declaration is tagged; the
    exact `mlstring`/width-indexed port is
    `crepAssignedFreeVarsHOL_imp_crepAssignedVarsHOL` below. -/
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

/-- Exact port of Cake `crepProps$assigned_free_vars_IMP_assigned_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml:373-378`) over the exact
    `CrepProgHOL` carrier (MlString function names and width-indexed words):
    every free variable of a program is an assigned variable of that program. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_IMP_assigned_vars"]
theorem crepAssignedFreeVarsHOL_imp_crepAssignedVarsHOL {width : Nat} [NeZero width]
    (program : CrepProgHOL width) (name : Nat)
    (h : name ∈ crepAssignedFreeVarsHOL program) : name ∈ crepAssignedVarsHOL program := by
  revert h
  induction program using crepAssignedFreeVarsHOL.induct with
  | case1 => intro h; simp [crepAssignedFreeVarsHOL] at h
  | case2 => intro h; simp_all [crepAssignedFreeVarsHOL, crepAssignedVarsHOL]
  | case3 => intro h; simpa [crepAssignedFreeVarsHOL, crepAssignedVarsHOL] using h
  | case4 => intro h; simpa [crepAssignedFreeVarsHOL, crepAssignedVarsHOL] using h
  | case5 =>
      intro h
      simp only [crepAssignedFreeVarsHOL, crepAssignedVarsHOL, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case6 =>
      intro h
      simp only [crepAssignedFreeVarsHOL, crepAssignedVarsHOL, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case7 => intro h; simp_all [crepAssignedFreeVarsHOL, crepAssignedVarsHOL]
  | case8 =>
      intro h
      simp only [crepAssignedFreeVarsHOL, crepAssignedVarsHOL, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case9 => intro h; simpa [crepAssignedFreeVarsHOL, crepAssignedVarsHOL] using h
  | case10 => intro h; simpa [crepAssignedFreeVarsHOL, crepAssignedVarsHOL] using h
  | case11 => intro h; simp [crepAssignedFreeVarsHOL] at h

/-- Production bridge: transporting the exact HOL theorem across `crepProgToHOL`
    recovers the executable `CrepProg` implication, so the exact-carrier port and
    the production property agree. -/
theorem crepAssignedFreeVars_imp_crepAssignedVars_via_HOL {width : Nat} [NeZero width]
    (program : CrepProg (BitVec width)) (name : Nat)
    (h : name ∈ crepAssignedFreeVars program) : name ∈ crepAssignedVars program := by
  have hhol : name ∈ crepAssignedFreeVarsHOL (crepProgToHOL program) := by
    simpa [crepProgToHOL_crepAssignedFreeVars] using h
  have hmem := crepAssignedFreeVarsHOL_imp_crepAssignedVarsHOL (crepProgToHOL program) name hhol
  simpa [crepProgToHOL_crepAssignedVars] using hmem

/-- Flapjack analogue of Cake `crepProps$nested_seq_assigned_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:411`): the assignments
    generated by `nested_seq (MAP2 Assign ns vs)` assign exactly `ns`.

    This and its width-specialized `...W` wrapper remain untagged: both use the
    production `CrepProg` carrier, whose `Call`/`ExtCall` names are Lean
    `String`, while HOL `prog` uses `mlstring`. The exact `CrepProgHOL` carrier
    exists, but `assigned_vars` and this theorem have not yet been ported over
    it. The direct HOL rows in `crep_assigned_vars_probe.out` check concrete
    observations only; they do not bridge the carrier mismatch. -/
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

/-- Flapjack analogue of Cake
    `crepProps$nested_seq_assigned_free_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:420`): the assignments
    generated by `nested_seq (MAP2 Assign ns vs)` assign exactly `ns`. Its
    width-specialized counterpart below still uses String-backed function names
    in `CrepProg`, unlike HOL's `mlstring` identifiers, so neither declaration
    is tagged. -/
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

/-- Variable-form of `nested_seq_assigned_free_vars_eq`: assigning each name
    from a temporary variable still assigns exactly the names. This is the form
    emitted by the non-`distinctLists` branch of `compileProgHOL`. -/
theorem crepAssignedFreeVars_nestedSeq_assign_var_zipWith {α : Type u}
    (names temporaries : List Nat) (h : names.length = temporaries.length) :
    crepAssignedFreeVars
        (crepNestedSeq
          (names.zipWith
            (fun name temporary => CrepProg.assign name (.var temporary : CrepExp α))
            temporaries)) =
      names := by
  induction names generalizing temporaries with
  | nil =>
      cases temporaries with
      | nil => simp [crepNestedSeq, crepAssignedFreeVars]
      | cons temporary temporaries => simp at h
  | cons name names ih =>
      cases temporaries with
      | nil => simp at h
      | cons temporary temporaries =>
          simp only [List.zipWith_cons_cons, List.length_cons] at h ⊢
          simp [crepNestedSeq, crepAssignedFreeVars, ih temporaries (by omega)]

/-- Untagged production adapter: writing a `word_lab` global cell on the
    14-field `CrepRuntimeState` leaves every local binding unchanged. HOL's
    exact `FLOOKUP_set_globals` (crepPropsScript.sml:297) is over the 11-field
    state; the same field equation is proved below over Flapjack's state, whose
    code map still has a String/`mlstring` carrier mismatch. -/
theorem flookup_setCrepRuntimeGlobals_locals {α σ : Type}
    (gv : BitVec 5) (w : PanWordLab α) (s : CrepRuntimeState α σ) (n : Nat) :
    FLOOKUP (setCrepRuntimeGlobals gv w s).locals n = FLOOKUP s.locals n :=
  rfl

/-- Generic-`α` analogue of `crepProps$FLOOKUP_set_globals`, deliberately
    untagged because HOL's state code map is keyed by `mlstring` and stores
    `mlstring`-bearing programs, while Flapjack uses `String`. The width-indexed
    analogue is `flookup_setCrepHolGlobals_localsW` below.
    `FLOOKUP (set_globals gv w s).locals n = FLOOKUP s.locals n`
    (crepPropsScript.sml:297). -/
theorem flookup_setCrepHolGlobals_locals {α σ : Type}
    (gv : BitVec 5) (w : PanWordLab α) (s : CrepHolState α σ) (n : Nat) :
    FLOOKUP (setCrepHolGlobals gv w s).locals n = FLOOKUP s.locals n :=
  rfl

/-- Flapjack width-specialized analogue of Cake `crepProps$FLOOKUP_set_globals`
    (`cakeml/pancake/semantics/crepPropsScript.sml:297-301`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.101`.
    The HOL equation `FLOOKUP (set_globals gv w s).locals n = FLOOKUP s.locals n`
    holds pointwise here (`rfl`), because `setCrepHolGlobalsW` updates only the
    `globals` component, exactly as HOL's `set_globals_def` does
    (crepSemScript.sml:61-63). The mismatch is the quantified whole-state carrier:
    `CrepHolState (BitVec width)` stores `locals`/`globals`/`code` as unrestricted
    `Nat -> Option`, `BitVec 5 -> Option` and `FunName -> Option` functions that
    admit infinite support, a strict superset of HOL's finite maps, and `code` is
    keyed by `FunName = String` rather than `funname = mlstring`
    (crepSemScript.sml:19-32). Because the quantifier ranges over a whole state,
    `names_as_string` cannot qualify the identifier and no `NameRanged` byte
    witness applies. The underlying update boundary is pinned directly by the
    `set_globals_direct=(SOME (Word 22w),SOME (Word 7w),NONE)` row of
    `scripts/hol-probes/crep_store_global_probe.out` (writing global `4w` leaves
    local lookups `3` and `9` unchanged) and sampled by
    `Flapjack/Test/CrepGlobalShapeParity.lean:110-116`. Restoring the tag depends
    on the exact finite-support Crep carrier tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
theorem flookup_setCrepHolGlobals_localsW {width : Nat} [NeZero width] {σ : Type}
    (gv : BitVec 5) (w : PanWordLab (BitVec width))
    (s : CrepHolState (BitVec width) σ) (n : Nat) :
    FLOOKUP (setCrepHolGlobalsW gv w s).locals n = FLOOKUP s.locals n :=
  rfl

/-- Kernel-checked bridge: the width-indexed `FLOOKUP_set_globals` analogue
    agrees with the generic production statement at `BitVec width`. -/
theorem flookup_setCrepHolGlobals_localsW_eq_generic {width : Nat} [NeZero width] {σ : Type}
    (gv : BitVec 5) (w : PanWordLab (BitVec width))
    (s : CrepHolState (BitVec width) σ) (n : Nat) :
    FLOOKUP (setCrepHolGlobalsW gv w s).locals n =
      FLOOKUP (setCrepHolGlobals gv w s).locals n :=
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

/-- Exact HOL `flookup_res_var_distinct_zip_eq` (`crepPropsScript.sml:777`):
    folding `res_var` over the zip of a key list with its values leaves a key
    that is not in the key list untouched. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar` uses Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem flookup_res_var_distinct_zip_eq [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List (Option β)) (fm : FiniteMap α β) (x : α)
    (hlen : xs.length = ys.length) (hx : x ∉ xs) :
    FLOOKUP ((xs.zip ys).foldl resVar fm) x = FLOOKUP fm x :=
  FLOOKUP_foldl_resVar_zip_not_mem xs ys fm x hlen hx

/-- Flapjack analogue of Cake `crepProps$dec_clock_simp`
    (`cakeml/pancake/semantics/crepPropsScript.sml:267-278`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.105`.
    The clause set matches HOL's ten field equations exactly: locals, globals,
    code, memory, memaddrs, sh_memaddrs, be, ffi, base_addr and top_addr are all
    preserved by the clock decrement (`decCrepHolClockW`, itself the analogue of
    `dec_clock_def`). The mismatch is the quantified whole-state carrier:
    `CrepHolState (BitVec width)` stores `locals`/`globals` as unrestricted
    `Nat → Option` / `BitVec 5 → Option` functions and `code` as
    `FunName → Option`, where HOL's `crepSem$state` uses finite maps and
    `funname = mlstring` (crepSemScript.sml:19-32). A whole-state result also
    cannot be authorized by `names_as_string`, and no `NameRanged` byte witness
    applies. Direct HOL rows `dec_clock_clock` / `dec_clock_globals` /
    `dec_clock_be` / `dec_clock_top` are in
    `scripts/hol-probes/crep_dec_clock_simp_probe.out`, and the clause shapes are
    sampled by `Flapjack/Test/CrepGlobalShapeParity.lean:601-605`. No exact
    finite-support carrier exists yet; restoring the tag depends on
    `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
theorem decCrepHolClock_simp {width : Nat} [NeZero width] {σ : Type} (s : CrepHolState (BitVec width) σ) :
    (decCrepHolClockW s).locals = s.locals ∧
      (decCrepHolClockW s).globals = s.globals ∧
      (decCrepHolClockW s).code = s.code ∧
      (decCrepHolClockW s).memory = s.memory ∧
      (decCrepHolClockW s).memaddrs = s.memaddrs ∧
      (decCrepHolClockW s).shMemaddrs = s.shMemaddrs ∧
      (decCrepHolClockW s).bigEndian = s.bigEndian ∧
      (decCrepHolClockW s).ffi = s.ffi ∧
      (decCrepHolClockW s).baseAddress = s.baseAddress ∧
      (decCrepHolClockW s).topAddress = s.topAddress := by
  simp [decCrepHolClockW]

/-- Flapjack analogue of Cake `crepProps$empty_locals_simp`
    (`cakeml/pancake/semantics/crepPropsScript.sml:282-294`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.106`.
    The clause set matches HOL's ten field equations exactly: globals, code,
    memory, memaddrs, sh_memaddrs, clock, be, ffi, base_addr and top_addr are all
    preserved when `locals` is cleared (`emptyCrepHolLocalsW`, itself the
    analogue of `empty_locals_def`). The mismatch is again the quantified
    whole-state carrier: `CrepHolState (BitVec width)` stores `locals`/`globals`
    as unrestricted `Nat → Option` / `BitVec 5 → Option` functions and `code` as
    `FunName → Option`, where HOL's `crepSem$state` uses finite maps and
    `funname = mlstring` (crepSemScript.sml:19-32). A whole-state result also
    cannot be authorized by `names_as_string`, and no `NameRanged` byte witness
    applies. Direct HOL rows `empty_locals_locals` / `empty_locals_clock` /
    `empty_locals_memory` are in
    `scripts/hol-probes/crep_dec_clock_simp_probe.out`, with
    `empty_locals_none` / `empty_locals_fields_preserved` in
    `scripts/hol-probes/crep_local_updates_probe.out`; the clause shapes are
    sampled by `Flapjack/Test/CrepGlobalShapeParity.lean:608-612`. No exact
    finite-support carrier exists yet; restoring the tag depends on
    `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
theorem emptyCrepHolLocals_simp {width : Nat} [NeZero width] {σ : Type} (s : CrepHolState (BitVec width) σ) :
    (emptyCrepHolLocalsW s).globals = s.globals ∧
      (emptyCrepHolLocalsW s).code = s.code ∧
      (emptyCrepHolLocalsW s).memory = s.memory ∧
      (emptyCrepHolLocalsW s).memaddrs = s.memaddrs ∧
      (emptyCrepHolLocalsW s).shMemaddrs = s.shMemaddrs ∧
      (emptyCrepHolLocalsW s).clock = s.clock ∧
      (emptyCrepHolLocalsW s).bigEndian = s.bigEndian ∧
      (emptyCrepHolLocalsW s).ffi = s.ffi ∧
      (emptyCrepHolLocalsW s).baseAddress = s.baseAddress ∧
      (emptyCrepHolLocalsW s).topAddress = s.topAddress := by
  simp [emptyCrepHolLocalsW]

/-! ## Width-indexed crepProps counterparts

HOL `crepPropsScript.sml` `exp`/`prog` are word-length indexed (`'a word`), so
the generic-over-`α` helper theorems above need positive-width specializations.
Expression-only wrappers below retain exact tags because `CrepExp` contains no
String-backed identifiers. The later program-property counterparts are
untagged: `CrepProg` embeds `FunName = String` in its `Call` and `ExtCall`
constructors, whereas HOL uses `funname = mlstring`. A width-indexed word payload
does not repair that identifier-carrier mismatch. -/

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "map_var_cexp_eq_var"]
theorem map_var_crepExpVars_eqW {width : Nat} [NeZero width] (names : List Nat) :
    (names.map (CrepExp.var (α := BitVec width))).flatMap crepExpVarsW = names :=
  map_var_crepExpVars_eq names

/-! Exact expression-carrier corollary of HOL
    `crepProps$length_load_shape_eq_shape` (`crepPropsScript.sml:30`). -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "length_load_shape_eq_shape"]
theorem length_loadShapeHOLW {width : Nat} [NeZero width]
    (count : Nat) (address : BitVec width) (value : CrepExpHOL width) :
    (loadShapeBytesHOLW address count value).length = count := by
  induction count generalizing address <;> simp [loadShapeBytesHOLW, *]

theorem length_loadShape_eq_shapeW {width : Nat} [NeZero width]
    (count : Nat) (address : BitVec width) (value : CrepExp (BitVec width)) :
    (loadShapeBytesW address count value).length = count := by
  simpa [loadShapeBytesW] using length_loadShape_eq_shape count address value

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "length_load_globals_eq_read_size"]
theorem loadGlobals_lengthW {width : Nat} [NeZero width]
    (address : BitVec 5) (count : Nat) :
    (loadGlobalsW (width := width) address count).length = count :=
  loadGlobals_length address count

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "el_load_globals_elem"]
theorem loadGlobals_getElemW {width : Nat} [NeZero width]
    (address : BitVec 5) (count n : Nat) (h : n < count) :
    (loadGlobalsW (width := width) address count)[n]'(by
      simpa only [loadGlobals_lengthW] using h) =
        .loadGlob (address + BitVec.ofNat 5 n) :=
  loadGlobals_getElem address count n h

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "var_cexp_load_globals_empty"]
theorem loadGlobals_crepExpVars_emptyW {width : Nat} [NeZero width]
    (address : BitVec 5) (count : Nat) :
    (loadGlobalsW (width := width) address count).flatMap crepExpVarsW = [] :=
  loadGlobals_crepExpVars_empty address count

/-- Flapjack width-specialized analogue of Cake
    `crepProps$assigned_free_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:458-465`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.103`.
    HOL proves `!es ad. assigned_free_vars (nested_seq (store_globals ad es)) = []`;
    the Lean equation over `crepNestedSeqW`/`storeGlobalsW` matches it
    pointwise, since `storeGlobals` builds only `StoreGlob` programs, whose
    `assigned_free_vars` clause is empty (crepLangScript.sml:149-162). The
    mismatch is the imported programme carrier: HOL's `crepLang$prog` embeds
    `funname = mlstring` in `Call`/`ExtCall`, while Lean's `CrepProg` embeds
    `FunName = String`; because the quantifier ranges over a `CrepProg`, its
    function names can differ from HOL's and no `mlstring` identifier exists for
    `names_as_string`, nor a `NameRanged` byte witness. The `store_globals` list
    shape is pinned by `empty`/`one`/`two` rows of
    `scripts/hol-probes/crep_store_globals_probe.out` and sampled by
    `Flapjack/Test/CrepAssignedVarsParity.lean:84-86,108-111`. Restoring the tag
    depends on the exact mlstring-carrier port `flapjack-pxn.18.3.5.8.8`. -/
theorem crepAssignedFreeVars_nestedSeq_storeGlobalsW {width : Nat} [NeZero width]
    (address : BitVec 5) (values : List (CrepExp (BitVec width))) :
    crepAssignedFreeVarsW (crepNestedSeqW (storeGlobalsW address values)) = [] :=
  crepAssignedFreeVars_nestedSeq_storeGlobals address values

/-- Flapjack width-specialized analogue of Cake
    `crepProps$assigned_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:449-456`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.104`.
    HOL proves `!es ad. assigned_vars (nested_seq (store_globals ad es)) = []`;
    the Lean equation over `crepNestedSeqW`/`storeGlobalsW` matches it pointwise,
    since `storeGlobals` builds only `StoreGlob` programs, whose `assigned_vars`
    clause is empty. The mismatch is the imported programme carrier: HOL's
    `crepLang$prog` embeds `funname = mlstring` in `Call`/`ExtCall`, while Lean's
    `CrepProg` embeds `FunName = String`, so the quantified programmes need not
    agree and no `mlstring` identifier or `NameRanged` byte witness is available.
    The `store_globals` list shape is pinned by
    `scripts/hol-probes/crep_store_globals_probe.out` and sampled by
    `Flapjack/Test/CrepAssignedVarsParity.lean:88-90,111`. Restoring the tag
    depends on the exact mlstring-carrier port `flapjack-pxn.18.3.5.8.8`. -/
theorem crepAssignedVars_nestedSeq_storeGlobalsW {width : Nat} [NeZero width]
    (address : BitVec 5) (values : List (CrepExp (BitVec width))) :
    crepAssignedVarsW (crepNestedSeqW (storeGlobalsW address values)) = [] :=
  crepAssignedVars_nestedSeq_storeGlobals address values

/-- Flapjack width-specialized analogue of Cake
    `crepProps$assigned_free_vars_IMP_assigned_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml:373-378`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.102`.
    HOL proves `!prog x. MEM x (assigned_free_vars prog) ==> MEM x (assigned_vars prog)`;
    the Lean implication over `crepAssignedFreeVarsW`/`crepAssignedVarsW` matches
    it pointwise. The mismatch is the imported programme carrier: HOL's
    `crepLang$prog` embeds `funname = mlstring` in `Call`/`ExtCall`, while Lean's
    `CrepProg` embeds `FunName = String`, so the quantified `prog` ranges over a
    carrier whose function names can differ from HOL's. The quantifiers are a
    whole `CrepProg` and a `varname = num` name, so no `mlstring` identifier
    exists for `names_as_string`, and no `NameRanged` byte witness applies.
    Direct HOL rows `imp_mem=T` and `imp_mem_absent=T` are in
    `scripts/hol-probes/crep_assigned_vars_probe.out` (probe header cites
    crepPropsScript.sml:373) and sampled by
    `Flapjack/Test/CrepAssignedVarsParity.lean:50-62`. Restoring the tag depends
    on the exact mlstring-carrier port `flapjack-pxn.18.3.5.8.8`. -/
theorem mem_crepAssignedFreeVars_imp_mem_crepAssignedVarsW {width : Nat} [NeZero width]
    (program : CrepProg (BitVec width)) (name : Nat)
    (h : name ∈ crepAssignedFreeVarsW program) : name ∈ crepAssignedVarsW program :=
  mem_crepAssignedFreeVars_imp_mem_crepAssignedVars program name h

/-- Width-specialized analogue of Cake
    `crepProps$nested_seq_assigned_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:410-415`). It has the same
    list-length premise and assigned-variable equation, but stays untagged
    because it uses production `CrepProg (BitVec width)`: `Call`/`ExtCall`
    names are `String`, whereas HOL `prog` uses `mlstring`. The exact
    `CrepProgHOL` carrier exists, but `assigned_vars` and this theorem are not
    yet ported over it. Existing HOL oracle rows validate concrete results,
    not a carrier bridge. -/
theorem crepAssignedVars_nestedSeq_assign_zipWithW {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExp (BitVec width)))
    (h : names.length = values.length) :
    crepAssignedVarsW
        (crepNestedSeqW
          (names.zipWith (fun name value => CrepProg.assign name value) values)) =
      names :=
  crepAssignedVars_nestedSeq_assign_zipWith names values h

/-- Flapjack analogue of Cake `crepProps$nested_seq_assigned_free_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:420-427`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.107`.
    The equation `assigned_free_vars (nested_seq (MAP2 Assign ns vs)) = ns` under
    `LENGTH ns = LENGTH vs` matches the Lean `zipWith`/`crepNestedSeqW` form
    pointwise. The mismatch is the imported program carrier: HOL's
    `crepLang$prog` embeds `funname = mlstring` in its `Call`/`ExtCall`
    constructors, while Lean's `CrepProg` embeds `FunName = String`. Because the
    quantified carrier is a whole `CrepProg` its `Call`/`ExtCall` names can differ
    from HOL's, and the quantifiers here (`names : List Nat` are `varname = num`
    keys, the result is `List Nat`) expose no `mlstring` identifier that
    `names_as_string` could qualify. Direct HOL row `nested_afv=[1; 2]` is in
    `scripts/hol-probes/crep_assigned_vars_probe.out` (probe header cites
    crepPropsScript.sml:420), and the equation is sampled by
    `Flapjack/Test/CrepAssignedVarsParity.lean:103-107`. No exact
    mlstring-carrier programme exists yet; restoring the tag depends on
    `flapjack-pxn.18.3.5.8.8`. -/
theorem crepAssignedFreeVars_nestedSeq_assign_zipWithW {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExp (BitVec width)))
    (h : names.length = values.length) :
    crepAssignedFreeVarsW
        (crepNestedSeqW
          (names.zipWith (fun name value => CrepProg.assign name value) values)) =
      names :=
  crepAssignedFreeVars_nestedSeq_assign_zipWith names values h

/-- Exact port of Cake `crepProps$nested_seq_assigned_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:410-415`) over the exact
    `CrepProgHOL` carrier: `assigned_vars (nested_seq (MAP2 Assign ns vs)) = ns`
    when `LENGTH ns = LENGTH vs`. The claim is in `varname = num` keys only, so
    no `mlstring` identifier is inspected. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "nested_seq_assigned_vars_eq"]
theorem crepAssignedVarsHOL_nestedSeq_assign_zipWith {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width))
    (h : names.length = values.length) :
    crepAssignedVarsHOL
        (crepNestedSeqHOL
          (names.zipWith (fun name value => CrepProgHOL.assign name value) values)) =
      names := by
  revert values
  induction names with
  | nil =>
      intro values h
      cases values with
      | nil => simp [List.zipWith, crepNestedSeqHOL, crepAssignedVarsHOL]
      | cons value values => simp at h
  | cons name names ih =>
      intro values h
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [List.zipWith, crepNestedSeqHOL, crepAssignedVarsHOL, ih values h]

/-- Exact port of Cake `crepProps$nested_seq_assigned_free_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:420-427`) over the exact
    `CrepProgHOL` carrier: `assigned_free_vars (nested_seq (MAP2 Assign ns vs)) = ns`
    when `LENGTH ns = LENGTH vs`. The claim is in `varname = num` keys only, so
    no `mlstring` identifier is inspected. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "nested_seq_assigned_free_vars_eq"]
theorem crepAssignedFreeVarsHOL_nestedSeq_assign_zipWith {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width))
    (h : names.length = values.length) :
    crepAssignedFreeVarsHOL
        (crepNestedSeqHOL
          (names.zipWith (fun name value => CrepProgHOL.assign name value) values)) =
      names := by
  revert values
  induction names with
  | nil =>
      intro values h
      cases values with
      | nil => simp [List.zipWith, crepNestedSeqHOL, crepAssignedFreeVarsHOL]
      | cons value values => simp at h
  | cons name names ih =>
      intro values h
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [List.zipWith, crepNestedSeqHOL, crepAssignedFreeVarsHOL, ih values h]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_nested_decs_append"]
theorem crepAssignedVarsHOL_nestedDecs_append {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width)) (body : CrepProgHOL width)
    (h : names.length = values.length) :
    crepAssignedVarsHOL (nestedDecsHOL names values body) =
      names ++ crepAssignedVarsHOL body := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => simp [nestedDecsHOL]
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons] at h
          simp [nestedDecsHOL, crepAssignedVarsHOL, ih values (by omega)]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_nested_decs_append"]
theorem crepAssignedFreeVarsHOL_nestedDecs_append {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width)) (body : CrepProgHOL width)
    (h : names.length = values.length) :
    crepAssignedFreeVarsHOL (nestedDecsHOL names values body) =
      (crepAssignedFreeVarsHOL body).filter
        (fun candidate => decide (candidate ∉ names)) := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil =>
          simp only [nestedDecsHOL, List.not_mem_nil]
          symm
          exact List.filter_eq_self.mpr (fun _ _ => rfl)
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons] at h
          rw [nestedDecsHOL, crepAssignedFreeVarsHOL, ih values (by omega), List.filter_filter]
          congr 1
          funext candidate
          by_cases hc : candidate = name
          · subst hc
            simp
          · simp [hc, List.mem_cons, bne_iff_ne]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_seq_store_empty"]
theorem crepAssignedVarsHOL_nestedSeq_storesHOL {width : Nat} [NeZero width]
    (values : List (CrepExpHOL width)) (address : CrepExpHOL width) (offset : BitVec width) :
    crepAssignedVarsHOL (crepNestedSeqHOL (storesHOL address values offset)) = [] := by
  induction values generalizing offset with
  | nil => simp [storesHOL, crepNestedSeqHOL, crepAssignedVarsHOL]
  | cons value values ih =>
      simp [storesHOL, crepNestedSeqHOL, crepAssignedVarsHOL, ih]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_seq_store_empty"]
theorem crepAssignedFreeVarsHOL_nestedSeq_storesHOL {width : Nat} [NeZero width]
    (values : List (CrepExpHOL width)) (address : CrepExpHOL width) (offset : BitVec width) :
    crepAssignedFreeVarsHOL (crepNestedSeqHOL (storesHOL address values offset)) = [] := by
  induction values generalizing offset with
  | nil => simp [storesHOL, crepNestedSeqHOL, crepAssignedFreeVarsHOL]
  | cons value values ih =>
      simp [storesHOL, crepNestedSeqHOL, crepAssignedFreeVarsHOL, ih]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_store_globals_empty"]
theorem crepAssignedVarsHOL_nestedSeq_storeGlobalsHOL {width : Nat} [NeZero width]
    (values : List (CrepExpHOL width)) (address : BitVec 5) :
    crepAssignedVarsHOL (crepNestedSeqHOL (storeGlobalsHOL address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobalsHOL, crepNestedSeqHOL, crepAssignedVarsHOL]
  | cons value values ih =>
      simp [storeGlobalsHOL, crepNestedSeqHOL, crepAssignedVarsHOL, ih]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_store_globals_empty"]
theorem crepAssignedFreeVarsHOL_nestedSeq_storeGlobalsHOL {width : Nat} [NeZero width]
    (values : List (CrepExpHOL width)) (address : BitVec 5) :
    crepAssignedFreeVarsHOL (crepNestedSeqHOL (storeGlobalsHOL address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobalsHOL, crepNestedSeqHOL, crepAssignedFreeVarsHOL]
  | cons value values ih =>
      simp [storeGlobalsHOL, crepNestedSeqHOL, crepAssignedFreeVarsHOL, ih]

theorem crepAssignedVars_nestedDecs_appendW {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExp (BitVec width)))
    (body : CrepProg (BitVec width)) (h : names.length = values.length) :
    crepAssignedVarsW (nestedDecsW names values body) = names ++ crepAssignedVarsW body :=
  crepAssignedVars_nestedDecs_append names values body h

theorem crepAssignedFreeVars_nestedDecs_appendW {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExp (BitVec width)))
    (body : CrepProg (BitVec width)) (h : names.length = values.length) :
    crepAssignedFreeVarsW (nestedDecsW names values body) =
      (crepAssignedFreeVarsW body).filter (fun candidate => decide (candidate ∉ names)) :=
  crepAssignedFreeVars_nestedDecs_append names values body h

theorem crepAssignedVars_nestedSeq_storesW {width : Nat} [NeZero width]
    (address : CrepExp (BitVec width)) (values : List (CrepExp (BitVec width)))
    (offset : BitVec width) :
    crepAssignedVarsW (crepNestedSeqW (storesW address values offset)) = [] := by
  rw [storesW_eq_stores]
  exact crepAssignedVars_nestedSeq_stores address values offset (BitVec.ofNat width (width / 8))

theorem crepAssignedFreeVars_nestedSeq_storesW {width : Nat} [NeZero width]
    (address : CrepExp (BitVec width)) (values : List (CrepExp (BitVec width)))
    (offset : BitVec width) :
    crepAssignedFreeVarsW (crepNestedSeqW (storesW address values offset)) = [] := by
  rw [storesW_eq_stores]
  exact crepAssignedFreeVars_nestedSeq_stores address values offset (BitVec.ofNat width (width / 8))

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "var_exp_load_shape"]
theorem crepExpVars_of_mem_loadShapeW {width : Nat} [NeZero width]
    (count : Nat) (address : BitVec width) (value n : CrepExp (BitVec width))
    (h : n ∈ loadShapeBytes address count value) : crepExpVars n = crepExpVars value := by
  rw [← loadShape_eq_loadShapeBytes_of_stride_eq address CrepBytesInWord.bytesInWord count value
    rfl] at h
  exact crepExpVars_of_mem_loadShape address CrepBytesInWord.bytesInWord count value n h

end Flapjack
