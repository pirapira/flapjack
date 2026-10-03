import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.HolRef

namespace Flapjack.Misc.SptreeAlistInsertReverse
open Flapjack

/-- Flapjack inline native paired-list append identity. Equal prefix lengths
are necessary because original alist_insert truncates at the shorter list. -/
private theorem appendInsert {α : Type} (keys : List Nat) (values : List α)
    (moreKeys : List Nat) (moreValues : List α) (tree : Spt α)
    (lengths : keys.length=values.length) :
    LoopSemStateFiniteExact.sptAlistInsert (keys++moreKeys) (values++moreValues) tree =
    LoopSemStateFiniteExact.sptAlistInsert keys values
      (LoopSemStateFiniteExact.sptAlistInsert moreKeys moreValues tree) := by
  induction keys generalizing values with
  | nil =>
    cases values with
    | nil => rfl
    | cons value values => simp at lengths
  | cons key keys ih =>
    cases values with
    | nil => simp at lengths
    | cons value values =>
      have tailLength : keys.length=values.length := by simpa using lengths
      simp only [List.cons_append,LoopSemStateFiniteExact.sptAlistInsert,ih values tailLength]

/-- Flapjack inline pull-insert law from literal native insert_swap, valid on
all trees including malformed ones. The key is absent from the inserted list. -/
private theorem pullInsert {α : Type} (keys : List Nat) (values : List α)
    (key : Nat) (value : α) (tree : Spt α) (absent : key ∉ keys) :
    LoopSemStateFiniteExact.sptAlistInsert keys values (sptInsert key value tree) =
    sptInsert key value (LoopSemStateFiniteExact.sptAlistInsert keys values tree) := by
  induction keys generalizing values with
  | nil => rfl
  | cons head keys ih =>
    cases values with
    | nil => rfl
    | cons first values =>
      have fresh : key≠head ∧ key∉keys := by simpa using absent
      simp only [LoopSemStateFiniteExact.sptAlistInsert,ih values fresh.2]
      exact sptInsert_swap head key first value _ (Ne.symm fresh.1)

/-- Full original arbitrary native-tree reversal law4086–4096. The generic
payload, distinct-key and equal-length guards are retained; no well-formedness
hypothesis is added. Native insertion uses the reviewed constructor carrier. -/
@[hol "cakeml/misc/miscScript.sml" "alist_insert_REVERSE"]
theorem alistInsertReverse {α : Type} (keys : List Nat) (values : List α) (tree : Spt α)
    (distinct : keys.Nodup) (lengths : keys.length=values.length) :
    LoopSemStateFiniteExact.sptAlistInsert keys.reverse values.reverse tree =
    LoopSemStateFiniteExact.sptAlistInsert keys values tree := by
  induction keys generalizing values tree with
  | nil =>
    cases values with
    | nil => rfl
    | cons value values => simp at lengths
  | cons key keys ih =>
    cases values with
    | nil => simp at lengths
    | cons value values =>
      have parts : key∉keys ∧ keys.Nodup := by simpa using distinct
      have tailLength : keys.length=values.length := by simpa using lengths
      rw [List.reverse_cons,List.reverse_cons,
        appendInsert keys.reverse values.reverse [key] [value] tree (by simpa using tailLength)]
      simp only [LoopSemStateFiniteExact.sptAlistInsert]
      rw [ih values (sptInsert key value tree) parts.2 tailLength]
      exact pullInsert keys values key value tree parts.1

end Flapjack.Misc.SptreeAlistInsertReverse
