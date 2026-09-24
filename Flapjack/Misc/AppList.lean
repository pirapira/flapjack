import Flapjack.HolRef

/-!
# HOL `misc$app_list` and `append`

Counterpart of the `app_list` datatype and `append_aux`/`append` helpers from
`cakeml/misc/miscScript.sml` (`append_aux_def`, `append_def`, `append_aux_thm`,
`append_thm`).  `misc$append` flattens an `app_list` (a small concatenation
tree) into a plain list and appears directly in the HOL
`stack_to_labProofScript.sml` `flatten_line_ok_pre` conclusion
`EVERY (line_ok_pre c) (append ls)`.

The datatype constructor names cannot be `List`/`Nil`/`Append` verbatim in the
`Flapjack` namespace (`List` is core), so they are named `AppList.list`,
`AppList.nil` and `AppList.append`.  The declaration tags carry the exact HOL
names.
-/

namespace Flapjack

/-- HOL `app_list = List ('a list) | Append app_list app_list | Nil`. -/
inductive AppList (α : Type) where
  /-- HOL `List ('a list)`. -/
  | list (values : List α) : AppList α
  /-- HOL `Append app_list app_list`. -/
  | append (left right : AppList α) : AppList α
  /-- HOL `Nil`. -/
  | nil : AppList α
  deriving Repr

/-- HOL `append_aux_def`. -/
@[hol "cakeml/misc/miscScript.sml" "append_aux_def"]
def appendAux {α : Type} : AppList α → List α → List α
  | .nil, aux => aux
  | .list values, aux => values ++ aux
  | .append left right, aux => appendAux left (appendAux right aux)

/-- HOL `append_def`: `append l = append_aux l []`. -/
@[hol "cakeml/misc/miscScript.sml" "append_def"]
def appListAppend {α : Type} (values : AppList α) : List α := appendAux values []

/-- HOL `append_aux_thm`: `!l xs. append_aux l xs = append_aux l [] ++ xs`. -/
@[hol "cakeml/misc/miscScript.sml" "append_aux_thm"]
theorem appendAux_thm {α : Type} (values : AppList α) (suffix : List α) :
    appendAux values suffix = appendAux values [] ++ suffix := by
  induction values generalizing suffix with
  | nil => rfl
  | list entries => simp [appendAux]
  | append left right ihLeft ihRight =>
      simp only [appendAux]
      rw [ihRight suffix, ihLeft (appendAux right [] ++ suffix), ihLeft (appendAux right []),
        List.append_assoc]

/-- HOL `append_thm`:
`append (Append l1 l2) = append l1 ++ append l2 /\ append (List xs) = xs /\
append Nil = []`. -/
@[hol "cakeml/misc/miscScript.sml" "append_thm"]
theorem appListAppend_thm {α : Type} (left right : AppList α) (entries : List α) :
    appListAppend (.append left right) = appListAppend left ++ appListAppend right ∧
      appListAppend (.list entries) = entries ∧
      appListAppend (.nil : AppList α) = [] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [appListAppend, appendAux, appendAux_thm]
    rfl
  · simp [appListAppend, appendAux]
  · rfl

/-- Flatten the leading `AppList` of a `(AppList α × Bool × Nat)` (the shape of
HOL `flatten`'s result) with `misc$append`. -/
def appListFlatten {α : Type} (result : AppList α × Bool × Nat) : List α × Bool × Nat :=
  (appListAppend result.1, result.2.1, result.2.2)

end Flapjack